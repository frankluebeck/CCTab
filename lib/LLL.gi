

# arguments: [delta,][scalarfun]
BindGlobal("LLLRecord", function(args...)
  local res, f;
  res := rec();
  # the constant for Lovasz condition, default 3/4
  f := First([1..Length(args)], i-> IsRat(args[i]));
  if f <> fail then
    res.y := args[f];
    if res.y <= 1/4 or res.y > 1 then
      res.y := 3/4;
    fi;
  else
    res.y := 3/4;
  fi;
  # the function function(v1, v2) for computing the scalar product
  # of vectors v1 and v2, default is standard scalar product
  f := First([1..Length(args)], i-> IsFunction(args[i]));
  if f <> fail then
    res.scalar := args[f];
  else
    res.scalar := function(v1, v2) return v1*v2; end;
  fi;

  # setting up the (empty) data structures
  # input vectors (will be set to "false" when the record
  # is extended by new rows of the Gram matrix instead of vectors)
  res.vectors := [];
  # number of input vectors
  res.n := 0;
  # lower triangular part of Gram matrix
  res.gram := [];
  # mue coefficients, entries below diagonal
  res.mue := [];
  # number of vectors reduced to zero
  res.r := 0;
  # number of vectors processed so far
  res.kmax := 0;
  # the transition matrix to LLL-reduced basis
  # (first r rows yield zero vectors)
  res.H := [];
  # norms of Gram-Schmidt basis
  res.B := [];

  return res;
end);

# adding non-zero vectors and extending the Gram matrix
# (zero vectors are ignored, no reduction is done)
BindGlobal("AddVectorsLLLRecord", function(LR, vs)
  local vecs, gram, sc, kmax, ng, v;
  vecs := LR.vectors;
  gram := LR.gram;
  sc := LR.scalar;
  kmax := LR.kmax;
  for v in vs do
    if not IsZero(v) then
      if kmax > 0 then
        ng := LR.H * List([1..kmax], i-> sc(v, vecs[i]));
      else
        ng := [];
      fi;
      Append(ng, List([kmax+1..LR.n], i-> sc(v,vecs[i])));
      Add(ng, sc(v,v));
      Add(vecs, v);
      Add(gram, ng);
      LR.n := LR.n+1;
    fi;
  od;
end);

# adding rows of Gram matrix, in that case set LR.vectors to false
# (no reduction is done)
BindGlobal("AddGramLLLRecord", function(LR, gramrows)
  LR.vectors := false;
  Append(LR.gram, gramrows);
  LR.n := LR.n + Length(gramrows);
end);

# the main function implementing the LLL algorithm, essentially
# LLLReducedGramMat from GAP library which follows 
#    Cohen, A course in algebraic number theory
# 
# optional argument delta overwrites the default in LR
# 
# in this function we do not change input vectors, such that repeated
# calls to AddVectorsLLLRecord and ReduceLLLRecord are equivalent to
# adding all vectors in the beginning and reducing once
if IsBound(GAP_jl) then
# does nothing if kmax > 0 during a stepwise computation
UseJuliaForLLLReduce := function(lll)
  local gr, jgr, lt, tr, i, j;
  if lll.gram = [] or lll.kmax > 0  then
    return;
  fi;
  gr := List(lll.gram, ShallowCopy);
  for i in [1..Length(gr)] do
    for j in [i+1..Length(gr)] do
      gr[i][j] := gr[j][i];
    od;
  od;
  jgr := GAPToJulia(Julia.ZZMatrix, gr);
  lt := Julia.lll_gram_with_transform(jgr);
  gr := GAP_jl.Obj(lt[1]);
  for i in [1..Length(gr)] do
    gr[i] := gr[i]{[1..i]};
  od;
  lll.gram := gr;
  tr := GAP_jl.Obj(lt[2]);
  if lll.H = [] then
    lll.H := tr;
  else
    lll.H := tr * lll.H;
  fi;
end;
else
# do nothing
UseJuliaForLLLReduce := function(arg...)
end;
fi;

BindGlobal("ReduceLLLRecord", function(LR, delta...)
  local y, gram, mue, B, H, r, n, kmax, k, null, ak, a, b,
        RED, q, mmue, BB, row, i, j, l;

  # in case Julia is available and kmax = 0 we let
  # Julia/Nemo do most of the work
##  sometimes very slow, so disable ...  
  #UseJuliaForLLLReduce(LR);

  if Length(delta) > 0 then
    y := delta[1];
  else
    y := LR.y;
  fi;
  gram := LR.gram;
  mue := LR.mue;
  B := LR.B;
  H := LR.H;
  r := LR.r;
  n := LR.n;
  kmax := LR.kmax;
  # we start here since first kmax vectors are already reduced
  k := kmax+1; 
  if k > n then
    return;
  fi;
  # extend the H matrix
  null := 0*[k..n];
  for row in H do
    Append(row, null);
  od;
  null := 0*[1..n];
  for i in [k..n] do
    H[i] := ShallowCopy(null);
    H[i][i] := 1;
  od;

  # helper that is needed in several places below
  RED := function( gram, mue, H, n, k, l, r )
    local rat, a, b, q, i;
    if l = 0 then
      return;
    fi;

    # Terminate for $\|\mue_{k,l}\| \leq \frac{1}{2}$.
    if 1 < mue[k][l] * 2 or mue[k][l] * 2 < -1 then

      # Let $q = `Round( mue[k][l] )'$ (is never zero), \ldots
      #q:= Int( mue[k][l] );
      #if AbsoluteValue( mue[k][l] - q ) * 2 > 1 then
      #  q:= q + SignInt( mue[k][l] );
      #fi;
      rat := mue[k][l];
      a := NumeratorRat(rat);
      b := DenominatorRat(rat);
      if a >= 0 then
        q := QuoInt(2*a+b, 2*b);
      else
        q := QuoInt(2*a-b, 2*b);
      fi;
      # rat = rat-q
      rat := (a - b*q)/b;

      # \ldots adjust the Gram matrix (rows and columns, but only
      # in the lower triangular half), \ldots
      #gram[k][k]:= gram[k][k] - q * gram[k][l];
      #for i in [ r+1 .. l ] do
      #  gram[k][i]:= gram[k][i] - q * gram[l][i];
      #od;
      #for i in [ l+1 .. k ] do
      #  gram[k][i]:= gram[k][i] - q * gram[i][l];
      #od;
      #for i in [ k+1 .. n ] do
      #  gram[i][k]:= gram[i][k] - q * gram[i][l];
      #od;
      a := gram[k];
      if a[l] <> 0 then
        a[k] := a[k] - q*a[l];
      fi;
      b := gram[l];
      for i in [ r+1 .. l ] do
        if b[i] <> 0 then
          a[i] := a[i] - q*b[i];
        fi;
      od;
      for i in [ l+1 .. k ] do
        b := gram[i][l];
        if b <> 0 then
          a[i] := a[i] - q*b;
        fi;
      od;
      for i in [ k+1 .. n ] do
        a := gram[i];
        if a[l] <> 0 then
          a[k] := a[k] - q*a[l];
        fi;
      od;

      # \ldots adjust `mue', \ldots
      #mue[k][l]:= mue[k][l] - q;
      a := mue[k];
      b := mue[l];
      #mue[k][l]:= rat;
      a[l] := rat;
      for i in [ r+1 .. l-1 ] do
        #if mue[l][i] <> 0 then
        #  mue[k][i]:= mue[k][i] - q * mue[l][i];
        #fi;
        if b[i] <> 0 then
          a[i]:= a[i] - q * b[i];
        fi;
      od;

      # \ldots and the basechange.
      #H[k]:= H[k] - q * H[l];
      a := H[k];
      b := H[l];
      for i in [1..n] do
        if b[i] <> 0 then
          a[i] := a[i] - q*b[i];
        fi;
      od;
    fi;
  end;

  # buffer
  ak := [];

  # now the actual work
  while k <= n do

    # step 2 (Incremental Gram-Schmidt)

    # If $k \leq k_{max}$ go to step 3.
    if k > kmax then

      Info( InfoUTable, 5,
            "ReducedLLLRecord: Take ", Ordinal( k ), " vector" );

      # Otherwise \ldots
      kmax:= k;
      B[k]:= gram[k][k];
      mue[k]:= [];
      for j in [ r+1 .. k-1 ] do
        ak[j]:= gram[k][j];
        for i in [ r+1 .. j-1 ] do
          ak[j]:= ak[j] - mue[j][i] * ak[i];
        od;
        mue[k][j]:= ak[j] / B[j];
        B[k]:= B[k] - mue[k][j] * ak[j];
      od;

    fi;

    # step 3 (Test LLL condition)
    if k > 1 then
      RED( gram, mue, H, n, k, k-1, r );
      while B[k] < ( y - mue[k][k-1]^2 ) * B[k-1] do

        # Execute Sub-algorithm SWAPG$( k )$\:
        # Exchange $H_k$ and $H_{k-1}$,
        q      := H[k];
        H[k]   := H[k-1];
        H[k-1] := q;

        # adjust the Gram matrix (rows and columns,
        # but only in the lower triangular half),
        a := gram[k];
        b := gram[k-1];
        for j in [ r+1 .. k-2 ] do
          #q            := gram[k][j];
          #gram[k][j]   := gram[k-1][j];
          #gram[k-1][j] := q;
          q    := a[j];
          a[j] := b[j];
          b[j] := q;
        od;
        for j in [ k+1 .. n ] do
          #q            := gram[j][k];
          #gram[j][k]   := gram[j][k-1];
          #gram[j][k-1] := q;
          a := gram[j];
          q      := a[k];
          a[k]   := a[k-1];
          a[k-1] := q;
        od;
        a := gram[k];
        b := gram[k-1];
        #q              := gram[k-1][k-1];
        #gram[k-1][k-1] := gram[k][k];
        #gram[k][k]     := q;
        q      := b[k-1];
        b[k-1] := a[k];
        a[k]   := q;

        # and if $k > 2$, for all $j$ such that $1 \leq j \leq k-2$
        # exchange $\mue_{k,j}$ with $\mue_{k-1,j}$.
        a := mue[k];
        b := mue[k-1];
        for j in [ r+1 .. k-2 ] do
          #q           := mue[k][j];
          #mue[k][j]   := mue[k-1][j];
          #mue[k-1][j] := q;
          q    := a[j];
          a[j] := b[j];
          b[j] := q;
        od;

        # Then set $\mue \leftarrow \mue_{k,k-1}$
        mmue:= mue[k][k-1];

        # and $B \leftarrow B_k + \mue^2 B_{k-1}$.
        BB:= B[k] + mmue^2 * B[k-1];

        # Now, in the case $B = 0$ (i.e. $B_k = \mue = 0$),
        if BB = 0 then

          # exchange $B_k$ and $B_{k-1}$
          B[k]   := B[k-1];
          B[k-1] := 0;

          # and for $i = k+1, k+2, \ldots, k_{max}$
          # exchange $\mue_{i,k}$ and $\mue_{i,k-1}$.
          for i in [ k+1 .. kmax ] do
            a := mue[i];
            #q           := mue[i][k];
            #mue[i][k]   := mue[i][k-1];
            #mue[i][k-1] := q;
            q      := a[k];
            a[k]   := a[k-1];
            a[k-1] := q;
          od;

        # In the case $B_k = 0$ and $\mue \not= 0$,
        elif B[k] = 0 and mmue <> 0 then

          # set $B_{k-1} \leftarrow B$,
          B[k-1]:= BB;

          # $\mue_{k,k-1} \leftarrow \frac{1}{\mue}
          b := 1 / mmue;
          #mue[k][k-1]:= 1 / mmue;
          mue[k][k-1] := b;

          # and for $i = k+1, k+2, \ldots, k_{max}$
          # set $\mue_{i,k-1} \leftarrow \mue_{i,k-1} / \mue$.
          for i in [ k+1 .. kmax ] do
            a := mue[i];
            #mue[i][k-1]:= mue[i][k-1] / mmue;
            a[k-1] := a[k-1] * b;
          od;

        else

          # Finally, in the case $B_k \not= 0$,
          # set (in this order) $t \leftarrow B_{k-1} / B$,
          q:= B[k-1] / BB;

          # $\mue_{k,k-1} \leftarrow \mue t$,
          b := mmue * q;
          #mue[k][k-1]:= mmue * q;
          mue[k][k-1] := b;

          # $B_k \leftarrow B_k t$,
          B[k]:= B[k] * q;

          # $B_{k-1} \leftarrow B$,
          B[k-1]:= BB;

          # then for $i = k+1, k+2, \ldots, k_{max}$ set
          # (in this order) $t \leftarrow \mue_{i,k}$,
          # $\mue_{i,k} \leftarrow \mue_{i,k-1} - \mue t$,
          # $\mue_{i,k-1} \leftarrow t + \mue_{k,k-1} \mue_{i,k}$.
          for i in [ k+1 .. kmax ] do
            a := mue[i];
            #q:= mue[i][k];
            #mue[i][k]:= mue[i][k-1] - mmue * q;
            #mue[i][k-1]:= q + mue[k][k-1] * mue[i][k];
            q      := a[k];
            a[k]   := a[k-1] - mmue * q;
            a[k-1] := q + b * a[k];
          od;

        fi;

        # Terminate the subalgorithm.

        if k > 2 then k:= k-1; fi;

        # Here we have always `k > r' since the loop is entered
        # for `k > r+1' only (because of `B[k-1] <> 0'),
        # so the only problem might be the case `k = r+1',
        # namely `mue[ r+1 ][r]' is used then; but this is bound
        # provided that the initial Gram matrix did not start
        # with zero columns, and its (perhaps not updated) value
        # does not matter because this would mean just to subtract
        # a multiple of a zero vector.

        RED(  gram, mue, H, n, k, k-1, r );

      od;
    fi;

    if B[ r+1 ] = 0 then
      r:= r+1;
    fi;

    for l in [ k-2, k-3 .. r+1 ] do
      RED(  gram, mue, H, n, k, l, r );
    od;
    k:= k+1;

    # step 4 (Finished?)
    # If $k \leq n$ go to step 2 (beginning of this loop)

  od;
  # copy kmax and r into record
  LR.kmax := kmax;
  LR.r := r;
end);
  

# this function first calls ReduceLLLRecord (which does nothing if kmax is
# already n) and then changes the input vectors to the reduced basis and
# adjusts the other data accordingly
BindGlobal("CleanLLLRecord", function(LR)
  local n, r, tr, nvec, gram, ngram, mue, nmue, nB, nH;
  n := LR.n;
  if n > LR.kmax then
    ReduceLLLRecord(LR);
  fi;
  r := LR.r;
  tr := LR.H{[r+1..n]};
  if LR.vectors = false then
    nvec := false;
  elif Length(LR.vectors) = 0 then
    return;
  else
    nvec := tr * LR.vectors;
  fi;
  gram := LR.gram;
  ngram := List([r+1..n], i-> gram[i]{[r+1..i]});
  mue := LR.mue;
  nmue := List([r+1..n], i-> mue[i]{[r+1..i-1]});
  nB := LR.B{[r+1..n]};
  if n > r then
    nH := IdentityMat(n-r);
  else
    nH := [];
  fi;
  LR.vectors := nvec;
  LR.gram := ngram;
  LR.mue := nmue;
  LR.H := nH;
  LR.B := nB;
  LR.r := 0;
  LR.n := n-r;
  LR.kmax := n-r;
end);


# symmetric mod for integer a and positive integer b
SMod := function(a, b)
  local res;
  res := a mod b;
  if 2*res > b then
    return res-b;
  else
    return res;
  fi;
end;
SModList := function(l, b)
  if IsList(l) then
    return List(l, a-> SModList(a, b));
  fi;
  return SMod(l, b);
end;

# inplace integer division by d of entries l[m]..l[n]
QuoVector := function(l, d, m, n)
  local i;
  if m <= n and IsFloat(l[m]) then
    d := 1.0/Float(d);
    for i in [m..n] do
      l[i] := l[i]*d;
    od;
  else
    for i in [m..n] do
      l[i] := QuoInt(l[i], d);
    od;
  fi;
end;
SModVector := function(l, d, m, n)
  local i, b, x;
  b := QuoInt(d+1, 2);
  for i in [m..n] do
    x := l[i] mod d;
    if x > b then
      l[i] := x-d;
    else
      l[i] := x;
    fi;
  od;
end;

# bad performance
MatGaussPositiveDefinite := function(A)
  local n, i, j;
  A := List(A, ShallowCopy);
  n := Length(A);
  # complete symmetrically if lower triangular
  if Length(A[1]) < n then
    for i in [1..n] do
      for j in [i+1..n] do
        A[i,j] := A[j,i];
      od;
    od;
  fi;

  for i in [2..n] do
    for j in [1..i-1] do
      if A[i,j] <> 0 then
        AddRowVector(A[i], A[j], -A[i,j]/A[j,j], j, n);
      fi;
    od;
  od;
  return A;
end;

# see Geddes, Czapor, Labahn, Algorithms for Computer Algebra, (9.3)
FractionFreeIntegerGauss := function(A)
  local m, n, d, r, p, q, k, j, i;
  A := List(A, ShallowCopy);
  m := Length(A);
  n := Length(A[m]);
  # complete symmetrically if lower triangular
  if Length(A[1]) < n then
    for i in [1..m] do
      for j in [i+1..n] do
        A[i,j] := A[j,i];
      od;
    od;
  fi;
  d := 1; 
  r := 1;
  for k in [1..n] do
    if r <= m then
      p := r;
      while p <= m and A[p,k] = 0 do
        p := p+1;
      od;
      if p <= m then
        for j in [k..n] do
          q := A[p,j];
          A[p,j] := A[r,j];
          A[r,j] := q;
        od;
        for i in [r+1..m] do
          q := -A[i,k];
          MultVector(A[i], A[r,k]);
          AddRowVector(A[i], A[r], q, k+1, n);
          #MultVector(A[i], 1/d);
          QuoVector(A[i], d, k, n);
          #    for j in [k+1..n] do
          #      A[i,j] := (A[r,k]*A[i,j] - A[i,k]*A[r,j])/d;
          #    od;
          A[i,k] := 0;
        od;
        d := A[r,k];
        r := r+1;
      fi;
    fi;
  od;
  return A;
end;

# A square symmetric positive definite matrix, simplifies details
FractionFreeIntegerGaussPositiveDefinite := function(A)
  local n, d, q, k, j, i, z;
  A := List(A, ShallowCopy);
  n := Length(A);
  z := Zero(A[1,1]);
  # complete symmetrically if lower triangular
  if Length(A[1]) < n then
    for i in [1..n] do
      for j in [i+1..n] do
        A[i,j] := A[j,i];
      od;
    od;
  fi;
  d := 1; 
  for k in [1..n] do
      for i in [k+1..n] do
        q := -A[i,k];
        MultVector(A[i], A[k,k]);
        AddRowVector(A[i], A[k], q, k+1, n);
        QuoVector(A[i], d, k, n);
        A[i,k] := z;
      od;
      d := A[k,k];
  od;
  return A;
end;
# An alternative to the previous functions is the following where
# the result is computed columnwise, see Cohen p.88 (2).
# Performance is worse because the intermediate expressions are non
# integral rational numbers.
##  TMat := function(A)
##    local n, T, dd, x, k, j, i;
##    n := Length(A);
##    T := NullMat(n,n);
##    dd := [1];
##    for k in [1..n] do
##      for j in [1..k] do
##        x := dd[j]*A[k,j];
##        for i in [1..j-1] do
##          x := x - (dd[j]*T[i,j]*T[i,k])/(dd[i+1]*dd[i]);
##        od;
##        T[j,k] := x;
##      od;
##      Add(dd, x);
##    od;
##    return T;
##  end;


# A: square symmetric positive definite matrix
# computes a fraction free Gauss elimination, together with
# a permutation of the rows and and columns of the input matrix
# such that the diagonal entries of the result are minimal
# (the i-th diagonal entry is the deterinant of the upper
# left ixi submatrix, that is the i-th principal minor).
# This is the transpose of the mu-matrix in classical LLL,
# i-th row multiplied by principal i x i-minor d_i.
PermutedFractionFreeIntegerGaussPositiveDefinite := function(A)
  local n, z, perm, d, kk, q, a, piv, ai, i, j, k;
  A := List(A, ShallowCopy);
  n := Length(A);
  z := Zero(A[1,1]);
  # complete symmetrically if lower triangular
  if Length(A[1]) < n then
    for i in [1..n] do
      for j in [i+1..n] do
        A[i,j] := A[j,i];
      od;
    od;
  fi;
  perm := [1..n]+0;
  if IsBound(PFFIG) then
    PFFIG(A, perm, InfoLevel(InfoUTable));
  else
    d := 1; 
    for k in [1..n] do
      # permute such that smallest diagonal entry is in position k
      kk := k;
      for i in [k+1..n] do
        if A[i,i]<A[kk,kk] then
          kk := i;
        fi;
      od;
      if kk > k then
        q := perm[k];
        perm[k] := perm[kk];
        perm[kk] := q;
        q := A[k];
        A[k] := A[kk];
        A[kk] := q;
        for i in [1..n] do
          a := A[i];
          q := a[k];
          a[k] := a[kk];
          a[kk] := q;
        od;
      fi;
      #for i in [k+1..n] do
      #  q := -A[i,k];
      #  MultVector(A[i], A[k,k]);
      #  AddRowVector(A[i], A[k], q, k+1, n);
      #  QuoVector(A[i], d, k, n);
      #  A[i,k] := z;
      #od;
      a := A[k];
      piv := A[k,k];
      for i in [k+1..n] do
        ai := A[i];
        q := -ai[k];
        for j in [k+1..n] do
          ai[j] := QuoInt(piv*ai[j]+q*a[j], d);
        od;
        ai[k] := z;
      od;
      d := A[k,k];
    od;
  fi;
  return [A, PermList(perm)^-1];
end;

# integral and modular variant of LLL
# greedy strategy, swaping vectors for which the gain
# (reduction factor of product of d_i) is maximal
# length reductions are delayed to the end
# Reference: Arne Storjohann, Faster algorithms for integer lattice
# basis reduction, ETH Reports, 1996.
LLLTransformUnimodularGram := function(gr)
  local n, a, mat, v, max, x, M, T, H, 
        SubtractRow, SwitchRow, ModSubtractRow, ModSwitchRow, 
        dd, lovasz, oldd, k, d, i, j;
  n := Length(gr);
  # make copy and complete if lower triangular
  gr := List(gr, ShallowCopy);
  for i in [1..n] do
    a := gr[i];
    for j in [Length(a)..n] do
      gr[i,j] := gr[j,i];
    od;
  od;
  # want result H with H gr H^t = id  <=>  H^-t H = gr^-1
  # so entries of H are at most sqrt(max(diagonal(gr^-1)))
  mat := Z(251)^0*gr;
  ConvertToMatrixRep(mat, 251);
  mat := List(mat^-1, r-> List(r, Int));
  v := 0*gr[1];
  max := 0;
  for i in [1..n] do
    v[i] := 1;
    x := RationalSolutionIntMat(gr, v, 251, mat)[1][i];
    if x > max then
      max := x;
    fi;
    v[i] := 0;
  od;
  # M is power of two larger than 2 times largest entry of result H
  M := 2^(QuoInt(Log2Int(max), 2) + 2);
  Info(InfoUTable, 4, "LLL bound M in result: ",M);
  # during the computation we can alway reduce entries of H modulo M
  # and entries in i-th row of T modulo d_i M = T[i,i] M

  T := PermutedFractionFreeIntegerGaussPositiveDefinite(gr);
  H := Permuted(IdentityMat(n), T[2]);
  T := T[1];

  SubtractRow := function(H, T, k, r, q)
    local mq, i;
    if q <> 0 then
      mq := -q;
      AddRowVector(H[k], H[r], mq);
      for i in [1..r] do
        T[i,k] := T[i,k] + mq*T[i,r];
      od;
    fi;
  end;
  SwitchRow := function(H, T, k)
    local c, x, a, old, d, i;
    if k > 2 then
      c := T[k-2,k-2];
    else
      c := 1;
    fi;
    # exchange rows k-1, k
    x := H[k];
    H[k] := H[k-1];
    H[k-1] := x;
    # exchange rows and colums k-1, k
    x := T[k];
    T[k] := T[k-1];
    T[k-1] := x;
    for i in [1..k] do
      a := T[i];
      x := a[k];
      a[k] := a[k-1];
      a[k-1] := x;
    od;
    # adjust entries of rows k-1, k. When T is current T then
    #   new row k-1 is (T[k-2,k-2]*T[k-1] + T[k,k-1]*T[k])/T[k,k]
    #   new row k   is (-T[k,k-1]*T[k-1] + T[k-1,k-1]*T[k])/T[k,k]
    # (this seems wrong in article)
    old := ShallowCopy(T[k-1]);
    MultVector(T[k-1], c);
    c := T[k,k-1];
    d := T[k,k];
    AddRowVector(T[k-1], T[k], c, k-1, n);
    #MultVector(T[k-1], 1/d);
    QuoVector(T[k-1], d, k-1, n);
    MultVector(T[k], old[k-1]);
    AddRowVector(T[k], old, -c, k-1, n);
    #MultVector(T[k], 1/d);
    QuoVector(T[k], d, k-1, n);
  end;
  ModSubtractRow := function(H, T, M, k, r, q)
    local ddm, i;
    SubtractRow(H, T, k, r, q);
    for j in [1..n] do
      H[k,j] := SMod(H[k,j], M);
    od;
    for i in [1..k-1] do
      if i = 1 then
        ddm := T[i,i]*M;
      else
        ddm := T[i,i]*T[i-1,i-1]*M;
      fi;
      T[i,k] := SMod(T[i,k], ddm);
    od;
  end;
  ModSwitchRow := function(H, T, M, k)
    local ddm, i, j, Ti;
    SwitchRow(H, T, k);
##      for i in [1..k] do
##        if i = 1 then
##          ddm := T[i,i]*M;
##        else
##          ddm := T[i,i]*T[i-1,i-1]*M;
##        fi;
##        if i <= k-2 then
##          T[i,k-1] := SMod(T[i,k-1], ddm);
##        fi;
##        if i <= k-1 then
##          T[i,k] := SMod(T[i,k], ddm);
##        fi;
##        if i = k-1 then
##          for j in [k..n] do
##            T[k-1,j] := SMod(T[k-1,j], ddm);
##          od;
##        fi;
##        if i = k then
##          for j in [k+1..n] do
##            T[k,j] := SMod(T[k,j], ddm);
##          od;
##        fi;
##      od;
    for i in [1..k] do
      if i = 1 then
        ddm := T[i,i]*M;
      else
        ddm := T[i,i]*T[i-1,i-1]*M;
      fi;
      Ti := T[i];
      if i <= k-2 then
        Ti[k-1] := SMod(Ti[k-1], ddm);
      fi;
      if i <= k-1 then
        Ti[k] := SMod(Ti[k], ddm);
      fi;
      if i = k-1 then
        for j in [k..n] do
          Ti[j] := SMod(Ti[j], ddm);
        od;
      fi;
      if i = k then
        for j in [k+1..n] do
          Ti[j] := SMod(Ti[j], ddm);
        od;
      fi;
    od;
  end;
  
  # now the main loop
  # d_i is in dd[i+1], where d_0 = 1
  dd := [1, T[1,1]];
  lovasz := [];
  for i in [2..n] do
    Add(dd, T[i,i]);
    lovasz[i] := [dd[i+1]*dd[i-1] + SMod(T[i-1,i], dd[i])^2, dd[i]^2];
  od;
  while true do
    k := 2;
    for i in [3..n] do
      # find k such that reduction factor of d_i is maximal
      if lovasz[i,1]*lovasz[k,2] < lovasz[k,1]*lovasz[i,2] then
        k := i;
      fi;
    od;
    Info(InfoUTable, 4, "k=",k, " ");
    # Storjohann article: if 2*dd[k+1]*dd[k-1] >= dd[k]^2 then
    # more ambitious: if 4*dd[k+1]*dd[k-1] >= 3*dd[k]^2 then
    # Here we go on as long as there exists a k such
    # that the swap reduces d[k-1].
    if lovasz[k,1] >= lovasz[k,2] then
      break;
    fi;
    oldd := dd[k];
    x := 2*T[k-1,k];
    if x < 0 then
      x := x - dd[k];
    else
      x := x + dd[k];
    fi;
    x := QuoInt(x, 2*dd[k]);
    ModSubtractRow(H, T, M, k, k-1, x);
    ModSwitchRow(H, T, M, k);
    # adjust dd and lovasz (only dd[k] has changed)
    dd[k] := T[k-1,k-1];
    for i in [Maximum(2,k-1)..Minimum(n,k+1)] do
      lovasz[i] := [dd[i+1]*dd[i-1] + SMod(T[i-1,i], dd[i])^2, dd[i]^2];
    od;
    Info(InfoUTable, 4, "T[k-1,k-1] shrinked by ",Float(oldd/dd[k]));
  od;

  Info(InfoUTable, 4, "Final size reduction\n");
  # finally the size reductions, which were delayed so far
  for k in [2..n] do
    for j in [k-1,k-2..1] do
      x := 2*T[j,k];
      d := T[j,j];
      if x < 0 then
        x := x - d;
      else
        x := x + d;
      fi;
      x := QuoInt(x, 2*d);
      ModSubtractRow(H, T, M, k, j, x);
    od;
  od;

  return H;
end;


DoSubLLLGram := function(gr, ind)
  local lll, d, nd;
  #local lll, min, nmin;
  lll := LLLRecord();
  d := SortedList(List(ind, i-> gr[i,i]));
  #min := Minimum(List(ind, i-> gr[i,i]));
  AddGramLLLRecord(lll, gr{ind}{ind});
  ReduceLLLRecord(lll, 999/1000);
  nd := SortedList(List([1..Length(ind)], i-> lll.gram[i,i]));
  #nmin := Minimum(List([1..Length(ind)], i-> lll.gram[i,i]));
  Print(d,"\n",nd,"\n");
end;


LLLTransformUnimodularGramSectional := function(gr)
  local n, a, mat, v, max, x, M, T, H, L,
        SubtractRow, SwitchRow, ModSubtractRow, ModSwitchRow, MainLoop, 
        d, i, j, k;
  n := Length(gr);
  # make copy and complete if lower triangular
  gr := List(gr, ShallowCopy);
  for i in [1..n] do
    a := gr[i];
    for j in [Length(a)..n] do
      gr[i,j] := gr[j,i];
    od;
  od;
  # want result H with H gr H^t = id  <=>  H^-t H = gr^-1
  # so entries of H are at most sqrt(max(diagonal(gr^-1)))
  mat := Z(251)^0*gr;
  ConvertToMatrixRep(mat, 251);
  mat := List(mat^-1, r-> List(r, Int));
  v := 0*gr[1];
  max := 0;
  for i in [1..n] do
    v[i] := 1;
    x := RationalSolutionIntMat(gr, v, 251, mat)[1][i];
    if x > max then
      max := x;
    fi;
    v[i] := 0;
  od;
  # M is power of two larger than 2 times largest entry of result H
  M := 2^(QuoInt(Log2Int(max), 2) + 2);
  Info(InfoUTable, 4, "LLL bound M in result: ",M);
  # during the computation we can alway reduce entries of H modulo M
  # and entries in i-th row of T modulo d_{i-1} d_i M = T[i-1,i-1] T[i,i] M

  T := PermutedFractionFreeIntegerGaussPositiveDefinite(gr);
  H := Permuted(IdentityMat(n), T[2]);
  T := T[1];

  # in the following functions L can be 0 (then it is ignored)
  # or a square matrix of size Length(T) (then the row operations
  # on T are applied to L as well
  SubtractRow := function(H, T, k, r, q, L)
    local mq, i;
    if q <> 0 then
      mq := -q;
      AddRowVector(H[k], H[r], mq);
      if L <> 0 then
        AddRowVector(L[k], L[r], mq);
      fi;
      for i in [1..r] do
        T[i,k] := T[i,k] + mq*T[i,r];
      od;
    fi;
  end;
  SwitchRow := function(H, T, k, L)
    local c, x, a, old, d, e, f, i;
    if k > 2 then
      c := T[k-2,k-2];
    else
      c := 1;
    fi;
    # exchange rows k-1, k
    x := H[k];
    H[k] := H[k-1];
    H[k-1] := x;
    # exchange rows and colums k-1, k
    x := T[k];
    T[k] := T[k-1];
    T[k-1] := x;
    for i in [1..k] do
      a := T[i];
      x := a[k];
      a[k] := a[k-1];
      a[k-1] := x;
    od;
    if L <> 0 then
      x := L[k];
      L[k] := L[k-1];
      L[k-1] := x;
    fi;

    # adjust entries of rows k-1, k. When T is current T then
    #   new row k-1 is (T[k-2,k-2]*T[k-1] + T[k,k-1]*T[k])/T[k,k]
    #   new row k   is (-T[k,k-1]*T[k-1] + T[k-1,k-1]*T[k])/T[k,k]
    old := ShallowCopy(T[k-1]);
    f := T[k,k-1];
    d := T[k,k];
    e := old[k-1];
    MultVector(T[k-1], c);
    AddRowVector(T[k-1], T[k], f, k-1, n);
    QuoVector(T[k-1], d, k-1, n);
    MultVector(T[k], e);
    AddRowVector(T[k], old, -f, k-1, n);
    QuoVector(T[k], d, k, n);
    if L <> 0 then
      old := ShallowCopy(L[k-1]);
      MultVector(L[k-1], c);
      AddRowVector(L[k-1], L[k], f, k-1, n);
      QuoVector(L[k-1], d, k-1, n);
      MultVector(L[k], e);
      AddRowVector(L[k], old, -f, k-1, n);
      QuoVector(L[k], d, k-1, n);
    fi;
  end;
  ModSubtractRow := function(H, T, M, k, r, q, L)
    local ddm, i;
    SubtractRow(H, T, k, r, q, L);
    SModVector(H[k], M, 1, n);
    for i in [1..k-1] do
      if i = 1 then
        ddm := T[i,i]*M;
      else
        ddm := T[i,i]*T[i-1,i-1]*M;
      fi;
      T[i,k] := SMod(T[i,k], ddm);
    od;
  end;
  ModSwitchRow := function(H, T, M, k, L)
    local ddm, i, j;
    SwitchRow(H, T, k, L);
    for i in [1..k] do
      if i = 1 then
        ddm := T[i,i]*M;
      else
        ddm := T[i,i]*T[i-1,i-1]*M;
      fi;
      if i <= k-2 then
        T[i,k-1] := SMod(T[i,k-1], ddm);
      fi;
      if i <= k-1 then
        T[i,k] := SMod(T[i,k], ddm);
      fi;
      if i = k-1 then
        SModVector(T[k-1], ddm, k, n);
      fi;
      if i = k then
        SModVector(T[k], ddm, k+1, n);
      fi;
    od;
  end;
 
  # now the main loop, packed in function such that we can also use
  # it for sectional LLLs
  MainLoop := function(H, T, M, L)
    local dd, k, x, y, i;
    dd := [1];
    for i in [1..n] do
      Add(dd, T[i,i]);
    od;
    while true do
      k := 2;
      x := [dd[k+1]*dd[k-1] + SMod(T[k-1,k], dd[k])^2, dd[k]^2];
      for i in [3..n] do
        y := [dd[i+1]*dd[i-1] + SMod(T[i-1,i], dd[i])^2, dd[i]^2];
        if y[1]*x[2] < x[1]*y[2] then
          k := i;
          x := y;
        fi;
      od;
      #if 2*dd[k+1]*dd[k-1] >= dd[k]^2 then
      if x[1] >= x[2] then
        # no further improvement possible
        break;
      fi;
      Info(InfoUTable, 4, "k=",k, " shrink factor ", Float(x[2]/x[1]));
      x := 2*T[k-1,k];
      if x < 0 then
        x := x - dd[k];
      else
        x := x + dd[k];
      fi;
      x := QuoInt(x, 2*dd[k]);
      ModSubtractRow(H, T, M, k, k-1, x, L);
      ModSwitchRow(H, T, M, k, L);
      for i in [1..n] do
        dd[i+1] := T[i,i];
      od;
    od;
  end;

##  oldT:=List(T,ShallowCopy);
##  H:=IdentityMat(n);
##    L := IdentityMat(n);
  MainLoop(H, T, M, 0);
##  Print("CHECKL: ", T = L*oldT*TransposedMat(H),"\n");

  Info(InfoUTable, 4, "Final size reduction\n");
  # finally the size reductions
  for k in [2..n] do
    for j in [k-1,k-2..1] do
      x := 2*T[j,k];
      d := T[j,j];
      if x < 0 then
        x := x - d;
      else
        x := x + d;
      fi;
      x := QuoInt(x, 2*d);
      ModSubtractRow(H, T, M, k, j, x, 0);
    od;
  od;
  # reduce entries to range [-M/2..M/2]
  x := M/2;
  for i in [1..n] do
    for j in [1..n] do
      if H[i,j] > x then
        H[i,j] := H[i,j] - M;
      fi;
    od;
  od;

##    return [H, L];
  return H;
end;


_tmpLLLH := fail;
LLLTransformGramFPyLLL := function(gr)
  local py3, str, inp, out, res;
  py3 := PathSystemProgram("python3");
  str := "gr = ";
  Append(str, String(gr));
  Append(str, "\n");
  # fpylll.config.float_types d dpe mpfr (mit precision=...)
  Append(str, """
from fpylll import *

G = IntegerMatrix.from_matrix(gr)
M = GSO.Mat(G, U = IntegerMatrix.identity(len(gr)), gram = True, float_type='mpfr', flags=1)
L = LLL.Reduction(M)
L()
H = [[0 for _ in gr] for _ in gr]
M.U.to_matrix(H)
print("_tmpLLLH := ", H, ";\n")
""");
  inp := InputTextString(str);
  res := "";
  out := OutputTextString(res, false);

  Process(DirectoryCurrent(), py3, inp, out, []);
  CloseStream(inp);
  CloseStream(out);
  inp := InputTextString(res);
  Read(inp);
  CloseStream(inp);
  res := _tmpLLLH;
  Unbind(_tmpLLLH);
  return res;
end;


