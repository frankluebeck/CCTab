
# utilities:utilities:  symmetric mod for integer a and positive integer b
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

# Configure number of threads for various standalone programs below which 
# use the FLINT library and several threads.
NRFlintThreads := 8;

# Print integer matrix in format read by the FLINT function
# read_fmpz_mat()
PrintIntegerMatToFlint := function(fname, mat)
  local fu;
  fu := function()
    local r, x;
    Print( Length( mat ), " ", Length( mat[1] ), "  \c" );
    for r in mat do
      for x in r do
        Print( x, " \c" );
      od;
    od;
    Print( "\n\n" );
  end;
  PrintTo1(fname, fu);
end;

# A: square symmetric positive definite matrix
# computes a fraction free Gauss elimination, together with
# a permutation of the rows and and columns of the input matrix
# such that the diagonal entries of the result are minimal
# (the i-th diagonal entry is the deterinant of the upper
# left ixi submatrix, that is the i-th principal minor).
# This is the transpose of the mu-matrix in classical LLL,
# i-th row multiplied by principal i x i-minor d_i.
PermutedFractionFreeIntegerGaussPositiveDefinite_GAP := function(A)
  local n, z, perm, d, kk, q, a, piv, ai, i, j, k, res;
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
  if IsBound(PFFIGx) then
    PFFIG(A, perm, InfoLevel(InfoCCTable));
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

# multithreaded standalone version of the previous function 
TMPRES774684629486 := fail;
PFFIGThreaded := function(gr)
  local prg, str, inp, res, out;
  prg := Filename(DirectoriesPackagePrograms("CCTab"), "pffgintmat_threads");
  if prg = fail then
    return fail;
  fi;
  str := "";
  out := OutputTextString(str, false);
  PrintIntegerMatToFlint(out, gr);
  CloseStream(out);
  inp := InputTextString(str);
  res := "";
  out := OutputTextString(res, false);
  Process(DirectoryCurrent(), prg, inp, out, [String(Length(gr)), String(NRFlintThreads)]);
  CloseStream(inp);
  CloseStream(out);
  inp := InputTextString(res);
  Read(inp);
  CloseStream(inp);
  res := [TMPRES774684629486.A, PermList(TMPRES774684629486.perm)^-1];
  Unbind(TMPRES774684629486);
  return res;
end;
if Filename(DirectoriesPackagePrograms("CCTab"), "pffgintmat_threads") <>
                                      fail then
  PermutedFractionFreeIntegerGaussPositiveDefinite := PFFIGThreaded;
else
  PermutedFractionFreeIntegerGaussPositiveDefinite := 
            PermutedFractionFreeIntegerGaussPositiveDefinite_GAP;
fi;


# a simplified version of InverseRatMat
InverseUnimodularMat_GAP := function(m)
  local p, mi, n, null, res, v, pi, r, x, i;
  p := 251;
  mi := Z(p)^0*m;
  ConvertToMatrixRep(mi,p);
  mi := List(mi^-1,r->List(r, Int));
  n := Length(m);
  null := 0*[1..n];
  res := [];
  for i in [1..n] do
    v := ShallowCopy(null); 
    v[i] := 1;
    pi := 1;
    r := ShallowCopy(null);
    while not IsZero(v) do
      x := SModList(v*mi, p);
      AddRowVector(r, x, pi);
      pi := pi*p; 
      v := (v-x*m)/p;
    od;
    Add(res, r);
  od;
  return res;
end;
# standalone version of function above using FLINT and multiple threads
TMPRES897966487097 := fail;
InvUniThreaded := function(mat)
  local prg, str, inp, res, out;
  prg := Filename(DirectoriesPackagePrograms("CCTab"), "invuni_threads");
  if prg = fail then
    return fail;
  fi;
  str := "";
  out := OutputTextString(str, false);
  PrintIntegerMatToFlint(out, mat);
  CloseStream(out);
  inp := InputTextString(str);
  res := "";
  out := OutputTextString(res, false);
  Process(DirectoryCurrent(), prg, inp, out, [String(NRFlintThreads), 
          String(Length(mat)), "4294967291" ]);
  CloseStream(inp);
  CloseStream(out);
  inp := InputTextString(res);
  Read(inp);
  CloseStream(inp);
  res := TMPRES897966487097.invmat;
  Unbind(TMPRES897966487097);
  return res;
end;
if Filename(DirectoriesPackagePrograms("CCTab"), "invuni_threads") <> fail then
  InverseUnimodularMat := InvUniThreaded;
else
  InverseUnimodularMat := InverseUnimodularMat_GAP;
fi;


# This is a variant of the algorithm described in this reference:
# Arne Storjohann, Faster algorithms for integer lattice
# basis reduction, ETH Reports, 1996.
# 
# integral and modular variant of LLL
# greedy strategy, swaping vectors for which the gain
# (reduction factor of product of d_i) is maximal
# length reductions are delayed to the end
# 
# the main loop is organized such that one could do many non-overlapping
# swaps in parallel; this is implemented in the standalone program for
# this algorithm
# 
LLLTransformUnimodularGram_GAP := function(gr)
  local n, a, max, M, T, HH, ModSubtractRow, ModSwitchRow, 
        dd, ddM, lovasz, k, klist, qlist, x, d, mat, v, H, i, j;
  n := Length(gr);
  # make copy and complete if lower triangular
  gr := List(gr, ShallowCopy);
  for i in [1..n] do
    a := gr[i];
    for j in [Length(a)..n] do
      gr[i,j] := gr[j,i];
    od;
  od;
  # want result H with H gr H^t = id  <=>  H^-1 H^-t = gr
  # so entries of H^-1 are at most sqrt(max(diagonal(gr)))
  max := gr[1,1];
  for i in [2..n] do
    if gr[i,i] > max then
      max := gr[i,i];
    fi;
  od;
  # M is power of two larger than 2 times largest entry of result H^-1
  M := 2^(QuoInt(Log2Int(max), 2) + 2);
  Info(InfoCCTable, 4, "LLL bound M in result: ",M);
  # during the computation we can always reduce entries of H^-1 modulo M
  # and entries in i-th row of T modulo d_{i-1} d_i M = T[i-1,i-1] T[i,i] M

  T := PermutedFractionFreeIntegerGaussPositiveDefinite(gr);
  # we compute HH = H^-t for which we have a bound for the entries
  HH := Permuted(IdentityMat(n), T[2]);
  T := T[1];
  
  # from now we don't need gr any more and work with T

  ModSubtractRow := function(HH, T, M, k, r, q, swapped)
    local a, b, j, i;
    if q <> 0 then
      a := HH[r];
      b := HH[k];
      for j in [1..n] do
        a[j] := SMod(a[j] + q*b[j], M);
      od;
      if swapped then
        for i in [1..r] do
          T[i,r] := SMod(T[i,r] - q*T[i,k], ddM[i]);
        od;
      else
        for i in [1..r] do
          T[i,k] := SMod(T[i,k] - q*T[i,r], ddM[i]);
        od;
      fi;
    fi;
  end;
  # here we assume that columns k-1 and k of T are already swapped
  # and that ddM is already adjusted
  ModSwitchRow := function(HH, T, M, k)
    local x, a, b, y, z, d, s, t, j;
    # exchange rows k-1, k
    x := HH[k];
    HH[k] := HH[k-1];
    HH[k-1] := x;

    # note the columns k-1 and k are already swapped
    # adjust entries of rows k-1, k. When T is current T then
    #   new row k-1 is (T[k-2,k-2]*T[k] + T[k-1,k-1]*T[k-1])/T[k-1,k]
    #   new row k   is (-T[k-1,k-1]*T[k] + T[k,k-1]*T[k-1])/T[k-1,k]
    # (this seems wrong in article)
    a := T[k-1];
    b := T[k];
    x := dd[k-1];
    y := b[k-1];
    z := a[k-1];
    d := a[k];
    for j in [k-1..n] do
      s := x*b[j] + z*a[j];
      s := SMod(QuoInt(s,d), ddM[k-1]);
      t := -z*b[j] + y*a[j];
      t := SMod(QuoInt(t,d), ddM[k]);
      a[j] := s;
      b[j] := t;
      if j = k-1 then
        # adjust dd, ddM
        dd[k] := s;
        ddM[k-1] := dd[k-1]*dd[k]*M;
        ddM[k] := dd[k]*dd[k+1]*M;
      fi;
    od;
  end;

  # now the main loop
  # d_i is in dd[i+1], where d_0 = 1
  dd := [1, T[1,1]];
  ddM := [dd[2]*M];
  lovasz := [];
  for i in [2..n] do
    Add(dd, T[i,i]);
    Add(ddM, dd[i]*dd[i+1]*M);
    lovasz[i] := [dd[i+1]*dd[i-1] + SMod(T[i-1,i], dd[i])^2, dd[i]^2];
  od;
  while true do
    # find list of k with distance at least 3 such that
    # swap of k an k-1 yields improvement
    k := n;
    klist := [];
    while k > 1 do
      if lovasz[k,1] < lovasz[k,2] then
        Add(klist, k);
        k := k-3;
      else
        k := k-1;
      fi;
    od;
    if Length(klist) = 0 then
      break;
    fi;
    qlist := [];
    for k in klist do
      x := 2*T[k-1,k];
      if x < 0 then
        x := x - dd[k];
      else
        x := x + dd[k];
      fi;
      Add(qlist, QuoInt(x, 2*dd[k]));
    od;

    # swap columns k-1 and k of T for all k
    for i in [1..n] do
      a := T[i];
      for k in klist do
        if k >= i then
          x := a[k];
          a[k] := a[k-1];
          a[k-1] := x;
        fi;
      od;
    od;
    # this loop could be done in parallel
    for i in [1..Length(klist)] do
      k := klist[i];
      x := qlist[i];
      # last argument means that we swapped the columns above
      ModSubtractRow(HH, T, M, k, k-1, x, true);
      ModSwitchRow(HH, T, M, k);
      # adjust lovasz
      for j in [Maximum(2,k-1)..Minimum(n,k+1)] do
        lovasz[j] := [dd[j+1]*dd[j-1] + SMod(T[j-1,j], dd[j])^2, dd[j]^2];
      od;
    od;
  od;

  Info(InfoCCTable, 4, "Final size reduction\n");
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
      ModSubtractRow(HH, T, M, k, j, x, false);
    od;
  od;

  # return inverse transpose of HH
  HH := TransposedMat(HH);
  mat := Z(251)^0*HH;
  ConvertToMatrixRep(mat, 251);
  mat := List(mat^-1, r-> List(r, Int));
  v := 0*[1..n];
  H := [];
  for i in [1..n] do
    v[i] := 1;
    Add(H, RationalSolutionIntMat(HH, v, 251, mat)[1]);
    v[i] := 0;
  od;
  return H;
end;

# a multithreaded variant of the previous GAP function
NRFlintThreads := 8;
TMPRES03695464 := fail;
LLLTUGIT := function(gr)
  local n, prg, str, out, inp, res, HH, mat, v, H, i;
  n := Length(gr);
  prg := Filename(DirectoriesPackagePrograms("CCTab"), "lll_modular_threads");
  if prg = fail then
    return fail;
  fi;
  str := "";
  out := OutputTextString(str, false);
  PrintIntegerMatToFlint(out, gr);
  CloseStream(out);
  inp := InputTextString(str);
  res := "";
  out := OutputTextString(res, false);
  Process(DirectoryCurrent(), prg, inp, out, [String(Length(gr)), String(NRFlintThreads)]);
  CloseStream(inp);
  CloseStream(out);
  inp := InputTextString(res);
  Read(inp);
  CloseStream(inp);
  H := TMPRES03695464.H;
  Unbind(TMPRES03695464);
  return H;
end;

if Filename(DirectoriesPackagePrograms("CCTab"), "lll_modular_threads") <>
                                              fail then
  LLLTransformUnimodularGram := LLLTUGIT;
else
  LLLTransformUnimodularGram := LLLTransformUnimodularGram_GAP;
fi;
