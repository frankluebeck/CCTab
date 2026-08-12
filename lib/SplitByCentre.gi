###########################################################################
##  SplitByCentre.gi
##  
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  Orthogonal decomposition of the lattice of generalized characters
##  according to the characters of (a subgroup of) the center.
##  

##  <#GAPDoc Label="SplitByCentre">
##  <ManSection>
##  <Oper Name="SplitByCentre" Arg="CCT"/>
##  <Meth Name="SplitByCentre" Label="withZ" Arg="CCT, zind"/>
##  <Filt Name="HasSplittingCentre" Arg="CCT"/>
##  <Attr Name="SplittingCentre" Arg="CCT"/>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object of a group
##  <M>G</M>. In the second form, <A>zind</A> must be a list of numbers of
##  conjugacy classes of <A>G</A> forming a subgroup <M>Z</M> of the
##  center of <M>G</M> (with the class of the
##  identity first). In the first form, <A>zind</A> is computed as the set
##  of classes of length <M>1</M>, that is the full centre of <M>G</M>.
##  <P/>
##  Each irreducible character of <A>G</A> restricted to <M>Z</M> is 
##  a multiple of an irreducible character of <M>Z</M> (Schur's Lemma).
##  We get an orthogonal decomposition of the lattice of generalized
##  characters into sublattices spanned by irreducible characters whose 
##  restrictions to <M>Z</M> are multiples of the same irreducible
##  character. <Ref Oper="SplitByCentre"/>  computes a data structure 
##  which allows to
##  split any generalized character according to this decomposition.
##  We only need to store class functions for one character of <M>Z</M>
##  per Galois orbit (the others can be computed by 
##  <Ref BookName="Reference" Oper="GaloisCyc"/>).
##  <P/>
##  This splitting is applied to all generalized characters already
##  stored in <A>CCT</A> and to all generalized characters which are
##  imported afterwards.
##  <P/>
##  After a successful call with non-trivial <M>Z</M> 
##  the filter <Ref Filt="HasSplittingCentre"/>
##  is set in <A>CCT</A> and the attribute
##  <Ref Attr="SplittingCentre"/> of <A>CCT</A> is set to <A>zind</A>.
##  <Example>
##  gap> G := SL(4,5);;
##  gap> CCT := CCTable(G);;
##  gap> SplitByCentre(CCT);
##  gap> HasSplittingCentre(CCT);
##  true
##  gap> SplittingCentre(CCT);
##  [ 1, 10, 19, 28 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>

# do nothing if splitting centre is already installed
InstallMethod(SplitByCentre, ["IsCCTable and HasSplittingCentre"],
function(CCT) end);
# find classes in centre and call method below
InstallMethod(SplitByCentre, ["IsCCTable"], function(CCT)
  local scls;
  scls := SizesConjugacyClasses(CCT);
  SplitByCentre(CCT, Positions(scls, 1));
end);
# now the real function
# argument zind must be list of positions of classes which form
# a subgroup of the centre (trivial class must be first)
InstallMethod(SplitByCentre, ["IsCCTable and HasUnderlyingGroup", "IsList"], 
function(CCT, zind)
  local G, cls, ncl, z, zmaps, done, x, a, sz, zg, tz, zchars, det, inv, 
        e, pr, found, reps, zgalois, k, jj, zchmults, known, i, j;
  # refuse to do anything for trivial case
  if Length(zind) = 1 then
    return;
  fi;

  # to compute splitting we need the map on classes by multiplication with
  # centre elements
  G := UnderlyingGroup(CCT);
  cls := ConjugacyClasses(CCT);
  ncl := NrConjugacyClasses(CCT);
  z := List(zind, i-> Representative(cls[i]));
  zmaps := [zind];
  done := BlistList([1..ncl], zind);
  for i in [1..ncl] do
    if not done[i] then
      x := Representative(cls[i]);
      a := [i];
      for j in [2..Length(z)] do
        Add(a, PositionConjugacyClass(G, x*z[j]));
      od;
      for k in a do
        done[k] := true;
      od;
      Add(zmaps, a);
    fi;
  od;
  CCT!.zmaps := zmaps;

  # the character table of the splitting group which parameterizes the
  # splitting
  sz := Length(z);
  zg := Group(z);
  SetConjugacyClasses(zg, List(z, x-> ConjugacyClass(zg, x)));
  tz :=CharacterTable(zg);
  zchars := List(Irr(tz), AsList);
  CCT!.zchars := zchars;
  det := DeterminantMat(zchars);
  inv := det*zchars^-1;
  CCT!.invzchars := [det, inv];

  # during computations we only need one character of z per Galois orbit
  e := Exponent(zg);
  pr := PrimeResidues(e);
  found := BlistList([1..sz], []);
  reps := [];
  zgalois := [];
  for i in [1..sz] do
    if not found[i] then
      found[i] := true;
      Add(reps, i);
      for j in pr do
        k := Position(zchars, GaloisCyc(zchars[i], j));
        if not found[k] then
          found[k] := true;
          # want exponent prime to |G|
          jj := j;
          while Gcd(Size(G), jj) <> 1 do
            jj := jj + e;
          od;
          # record Galois map from part i to k and its inverse
          zgalois[k] := [i,jj,1/jj mod Size(G)];
        fi;
      od;
    fi;
  od;
  CCT!.zchreps := reps;
  CCT!.zgalois := zgalois;
  # for counting purposes
  zchmults := [];
  for i in reps do
    zchmults[i] := 1 + Number(Set(zgalois), a-> a[1]=i);
  od;
  CCT!.zchmults := zchmults;

  SetSplittingCentre(CCT, zind);

  # we remove already known characters from CCT!.hnfs and add them
  # back as new characters (such that they are split).
  known := Concatenation(CCT!.hnfs[1].hnf, CCT!.hnfs[1].new);
  CCT!.hnfs := [];
  for i in reps do
    CCT!.hnfs[i] := rec(new := [], hnf := [], pivots := [], index := 0);
  od;
  ImportToCCTable(CCT, known);
end);

##  <#GAPDoc Label="SplitCharacterByCentre">
##  <ManSection>
##  <Oper Name="SplitCharacterByCentre" Arg="CCT, ch"/>
##  <Oper Name="SplitEncodedCharacterByCentre" Arg="CCT, ech"/>
##  <Returns>a list of (encoded) characters</Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object with
##  <C>HasSplittingCentre(CCT) = </C><K>true</K>.
##  In the first form let
##  <A>ch</A> be a generalized character of the underlying group, given
##  by a list of values on <E>all</E> conjugacy classes (not encoded as by
##  <Ref Func="EncodeForCCTable"/>). In the second form <A>ech</A> is a
##  character endoded for <A>CCT</A>. This function decomposes the character
##  according to the splitting centre (see <Ref Oper="SplitByCentre"/>).
##  <Example>
##  gap> G := SmallGroup(96, 14);;
##  gap> CCT := CCTable(G);;
##  gap> SplitByCentre(CCT);
##  gap> U := TrivialSubgroup(G);;
##  gap> reg := InducedClassFunction(TrivialCharacter(U), G);;
##  gap> SplitCharacterByCentre(CCT, reg);
##  [ [ 24, 0, 0, 24, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0,
##        0, 0, 0, 0 ],
##    [ 24, 0, 0, -24, 0, 24, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0, 0, 0, 0, 0,
##        0, 0, 0, 0 ],
##    [ 24, 0, 0, 24, 0, -24, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0, 0, 0, 0, 0,
##        0, 0, 0, 0 ],
##    [ 24, 0, 0, -24, 0, -24, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0,
##        0, 0, 0, 0 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
# in general characters of centre involve cyclotomics
# we do the splitting with the expanded character
#

InstallMethod(SplitCharacterByCentre,
              [IsCCTable and HasSplittingCentre, IsList], 
function(CCT, ech)
  local zchars, nch, inv, zmaps, zind, reps, zgal, res, pos, coeffs, i, a;

  zchars := CCT!.zchars;
  nch := Length(zchars);
  inv := CCT!.invzchars;
  zmaps := CCT!.zmaps;
  zind := zmaps[1];
  reps := CCT!.zchreps;
  zgal := CCT!.zgalois;

  res := [];
  if ech[1] <> 0 then
    pos := Position(zchars, ech{zind}/ech[1]);
  else
    pos := fail;
  fi;
  if pos <> fail then
    # nothing to do
    res[pos] := ech;
  else
    for i in [1..nch] do
      res[i] := [];
    od;
    for a in zmaps do
      coeffs := (ech{a} * inv[2]) / inv[1];
      for i in [1..nch] do
        res[i]{a} := coeffs[i]*zchars[i];
      od;
    od;
  fi;
  # we Galois conjugate all characters such that they belong to the
  # character of the centre representing its Galois orbit
  for i in [1..nch] do
    if IsBound(res[i]) and IsBound(zgal[i]) then
      res[i] := GaloisCyc(res[i], zgal[i][3]);
    fi;
  od;
  for i in [1..nch] do
    if IsBound(res[i]) then
      if IsZero(res[i]) then
        Unbind(res[i]);
      fi;
    fi;
  od;
  return res;
end);
# ch is a character encoded in CCT format
InstallMethod(SplitEncodedCharacterByCentre, 
              [IsCCTable and HasSplittingCentre, IsList], 
function(CCT, ch)
  local zchars, nch, inv, zmaps, zind, reps, zgal, res, ech, pos, coeffs, i, a;

  zchars := CCT!.zchars;
  nch := Length(zchars);
  inv := CCT!.invzchars;
  zmaps := CCT!.zmaps;
  zind := zmaps[1];
  reps := CCT!.zchreps;
  zgal := CCT!.zgalois;

  res := [];
  ech := ExpandFromCCTable(CCT, [ch])[1];
  if ech[1] <> 0 then
    pos := Position(zchars, ech{zind}/ech[1]);
  else
    pos := fail;
  fi;
  if pos <> fail then
    # nothing to do
    res[pos] := ech;
  else
    for i in [1..nch] do
      res[i] := [];
    od;
    for a in zmaps do
      coeffs := (ech{a} * inv[2]) / inv[1];
      for i in [1..nch] do
        res[i]{a} := coeffs[i]*zchars[i];
      od;
    od;
  fi;
  # we Galois conjugate all characters such that they belong to the
  # character of the centre representing its Galois orbit
  for i in [1..nch] do
    if IsBound(res[i]) and IsBound(zgal[i]) then
      res[i] := GaloisCyc(res[i], zgal[i][3]);
    fi;
  od;
  for i in [1..nch] do
    if IsBound(res[i]) then
      if IsZero(res[i]) then
        Unbind(res[i]);
      else
        res[i] := EncodeForCCTable(CCT, [res[i]])[1];
      fi;
    fi;
  od;
  return res;
end);

##  InstallMethod(SplitCharactersByCentre, 
##                ["IsCCTable and HasSplittingCentre", "IsList"], 
##  function(CCT, chs)
##    local zchars, inv, zmaps, zind, reps, res, 
##          echs, ech, pos, r, coeffs, i, j, a;
##  
##    zchars := CCT!.zchars;
##    inv := CCT!.invzchars;
##    zmaps := CCT!.zmaps;
##    zind := zmaps[1];
##    reps := CCT!.zchreps;
##  
##    res := [];
##    for i in reps do
##      res[i] := [];
##    od;
##    echs := ExpandFromCCTable(CCT, chs);
##    for j in [1..Length(chs)] do
##      ech := echs[j];
##      if ech[1] <> 0 then
##        pos := Position(zchars, ech{zind}/ech[1]);
##      else
##        pos := fail;
##      fi;
##      if pos <> fail then
##        # nothing to do
##        if pos in reps then
##          Add(res[pos], chs[j]);
##        fi;
##      else
##        r := [];
##        for i in reps do
##          r[i] := [];
##        od;
##        for a in zmaps do
##          coeffs := (ech{a} * inv[2]) / inv[1];
##          for i in reps do
##            r[i]{a} := coeffs[i]*zchars[i];
##          od;
##        od;
##        r{reps} := EncodeForCCTable(CCT, r{reps});
##        for i in reps do
##          Add(res[i], r[i]);
##        od;
##      fi;
##    od;
##    return res;
##  end);

