

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

