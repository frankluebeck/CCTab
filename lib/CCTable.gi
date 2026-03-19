###########################################################################
##  CCTable.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to create a CCTable for a finite group.
##  This will be used as a container for computing the irreducible characters
##  of the group without using 'CharacterTable'.
##  
##  Characters are stored as lists of values only on representing classes of
##  rational classes (the remaining values can be computed with GaloisCyc,
##  see 'RatClassExps' or 'RationalClassesInfo'.
##  
##  We install various attributes for CCTable which delegate to the group.
##  
##  Furthermore, there are functions to import generalized characters in
##  various formats.
##  ???and to LLL-reduce the lattice of generalized characters
##  ???found so far.
##  
##  The method 'Irr' for a 'CCTable' computes all irreducibles.

# utility
BindGlobal("StringCollectedFactors", function(n)
  local c, res, a;
  c := Collected(FactorsInt(n));
  res := "";
  for a in c do
    if Length(res) > 0 then
      Append(res, " ");
    fi;
    Append(res, String(a[1]));
    if a[2] > 1 then
      Append(res, "^");
      Append(res, String(a[2]));
    fi;
  od;
  return res;
end);
# create (empty) CCTable
InstallMethod(CCTable, ["IsGroup"], function(G)
  local res;
  # irr: list of known irreducibles
  # hnfs: list of records for Hermite normal forms
  # UnderlyingGroup
  res := ObjectifyWithAttributes(
         rec(irr := [], 
         hnfs := [rec(new := [], hnf := [], pivots := [], index := 0)]), 
                                 CCTableType, UnderlyingGroup, G);
  return res;
end);
InstallMethod(ViewString, ["IsCCTable"], function(CCT)
  return Concatenation("CCTable( ", ViewString(UnderlyingGroup(CCT)), " )");
end);
InstallMethod(PrintString, ["IsCCTable"], function(CCT)
  return Concatenation("CCTable( ", PrintString(UnderlyingGroup(CCT)), " )");
end);
# not needed, but sometimes yields nicer display without continuation '\'s
InstallMethod(ViewObj, ["IsCCTable"], function(CCT)
  Print("CCTable( ");
  ViewObj(UnderlyingGroup(CCT));
  Print(" )");
end);
InstallMethod(PrintObj, ["IsCCTable"], function(CCT)
  Print("CCTable( ");
  PrintObj(UnderlyingGroup(CCT));
  Print(" )");
end);

# delegate some attributes to underlying group
InstallOtherMethod(Size, ["IsCCTable"], 
  CCT-> Size(UnderlyingGroup(CCT)));
InstallOtherMethod(ConjugacyClasses, ["IsCCTable"], 
  CCT-> ConjugacyClasses(UnderlyingGroup(CCT)));
InstallOtherMethod(NrConjugacyClasses, ["IsCCTable"], 
  CCT-> NrConjugacyClasses(UnderlyingGroup(CCT)));
InstallOtherMethod(PowerMapsOfAllClasses, ["IsCCTable"], 
  CCT-> PowerMapsOfAllClasses(UnderlyingGroup(CCT)));
InstallOtherMethod(RationalClassSets, ["IsCCTable"], 
  CCT-> RationalClassSets(UnderlyingGroup(CCT)));
InstallMethod(NrRationalClasses, ["IsCCTable"], 
  CCT-> Length(RationalClassSets(CCT)));
InstallMethod(RatClassExps, ["IsNearlyCharacterTable and HasUnderlyingGroup"], 
  CCT-> RatClassExps(UnderlyingGroup(CCT)));
InstallMethod(RationalClassesInfo, 
             ["IsNearlyCharacterTable and HasUnderlyingGroup"], 
function(CCT)
  return RationalClassesInfo(UnderlyingGroup(CCT));
end);
InstallOtherMethod(OrdersClassRepresentatives, ["IsCCTable"],
  CCT-> List(ConjugacyClasses(CCT), c-> Order(Representative(c))));
InstallOtherMethod(SizesConjugacyClasses, ["IsCCTable"],
  CCT-> List(ConjugacyClasses(CCT), Size));


##  importing generalized characters on all classes (ordered as in G)
##  or from character table of G, they are added to
##  the list of new characters CCT!.nchars after subtracting the projection
##  on the space of already known irreducibles
##  
##  Note: only rational linear combinations of irreducibles can be handled
##  here, not arbitrary class functions!

# First a separate function to encode characters as integer vector;
# each character can be a list of values (in the ordering of the conjugacy 
# classes of the group) or 
# a class function object (values in ordering of the
# IdentificationOfConjugacyClasses of the table, if this is set).

# first the function that encodes characters as integer vectors using
# RationalClassesInfo(G)
BindGlobal("EncodeForCCTable", function(CCT, l)
  local rci, ind, len, res, t, idc, ch, c, v, r, co, pol, cc, s, i, j, single;
  single := (Length(l) > 0 and not IsList(l[1]));
  if single then l := [l]; fi;
  rci := RationalClassesInfo(CCT);
  ind := List(rci, a-> a.classes[1]);
  len := Length(ind);
  res := [];
  for ch in l do
    if HasUnderlyingCharacterTable(ch) then
      t := UnderlyingCharacterTable(ch);
      if HasIdentificationOfConjugacyClasses(t) then
        idc := IdentificationOfConjugacyClasses(t);
        ch := AsList(ch);
        c := [];
        c{idc} := ch;
        ch := c;
      else
        ch := AsList(ch);
      fi;
    fi;
      
    ch := ch{ind};
    v := [];
    for i in [1..len] do
      r := rci[i];
      co := r.conductor;
      if co = 1 then
        Add(v, ch[i]);
      else
        if IsRat(ch[i]) then
          Add(v, ch[i]);
          for j in [2..r.dim] do
            Add(v, 0);
          od;
        else
          pol := r.cpol;
          cc := CoeffsCyc(ch[i], co);
          s := ReduceCoeffs(cc, pol);
          for j in [1..s] do
            Add(v,cc[j]);
          od;
          for j in [s+1..r.dim] do
            Add(v, 0);
          od;
        fi;
      fi;
    od;
    Add(res, v);
  od;
  if single then res := res[1]; fi;
  return res;
end);

# import generalized characters already encoded in CCT format
BindGlobal("ImportEncodedToCCTable", function(CCT, vs)
  local single, vs2, irr, c, v, hnfs, zgal, lvs, ch, i;

  if Length(vs) = 0 then
    return;
  fi;

  single := (Length(vs) > 0 and not IsList(vs[1]));
  if single then vs := [vs]; fi;

  # subtract known irreducibles
  if Length(CCT!.irr) > 0 then
    vs2 := [];
    irr := CCT!.irr;
    for v in vs do
      for ch in irr do
        c := ScalarProduct(CCT, v, ch);
        if c <> 0 then
          v := v - c*ch;
        fi;
      od;
      Add(vs2, v);
    od;
    vs := vs2;
  fi;
  # if we split characters by centre, we first split the input characters
  # (otherwise we mimic the splitting setup by lists with one entry)
  hnfs := CCT!.hnfs;
  if HasSplittingCentre(CCT) then
    zgal := [];
    for i in [1..Length(CCT!.zchars)] do
      if not IsBound(CCT!.zgalois[i]) then
        Add(zgal, i);
      else
        Add(zgal, CCT!.zgalois[i][1]);
      fi;
    od;
    for v in vs do
      lvs := SplitEncodedCharacterByCentre(CCT, v);
      for i in [1..Length(zgal)] do
        if IsBound(lvs[i]) and not IsZero(lvs[i]) then
          AddSet(hnfs[zgal[i]].new, lvs[i]);
        fi;
      od;
    od;
  else
    hnfs[1].new := Set(Concatenation(hnfs[1].new, vs));
  fi;
end);
# import generalized characters given by values on classes of G
BindGlobal("ImportToCCTable", function(CCT, chs)
  local vs;
  vs := EncodeForCCTable(CCT, chs);
  ImportEncodedToCCTable(CCT, vs);
end);
# Converse of import:
# l can be a list of integer vectors in the format of characters in CCT.
# Without argument l all known irreducible characters stored in CCT will 
# be expanded.
BindGlobal("ExpandFromCCTable", function(CCT, li...)
  local single, rci, res, v, c, x, vals, l, r, i;
  if Length(li) > 0 then
    li := li[1];
    single := (Length(li) > 0 and not IsList(li[1]));
    if single then li := [li]; fi;
  else
    li := CCT!.irr;
    single := false;
  fi;

  rci := RationalClassesInfo(CCT);
  res := [];
  
  for l in li do
    v := [];
    for r in rci do
      c := r.conductor;
      if c = 1 then
        v[r.classes[1]] := l[r.ind];
      else
        x := l{r.ind};
        while Length(x)<c do
          Add(x, 0);
        od;
        x := CycList(x);
        vals := [x];
        for i in [3..Length(r.exponents)] do
          Add(vals, GaloisCyc(x, r.exponents[i]));
        od;
        v{r.classes} := vals;
      fi;
    od;
    Add(res, v);
  od;
  if single then res := res[1]; fi;
  return res;
end);

BindGlobal("HasFullRankCCTable", function(CCT)
  local k;
  k := NrConjugacyClasses(CCT);
  if HasSplittingCentre(CCT) then
    return (Length(CCT!.irr) + Sum(CCT!.zchreps, i-> 
                      CCT!.zchmults[i] * Length(CCT!.hnfs[i].hnf))) = k;
  else
    return (Length(CCT!.irr) + Length(CCT!.hnfs[1].hnf)) = k;
  fi;
end);

BindGlobal("UpdateHNFCCTable", function(CCT)
  local tind, r, ind, m, i;
  tind := 1;
  if HasFullRankCCTable(CCT) then
    if not HasSplittingCentre(CCT) then
      r := CCT!.hnfs[1];
      while Length(r.new) > 0 do
        ind := AddVectorToHNF(r.hnf, r.pivots, Remove(r.new));
        if r.index <> 0 then
          r.index := r.index/ind;
          tind := tind*ind;
        fi;
      od;
    else
      for i in CCT!.zchreps do
        r := CCT!.hnfs[i];
        m := CCT!.zchmults[i];
        while Length(r.new) > 0 do
          ind := AddVectorToHNF(r.hnf, r.pivots, Remove(r.new));
          if r.index <> 0 then
            r.index := r.index/ind;
            tind := tind*ind^m;
          fi;
        od;
      od;
    fi;
  else
    tind := 0;
    for r in CCT!.hnfs do
      if Length(r.new) > 0 then
        r.hnf := HermiteNormalFormIntegerMat(Concatenation(r.hnf, r.new));
        while IsZero(r.hnf[Length(r.hnf)]) do
          Remove(r.hnf);
        od;
        r.pivots := List(r.hnf, v-> First([1..Length(v)], 
                                                i-> not IsZero(v[i])));
        r.new := [];
      fi;
    od;
  fi;
  return tind;
end);

BindGlobal("ImportInducedFromAllMaximalCyclicToCCTable", function(CCT)
  local G, t, im, ords, f, ps, tind, hnf, k, gram, index, e, a, r, i, j, p;
  if IsBound(CCT!.maxcycdone) then
    return;
  fi;
  G := UnderlyingGroup(CCT);
  Info(InfoCCTable, 1, "Inducing characters from all maximal cyclic subgroups.");
  t := Runtime();
  im := InducedFromAllMaximalCyclicSubgroups(G);
  Info(InfoCCTable, 1, "      ", Length(im), " characters   ", 
                                               StringTime(Runtime()-t));

  Info(InfoCCTable, 1, "Computing Hermite normal form of found characters");
  t := Runtime();
  ImportToCCTable(CCT, im);
  # we also update the HNFs
  UpdateHNFCCTable(CCT);
  Info(InfoCCTable, 1, "      ",  StringTime(Runtime()-t));
  # now we know that the index in the character lattice
  # is only divisible by primes p | |G| such that the
  # Sylow-p-subgroup of G is not cyclic; we compute the index
  ords := Set(OrdersClassRepresentatives(CCT));
  f := Collected(Factors(Size(G)));
  Info(InfoCCTable, 1, "Computing index of found lattice in full lattice");
  t := Runtime();
  ps := [];
  for a in f do
    if not a[1]^a[2] in ords then
      Add(ps, a[1]);
    fi;
  od;
  for r in CCT!.hnfs do
    hnf := r.hnf;
    k := Length(hnf);
    gram := List([1..k], i-> []);
    for i in [1..k] do
      for j in [i..k] do
        gram[i,j] := ScalarProduct(CCT, hnf[i], hnf[j]);
        gram[j,i] := gram[i,j];
      od;
    od;
    index := 1;
    for p in ps do
      e := Sum(ElementaryDivisorsPPartRk(gram, p, k))/2;
      index := index * p^e;
    od;
    r.index := index;
  od;
  tind := FindIndexCCTable(CCT);
  Info(InfoCCTable, 1, "       index ",StringCollectedFactors(tind), "   ",  
                            StringTime(Runtime()-t));
  # mark as done
  CCT!.maxcycdone := true;
end);

# find irreducibles in full (sub-)lattice with specific LLL
# for unimodular Gram matrices
BindGlobal("FindIrreduciblesInFullLattices", function(CCT)
  local r, hnf, k, gram, H, nirr, ex, l, i, j, a;
  for l in [1..Length(CCT!.hnfs)] do
    if IsBound(CCT!.hnfs[l]) then
      r := CCT!.hnfs[l];
    fi;
    if r.index = 1 and Length(r.hnf) > 0 then
      hnf := r.hnf;
      k := Length(hnf);
      gram := List([1..k], i-> []);
      for i in [1..k] do
        for j in [i..k] do
          gram[i,j] := ScalarProduct(CCT, hnf[i], hnf[j]);
          gram[j,i] := gram[i,j];
        od;
      od;
      H := LLLTransformUnimodularGram(gram);
      nirr := H * hnf;
      for i in [1..k] do
        if nirr[i,1] < 0 then
          nirr[i] := -nirr[i];
        fi;
      od;
      Sort(nirr);
      Append(CCT!.irr, nirr);
      # maybe we also found some Galois conjugates
      if IsBound(CCT!.zgalois) then
        for a in Set(CCT!.zgalois) do
          if a[1] = l then
            ex := ExpandFromCCTable(CCT, nirr);
            ex := GaloisCyc(ex, a[2]);
            Append(CCT!.irr, EncodeForCCTable(CCT, ex));
          fi;
        od;
      fi;
      r.hnf := [];
      r.new := [];
      r.pivots := [];
      r.index := 1;
    fi;
  od;
end);

# returns the index of lattice of found characters in full lattice
# of irreducible characters
BindGlobal("FindIndexCCTable", function(CCT)
  local tind, i;
  if HasSplittingCentre(CCT) then
    tind := 1;
    for i in CCT!.zchreps do
      if CCT!.hnfs[i].index = 0 then
        return fail;
      else
        tind := tind*CCT!.hnfs[i].index^CCT!.zchmults[i];
      fi;
    od;
  else
    if CCT!.hnfs[1].index = 0 then
      return fail;
    else
      tind := CCT!.hnfs[1].index;
    fi;
  fi;
  return tind;
end);


# This is the default function for computing a full character table
# since HNF is only for bookkeeping we ignore non-pivot columns
BindGlobal("IrrCCTableHNF",  function(CCT)
  local finalize, G, t, rci, ncl, ind, index, scen, ords, op, mnc, 
        j, p, idat, next, oldindex, vs, i;

  # find irreducibles when whole lattice of generalized characters found
  finalize := function()
    Info(InfoCCTable, 1, "Lattice complete, using LLL for irreducibles.");
    t := Runtime();
    FindIrreduciblesInFullLattices(CCT);
    Info(InfoCCTable, 1, "      ", StringTime(Runtime()-t));
    if Length(CCT!.irr) <> ncl then
      Info(InfoWarning, 1, "LLL did not find all irreducibles!");
      return fail;
    fi;
    return CCT!.irr;
  end;

  G := UnderlyingGroup(CCT);
  Info(InfoCCTable, 1, "Computing info on rational classes.");
  t := Runtime();
  rci := RationalClassesInfo(CCT);
  ncl := NrConjugacyClasses(G);
  Info(InfoCCTable, 1, "      ", ncl, " classes, ",
                       Length(rci), " rational      ",StringTime(Runtime()-t));

  # all induced characters from cyclic subgroups
  ImportInducedFromAllMaximalCyclicToCCTable(CCT);

  # to find the determinant we use that its prime divisors
  # also divide the order |G|, in this particular case only primes p
  # with non-cyclic p-elementary subgroups are left 
  # using trivial and natural characters
  Info(InfoCCTable, 1, "Adding trivial and natural characters.");
  ind := FindIndexCCTable(CCT);
  t := Runtime();
  ImportToCCTable(CCT, [1+0*[1..ncl]]);
  ImportToCCTable(CCT, NaturalCharacters(G));
  UpdateHNFCCTable(CCT);
  index := FindIndexCCTable(CCT);
  Info(InfoCCTable, 1, "      found index ", StringCollectedFactors(ind/index),
                       "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # And some cheap characters from power maps
  Info(InfoCCTable, 1, "Adding cheap characters from power maps.");
  ind := index;
  t := Runtime();
  ImportToCCTable(CCT, SmallPowerMapCharacters(G));
  UpdateHNFCCTable(CCT);
  index := FindIndexCCTable(CCT);
  Info(InfoCCTable, 1, "      found index ", StringCollectedFactors(ind/index),
                       "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # Now we need non-cyclic elementary subgroups
  Info(InfoCCTable, 1, "Considering maximal non-cyclic elementary subgroups.");
  # helper for info
  scen := SizesCentralizers(CCT);
  ords := OrdersClassRepresentatives(CCT);
  op := function(i, p)
    local sz, res;
    sz := scen[i]/p;
    res := 1;
    while IsInt(sz) do
      res := res*p;
      sz := sz/p;
    od;
    return res;
  end;

  # We know that we only need to look at p-elementary subgroups when
  # p is still dividing the current index.
  # Also, we stop checking new virtual characters from a p-elementary
  # subgroup when p is no longer dividing the index (can be very useful
  # when something close to the Sylow-p-subgroups with maybe many characters
  # are considered towards the end).
  mnc := Reversed(MaximalNonCyclicElementarySubgroups(G));
  for i in [1..Length(mnc)] do
    j := mnc[i][1];
    p := mnc[i][2];
    # not needed if p does not divide index
    if index mod p = 0 then
      Info(InfoCCTable, 1, "Inducing characters from elementary ", [j,p],
                " |C|=",ords[j]," |P|=",op(j, p));
      t := Runtime();
      idat := InductionDataFromElementaryCCTable(CCT, j, p);
      Info(InfoCCTable, 1, "      ", StringTime(Runtime()-t));
      t := Runtime();
      next := idat.next;
      oldindex := index;
      vs := Set(next());
      while vs <> fail and index mod p = 0 do
        ImportEncodedToCCTable(CCT, vs);
        ind := UpdateHNFCCTable(CCT);
        index := index/ind;
        vs := next();
      od;
      Info(InfoCCTable, 1, "      found index ", 
                           StringCollectedFactors(oldindex/index), " of ", 
                          StringCollectedFactors(oldindex), "   ", 
                          StringTime(Runtime()-t));
      if index = 1 then
        return finalize();
      fi;
    fi;
  od;
  if index <> 1 then
    Error("Lattice still incomplete, this should not happen...");
    return fail;
  fi;
end);


# we use the previous function as default method for Irr of CCTables
InstallOtherMethod(Irr, ["IsCCTable"], IrrCCTableHNF);


# hnf  integer matrix in Hermite normal form
# piv  indices of pivot columns of hnf
# v    integer vector in Q-span of the rows of hnf
# changes hnf to Hermite normal form of lattice extended by v
# returns index of lattice of hnf in extended lattice
BindGlobal("AddVectorToHNF", function(hnf, piv, v)
  local ind, n, npiv, a, j, g, b, jj, ua, aj, c, q, i, k, clean;
  ind := 1;
  n := Length(hnf[1]);
  npiv := Length(piv);
  # reduce new vector
  for i in [1..npiv] do
    j := piv[i];
    if v[j] <> 0 then
      q := -QuoInt(v[j], hnf[i][j]);
      if q <> 0 then
        AddRowVector(v, hnf[i], q, j, n);
      fi;
    fi;
  od;
  if IsZero(v) then
    return 1;
  fi;
  # v extends the lattice
  clean := false;
  for i in [1..npiv] do
    a := hnf[i];
    j := piv[i];
    if v[j] <> 0 then
      q := -QuoInt(v[j], a[j]);
      if q <> 0 then
        AddRowVector(v, a, q, j, n);
      fi;
      if v[j] <> 0 then
        # we have found a vector that enlarges the lattice
        if i=npiv then
          b := MATINTbezout(a[j], 0, v[j], 0);
        else
          jj := piv[i+1];
          b := MATINTbezout(a[j], a[jj], v[j], v[jj]);
        fi;
        # index grows
        ind := ind * (a[j]/b.gcd);
        ua := b.coeff3 * a;
        MultVector(a, b.coeff1);
        AddRowVector(a, v, b.coeff2, j, n);
        AddRowVector(ua, v, b.coeff4, j, n);
        v := ua;
        clean := true;
      fi;
    fi;
    if clean then
      # clean upwards
      aj := a[j];
      for k in [1..i-1] do
        c := hnf[k][j];
        if c >= aj or -c >= aj then
          q := -QuoInt(c, aj);
          if q <> 0 then
            AddRowVector(hnf[k], a, q, j, n);
          fi;
        fi;
      od;
    fi;
  od;
  return ind;
end);

