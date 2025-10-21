###########################################################################
##  UTable.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to create a UTable for a finite group.
##  This will be used as a container for computing the irreducible characters
##  of the group without using 'CharacterTable'.
##  
##  Characters are stored as lists of values only on representing classes of
##  rational classes (the remaining values can be computed with GaloisCyc,
##  see 'RatClassExps'.
##  
##  We install various attributes for UTable which delegate to the group.
##  
##  Furthermore, there are functions to import generalized characters in
##  various formats, and to LLL-reduce the lattice of generalized characters
##  found so far.
##  
##  The method 'Irr' for a 'UTable' computes all irreducibles, essentially
##  via Unger's algorithm, using the functionality of this package.

# create (empty) UTable
InstallMethod(UTable, ["IsGroup"], function(G)
  local res;
  # we have lists for characters: i irreducible,
  # n: newly imported or computed characters
  # and an LLL record to which we can add new characters and
  # extract irreducible ones
  res := ObjectifyWithAttributes(rec(ichars := [], nchars := []), 
                                 UTableType, UnderlyingGroup, G);
  res!.lll := LLLRecord({v,w}-> ScalarProduct(res, v, w), 9/10);
  return res;
end);
InstallMethod(ViewObj, ["IsUTable"], function(UT)
  Print("UTable( ");
  ViewObj(UnderlyingGroup(UT));
  Print(" )");
end);
InstallMethod(PrintObj, ["IsUTable"], function(UT)
  Print("UTable( ");
  PrintObj(UnderlyingGroup(UT));
  Print(" )");
end);

# delegate some attributes to group
InstallOtherMethod(Size, ["IsUTable"], 
  UT-> Size(UnderlyingGroup(UT)));
InstallOtherMethod(ConjugacyClasses, ["IsUTable"], 
  UT-> ConjugacyClasses(UnderlyingGroup(UT)));
InstallOtherMethod(NrConjugacyClasses, ["IsUTable"], 
  UT-> NrConjugacyClasses(UnderlyingGroup(UT)));
InstallOtherMethod(PowerMapsOfAllClasses, ["IsUTable"], 
  UT-> PowerMapsOfAllClasses(UnderlyingGroup(UT)));
InstallOtherMethod(RationalClassSets, ["IsUTable"], 
  UT-> RationalClassSets(UnderlyingGroup(UT)));
InstallMethod(NrRationalClasses, ["IsUTable"], 
  UT-> Length(RationalClassSets(UT)));
InstallMethod(NrRationalClasses, ["IsGroup"], 
  G-> Length(RationalClassSets(G)));
InstallMethod(RationalClassIndices, ["IsGroup"], 
  G-> List(RationalClassSets(G), a-> a[1]));
InstallMethod(RationalClassIndices, ["IsUTable"], 
  UT-> RationalClassIndices(UnderlyingGroup(UT)));
InstallOtherMethod(OrdersClassRepresentatives, ["IsUTable"],
  UT-> List(ConjugacyClasses(UT), c-> Order(Representative(c))));
InstallOtherMethod(SizesConjugacyClasses, ["IsUTable"],
  UT-> List(ConjugacyClasses(UT), Size));


##  importing generalized characters on all classes (ordered as in G)
##  or from character table of G, they are added to
##  the list of new characters UT!.nchars after subtracting the projection
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
BindGlobal("EncodeForUTable", function(UT, l)
  local rci, ind, len, res, t, idc, ch, c, v, r, co, pol, cc, s, i, j;
  rci := RationalClassesInfo(UT);
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
  return res;
end);

# import generalized characters already encoded in UT format
BindGlobal("ImportEncodedToUTable", function(UT, vs)
  local lvs, ll, lic, lnc, c, v, i, ic;
  if Length(vs) = 0 then
    return;
  fi;

  # if we split characters by centre, we first split the input characters
  # (otherwise we mimic the splitting setup by lists with one entry)
  if HasSplittingCentre(UT) then
    lvs := SplitCharactersByCentre(UT, vs);
    ll := UT!.lll;
    lic := UT!.ichars;
    lnc := UT!.nchars;
  else
    lvs := [vs];
    ll := [UT!.lll];
    lic := [UT!.ichars];
    lnc := [UT!.nchars];
  fi;
  for i in [1..Length(lvs)] do
    if IsBound(lvs[i]) then
      vs := lvs[i];
      for v in vs do
        # reduce with known irreducibles
        # note that after splitting the functions in lvs[i] can
        # only have irreducibles in lic[i] as constituents
        for ic in lic[i] do
          c := ScalarProduct(UT, v, ic);
          if c <> 0 then
            v := v - c * ic;
          fi;
        od;

        if not (IsZero(v) or v in ll[i].vectors or v in lnc[i]) then
          Add(lnc[i], v);
        fi;
      od;
    fi;
  od;
end);
# import generalized characters given by values on classes of G
BindGlobal("ImportToUTable", function(UT, chs)
  local vs;
  vs := EncodeForUTable(UT, chs);
  ImportEncodedToUTable(UT, vs);
end);
# Converse of import:
# l can be a list of integer vectors in the format of characters in UT.
# Without argument l all characters in UT!.ichars will be expanded.
BindGlobal("ExpandFromUTable", function(UT, li...)
  local lli, gal, rci, res, tmp, r, v, c, x, vals, i, l, k, e;
  if Length(li) > 0 then
    li := li[1];
    if li=[] then
      return [];
    else
      lli := [li];
      gal := [[]];
    fi;
  else
    if not HasSplittingCentre(UT) then
      lli := [UT!.ichars];
      gal := [[]];
    else
      # in splitting centre case we also return Galois conjugates
      lli := [];
      gal := [];
      for i in UT!.zchreps do
        Add(lli, UT!.lll[i]);
        Add(gal, List(Filtered(UT!.zgalois, a-> a[1]=i), b-> b[2]));
      od;
    fi;
  fi;

  rci := RationalClassesInfo(UT);
  res := [];
  
  for k in [1..Length(lli)] do
    li := lli[k];
    tmp := [];
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
      Add(tmp, v);
    od;
    Append(res, tmp);
    for e in gal[k] do
      Append(res, GaloisCyc(tmp, e));
    od;
  od;
  return res;
end);

# extend LLL record by new characters in UT!.nchars
# done in a loop of adding a few new characters, reducing and cleaning 
# the LLL record (this can avoid the computation of many scalar products)
BindGlobal("ExtendLLLUTable", function(UT, k...)
  local lnc, ll, nc, lll, len, rg, i;
  # we reduce at most k new characters at a time
  if Length(k) > 0 then
    k := k[1];
  else
    k := 10;
  fi;

  # in case of splitting centre we consider each LLL record separately
  if HasSplittingCentre(UT) then
    lnc := [];
    ll := [];
    for i in UT!.zchreps do
      Add(lnc, UT!.nchars[i]);
      Add(ll, UT!.lll[i]);
    od;
  else
    lnc := [UT!.nchars];
    ll := [UT!.lll];
  fi;

  for i in [1..Length(lnc)] do
    nc := lnc[i];
    lll := ll[i];
    len := Length(nc);
    rg := [1..k];
    while rg[1] <= len do
      if rg[Length(rg)] > len then
        rg := [rg[1]..len];
      fi;
      AddVectorsLLLRecord(lll, nc{rg});
      CleanLLLRecord(lll);
      rg := [rg[1]+k..rg[1]+(2*k-1)];
    od;
    while Length(nc) > 0 do Remove(nc); od;
  od;
end);


# reduce characters in UT!.lll and
# move found irreducibles to UT!.ichars, and remove those from the remaining
# characters
# (in case of splitting by centre we can handle the part for each character
# of the centre separately)
BindGlobal("ReduceUTable", function(UT, delta...)
  local RL, ncl, ll, lic, lmul, lll, nirr, irr, g, len, m, oc, noc, ch, 
        ng, gg, v, ni, ic, sfi, sfo, sdet, i, j, k;
  if ReduceLLLRecordInternal <> fail then
    RL := ReduceLLLRecordInternal;
  else
    RL := ReduceLLLRecord;
  fi;
  if Length(delta) > 0 then
    delta := delta[1];
  else
    if HasSplittingCentre(UT) then
      delta := UT!.lll[UT!.zchreps[1]].y;
    else
      delta := UT!.lll.y;
    fi;
  fi;
  ncl := NrConjugacyClasses(UT);
  
  if HasSplittingCentre(UT) then
    ll := [];
    lic := [];
    lmul := [];
    for i in UT!.zchreps do
      Add(ll, UT!.lll[i]);
      Add(lic, UT!.ichars[i]);
      Add(lmul, UT!.zchmults[i]);
    od;
  else
    ll := [UT!.lll];
    lic := [UT!.ichars];
    lmul := [1];
  fi;

  for k in [1..Length(ll)] do
    # reduce and clean
    lll := ll[k];
    RL(lll, delta);
    CleanLLLRecord(lll);
    
    # now check for irreducibles and adjust
    nirr := [];
    irr := [];
    g := lll.gram;
    len := Length(g);
    for i in [1..len] do
      if g[i][i] = 1 then
        Add(irr, i);
      else
        Add(nirr, i);
      fi;
    od;
    # since g is lower triangular
    m := function(i,j)
      if j <= i then
        return g[i][j];
      else
        return g[j][i];
      fi;
    end;
    if Length(irr) > 0 then
      oc := lll.vectors;
      # new list of vectors
      noc := [];
      for i in nirr do
        ch := oc[i];
        # subtract irreducibles in irr
        for j in irr do
          ch := ch - m(i,j)*oc[j];
        od;
        Add(noc, ch);
      od;
      # new gram
      ng := [];
      gg := [];
      for i in nirr do
        # write reduced character as sum of new irreducibles and remain
        # (all mutually orthogonal) -> easy to get new gram entry from old
        gg[i] := List(irr, k-> m(i,k));
        v := [];
        for j in nirr do
          if j <= i then
            Add(v, g[i][j] - gg[i]*gg[j]);
          fi;
        od;
        Add(ng, v);
      od;
      # remove zero characters from new characters
      for i in [Length(noc), Length(noc)-1..1] do
        if IsZero(noc[i]) then
          Remove(noc, i);
          Remove(ng, i);
          for v in ng do
            Remove(v, i);
          od;
        fi;
      od;
      # move the new irreducibles (after adjusting sign)
      ni := oc{irr};
      ic := lic[k];
      for ch in ni do
        if ch[1] < 0 then
          Add(ic, -ch);
        else
          Add(ic, ch);
        fi;
      od;
      # reset LLL record
      lll.vectors := noc;
      lll.gram := ng;
      lll.n := Length(ng);
      lll.kmax := 0;
      lll.r := 0;
      lll.mue := [];
      lll.B := [];
      lll.H := [];
      RL(lll, delta);
    fi;
  od;
  sfi := function()
    local res, sum, i;
    if not HasSplittingCentre(UT) then
      return Length(lic[1]);
    else
      res := [];
      sum := 0;
      for i in [1..Length(ll)] do
        sum := sum + lmul[i]*Length(lic[i]);
        if lmul[i] = 1 then
          Add(res, String(Length(lic[i])));
        else
          Add(res, Concatenation(String(lmul[i]),"*",String(Length(lic[i]))));
        fi;
      od;
      res := JoinStringsWithSeparator(res, "+");
      return Concatenation(res, "=", String(sum));
    fi;
  end;
  sfo := function()
    local res, sum, i;
    if not HasSplittingCentre(UT) then
      return Length(ll[1].vectors);
    else
      res := [];
      sum := 0;
      for i in [1..Length(ll)] do
        sum := sum + lmul[i]*Length(ll[i].vectors);
        if lmul[i] = 1 then
          Add(res, String(Length(ll[i].vectors)));
        else
          Add(res, Concatenation(String(lmul[i]),"*",String(Length(ll[i].vectors))));
        fi;
      od;
      res := JoinStringsWithSeparator(res, "+");
      return Concatenation(res, "=", String(sum));
    fi;
  end;
  sdet := function()
    local det, res, a;
    det := DeterminantGramUTable(UT);
    if IsInt(det) then 
      return det;
    else
      res := [];
      for a in det do
        if a[2] <> 1 then
          Add(res, Concatenation(String(a[1]), "^", String(a[2])));
        else
          Add(res, String(a[1]));
        fi;
      od;
      return JoinStringsWithSeparator(res,"*");
    fi;
  end;
  Info(InfoUTable, 1, "|irr| = ",sfi(), "/", ncl,  " |other| = ",
                      sfo(), " det(Gram) = ", sdet());
end);

# Can be useful information
BindGlobal("DeterminantGramUTable", function(UT)
  local res, l, i;
  if not HasSplittingCentre(UT) then
    return Product(Filtered(UT!.lll.B, c-> c<>0));
  else
    res := [];
    for i in UT!.zchreps do
      l := UT!.lll[i].B;
      Add(res, [Product(Filtered(l, c-> c<>0)), UT!.zchmults[i]]);
    od;
    return res;
  fi;
end);

# The main automatic function.
# Can be called from the start or after adding characters by hand.
# We keep this version which uses 'InducedFromElementary' and first skips
# elementary subgroups with many conjugacy classes.
BindGlobal("IrrUTable1", 
function(UT)
  local G, len, scen, ncl, ords, op, v, l, det, 
        mc, mnc, g, i, a, j;
  G := UnderlyingGroup(UT);
  len := NrRationalClasses(UT);
  scen := SizesCentralizers(UT);
  ncl := NrConjugacyClasses(UT);
  ords := OrdersClassRepresentatives(UT);
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

  # induce from all (maximal) cyclic subgroups
  Info(InfoUTable, 1, "Induce from maximal cyclic subgroups");
  ImportToUTable(UT, InducedFromAllMaximalCyclicSubgroups(G));
  
  # Note that it is not good to add the trivial character as
  # irreducible first, because reduction with it will make
  # sparse induced characters non-sparse.
  Info(InfoUTable, 1, "Trivial and natural characters");
  ImportToUTable(UT, [0*[1..ncl]+1]);
  l := NaturalCharacters(G);
  ImportToUTable(UT, l);

  ExtendLLLUTable(UT);
  ReduceUTable(UT);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Cheap characters from power maps");
  l := SmallPowerMapCharacters(G);
  ImportToUTable(UT, l);

  # Reduce these
  ExtendLLLUTable(UT);
  ReduceUTable(UT);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;

  # now induce from (maximal) non-cyclic elementary subgroups
  mnc := MaximalNonCyclicElementarySubgroups(G);
  if not IsBound(UT!.mncdone) then
    UT!.mncdone := [];
    UT!.mncbig := [];
    UT!.mncbigncl := [];
  fi;
  # first only cases where p is still in determinant of Gram matrix
  # (this is in the index of the lattice found so far)
  for a in mnc do
    if not a in UT!.mncdone then
      det := DeterminantGramUTable(UT);
      if det mod a[2] = 0 then
        # avoid excessive number of induced characters
        l := InducedFromElementary(UT, a[1], a[2], 1000);
        if IsInt(l) then
          Info(InfoUTable, 1, "Skipping elementary ",a,
               " with ",l," conjugacy classes");
          Add(UT!.mncbig, a);
          Add(UT!.mncbigncl, l);
        else
          Info(InfoUTable, 1, "Induce from elementary ", a,
                " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
          ImportToUTable(UT, l);
          AddSet(UT!.mncdone, a);
          ExtendLLLUTable(UT);
          ReduceUTable(UT);
          if Length(UT!.ichars) = ncl then
            Sort(UT!.ichars);
            return UT!.ichars;
          fi;
        fi;
      fi;
    fi;
  od;
  # if not done the remaining cases with not too many classes
  for a in mnc do
    if not a in UT!.mncdone and not a in UT!.mncbig then
      l := InducedFromElementary(UT, a[1], a[2], 1000);
      if IsInt(l) then
        Info(InfoUTable, 1, "Skipping elementary ",a,
             " with ",l," conjugacy classes");
        Add(UT!.mncbig, a);
        Add(UT!.mncbigncl, l);
      else
        Info(InfoUTable, 1, "Induce from elementary ", a,
              " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
        ImportToUTable(UT, l);
        AddSet(UT!.mncdone, a);
        ExtendLLLUTable(UT);
        ReduceUTable(UT);
        if Length(UT!.ichars) = ncl then
          Sort(UT!.ichars);
          return UT!.ichars;
        fi;
      fi;
    fi;
  od;
  # remaining elementary subgroups, first those with fewer classes
  SortParallel(UT!.mncbigncl, UT!.mncbig);
  for i in [1..Length(UT!.mncbig)] do
    a := UT!.mncbig[i];
    Info(InfoUTable, 1, "Induce from elementary ", a,
          " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]), 
          " (", UT!.mncbigncl[i], " classes)");
    l := InducedFromElementary(UT, a[1], a[2]);
    ImportToUTable(UT, l);
    AddSet(UT!.mncdone, a);
    ExtendLLLUTable(UT);
    ReduceUTable(UT);
    if Length(UT!.ichars) = ncl then
      Sort(UT!.ichars);
      return UT!.ichars;
    fi;
  od;

  # we should be done by now, but maybe we need a stronger LLL
  ExtendLLLUTable(UT);
  ReduceUTable(UT, 99999/100000);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;
  
  # we give up, print a warning and return fail
  Info(InfoWarning, 1, "Irr for UTable: not all irreducibles found.\n",
       "Maybe try LLL with delta=1, or add some characters...");
  return fail;
end);

# In this version we use 'InductionDataFromElementaryUTable' to avoid huge
# character tables of elementary subgroups (characters are produced by and
# by). We start with elementary subgroups close to Sylow subgroups which
# often yield many useful generalized characters.
# Optional parameter k (default k=10) says how often the LLL data are
# cleaned up (seems little overhead and avoids the computation of too many 
# scalar products).
BindGlobal("IrrUTable2",  function(UT, k...)
  local G, len, scen, ncl, ords, op, found, allirr, l, mnc, det, 
        idat, next, vs, a, v;
  if Length(k) > 0 then
    k := k[1];
  else
    k := 10;
  fi;
  G := UnderlyingGroup(UT);
  len := NrRationalClasses(UT);
  scen := SizesCentralizers(UT);
  ncl := NrConjugacyClasses(UT);
  ords := OrdersClassRepresentatives(UT);
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

  # helper to count and collect the found irreducibles
  found := function()
    if HasSplittingCentre(UT) then
      return Sum(UT!.zchreps, i-> UT!.zchmults[i] * Length(UT!.ichars[i]));
    else
      return Length(UT!.ichars);
    fi;
  end;
  allirr := function()
    local res, tmp, i, a;
    if HasSplittingCentre(UT) then
      res := [];
      for i in UT!.zchreps do
        tmp := UT!.ichars[i];
        Sort(tmp);
        Append(res, tmp);
        for a in UT!.zgalois do
          if a[1] = i then
            Append(res, EncodeForUTable(UT, 
                               GaloisCyc(ExpandFromUTable(UT, tmp), a[2])));
          fi;
        od;
      od;
      return res;
    else
      Sort(UT!.ichars);
      return UT!.ichars;
    fi;
  end;


  # induce from all (maximal) cyclic subgroups
  Info(InfoUTable, 1, "Induce from maximal cyclic subgroups");
  ImportToUTable(UT, InducedFromAllMaximalCyclicSubgroups(G));
  
  # Note that it is not good to add the trivial character as
  # irreducible first, because reduction with it will make
  # sparse induced characters non-sparse.
  Info(InfoUTable, 1, "Trivial and natural characters");
  ImportToUTable(UT, [0*[1..ncl]+1]);
  l := NaturalCharacters(G);
  ImportToUTable(UT, l);

  ExtendLLLUTable(UT, k);
  ReduceUTable(UT);
  if found() = ncl then
    return allirr();
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Cheap characters from power maps");
  l := SmallPowerMapCharacters(G);
  ImportToUTable(UT, l);

  # Reduce these
  ExtendLLLUTable(UT, k);
  ReduceUTable(UT);
  if found() = ncl then
    return allirr();
  fi;

  # now induce from (maximal) non-cyclic elementary subgroups
  mnc := MaximalNonCyclicElementarySubgroups(G);
  if not IsBound(UT!.mncdone) then
    UT!.mncdone := [];
  fi;
  # first only cases where p is still in determinant of Gram matrix
  # (this is in the index of the lattice found so far)
  for a in mnc do
    if not a in UT!.mncdone then
      det := DeterminantGramUTable(UT);
      if IsInt(det) then
        det := [[det]];
      fi;
      if ForAny(det, m-> m[1] mod a[2] = 0) then
        Info(InfoUTable, 1, "Induce from elementary ", a,
                " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
        idat := InductionDataFromElementaryUTable(UT, a[1], a[2]);
        next := idat.next;
        vs := Set(next());
        while vs <> fail do
          ImportEncodedToUTable(UT, vs);
          if Length(UT!.nchars) > 500 then
            ExtendLLLUTable(UT, k);
            ReduceUTable(UT);
          fi;
          if found() = ncl then
            return allirr();
          fi;
          vs := next();
        od;
        if Length(UT!.nchars) > 0 then
          ExtendLLLUTable(UT, k);
          ReduceUTable(UT);
        fi;
        if found() = ncl then
          return allirr();
        fi;
        AddSet(UT!.mncdone, a);
      fi;
    fi;
  od;
  # if not done we also need the remaining elementary subgroups
  for a in mnc do
    if not a in UT!.mncdone then
      Info(InfoUTable, 1, "Induce from elementary ", a,
              " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
      idat := InductionDataFromElementaryUTable(UT, a[1], a[2]);
      next := idat.next;
      vs := Set(next());
      while vs <> fail do
        ImportEncodedToUTable(UT, vs);
        if Length(UT!.nchars) > 500 then
          ExtendLLLUTable(UT, k);
          ReduceUTable(UT);
        fi;
        if found() = ncl then
          return allirr();
        fi;
        vs := next();
      od;
      if Length(UT!.nchars) > 0 then
        ExtendLLLUTable(UT, k);
        ReduceUTable(UT);
      fi;
      if found() = ncl then
        return allirr();
      fi;
      AddSet(UT!.mncdone, a);
    fi;
  od;

  # we should be done by now, but maybe we need a stronger LLL
  ExtendLLLUTable(UT, k);
  ReduceUTable(UT, 9999999/10000000);
  if found() = ncl then
    return allirr();
  fi;
  
  # we give up, print a warning and return fail
  Info(InfoWarning, 1, "Irr for UTable: not all irreducibles found.\n",
       "Maybe try LLL with delta=1, or add some characters...");
  return fail;
end);

# we use second as default method
InstallOtherMethod(Irr, ["IsUTable"], UT-> IrrUTable2(UT, 10));


# hnf  integer matrix in Hermite normal form
# piv  indices of pivot columns of hnf
# v    integer vector in Q-span of the rows of hnf
# changes hnf to Hermite normal form of lattice extended by v
# returns index of lattice of hnf in extended lattice
AddVectorToHNF := function(hnf, piv, v)
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
end;

UTableHNFCyclic := function(UT)
  local G, it, iti, hnf, piv, In;
  G := UnderlyingGroup(UT);
  it := InducedFromAllMaximalCyclicSubgroups(G);
  iti := EncodeForUTable(UT, it);
  hnf := HermiteNormalFormIntegerMat(iti);
  hnf := Filtered(hnf, a-> not IsZero(a));
  piv := List(hnf, a-> First([1..Length(a)], i-> a[i]<>0));
  return rec(matrix := hnf, pivots := piv, index := 1);
end;

HNF:=0;
IrrUTable3 := function(UT)
  local finalize, G, t, rci, ncl, icyc, mat, hnf, pos, dim, piv, gram, hgram, 
        index, ind, vs, scen, ords, op, mnc, data, j, ps, p, e, idat, next, 
        good, bad, oldindex, In, v, i;

  # find irreducibles when whole lattice of generalized characters found
  finalize := function()
    local t, lll, norms;
    Info(InfoUTable, 1, "Lattice complete, using LLL for irreducibles.");
    t := Runtime();
    lll := UT!.lll;
    norms := List(hnf, c-> ScalarProduct(UT,c,c));
    SortParallel(norms, hnf);
    AddVectorsLLLRecord(lll, hnf);
    ReduceUTable(UT);
    if Length(UT!.ichars) <> ncl then
      # try harder
      ReduceUTable(UT, 999999/1000000);
    fi;
    Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
    if Length(UT!.ichars) <> ncl then
      Info(InfoWarning, 1, "LLL does not find all irreducibles!");
      return fail;
    fi;
    return UT!.ichars;
  end;

  G := UnderlyingGroup(UT);
  Info(InfoUTable, 1, "Computing info on rational classes.");
  t := Runtime();
  rci := RationalClassesInfo(UT);
  ncl := NrConjugacyClasses(G);
  Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));

  # all induced characters from cyclic subgroups
  Info(InfoUTable, 1, "Inducing characters from all maximal cyclic subgroups.");
  t := Runtime();
  icyc := InducedFromAllMaximalCyclicSubgroups(G);
  mat := EncodeForUTable(UT, icyc);
  Info(InfoUTable, 1, "      ", Length(mat), " characters   ", StringTime(Runtime()-t));

  # Hermite normal form
  Info(InfoUTable, 1, "Finding Hermite normal form for character values.");
  t := Runtime();
  hnf := HermiteNormalFormIntegerMat(mat);
  pos := First([1..Length(hnf)], i-> IsZero(hnf[i]));
  if pos <> fail then
    hnf := hnf{[1..pos-1]};
  fi;
  dim := Length(hnf);
  piv := List(hnf, a-> First([1..Length(a)], i-> a[i]<>0));
  Info(InfoUTable, 1, "      dimension ", dim, "   ", StringTime(Runtime()-t));

  # find index
  Info(InfoUTable, 1, "Computing index of all generalized characters.");
  t := Runtime();
  gram := List(hnf, c-> List(hnf, d-> ScalarProduct(UT, c, d)));
##    hgram := HermiteNormalFormIntegerMat(gram);
##    gram := 0;
##    index := RootInt(Product([1..dim], i-> hgram[i][i]));
##    hgram := 0;
##  or
##    index := RootInt(DeterminantIntMat(gram));
  # to find the determinant we use that its prime divisors
  # also divide the order |G|
  #TODO  only p in mnc !!!
  ps := Set(Factors(Size(G)));
  index := 1;
  for p in ps do
    e := Sum(ElementaryDivisorsPPartRk(gram, p, dim))/2;
    index := index * p^e;
  od;
  Info(InfoUTable, 1, "      index ", index, "   ", StringTime(Runtime()-t));

  # using trivial and natural characters
  Info(InfoUTable, 1, "Adding trivial and natural characters.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, NaturalCharacters(G)));
  for v in vs do
    ind := ind * AddVectorToHNF(hnf, piv, v);
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Adding cheap characters from power maps.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, SmallPowerMapCharacters(G)));
  for v in vs do
    ind := ind * AddVectorToHNF(hnf, piv, v);
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # Now we need non-cyclic elementary subgroups
  Info(InfoUTable, 1, "Considering maximal non-cyclic elementary subgroups.");
  # helper for info
  scen := SizesCentralizers(UT);
  ords := OrdersClassRepresentatives(UT);
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

  mnc := Reversed(MaximalNonCyclicElementarySubgroups(G));
  data := [];
  # in a first round we only induce a few characters from each elementary
  # subgroup
  for i in [1..Length(mnc)] do
    j := mnc[i][1];
    p := mnc[i][2];
    # not needed if p does not divide index
    if index mod p = 0 then
      Info(InfoUTable, 1, "Inducing some characters from elementary ", [j,p],
                " |C|=",ords[j]," |P|=",op(j, p));
      t := Runtime();
      idat := InductionDataFromElementaryUTable(UT, j, p);
      Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
      t := Runtime();
      #data[i] := idat;
      next := idat.next;
      # we make some statistics and only add a few induced characters in
      # this round
      good := 0;
      bad := 0;
      oldindex := index;
      vs := Set(next());
      #while vs <> fail and 3*good > bad  and index mod p = 0 do
      while vs <> fail and index mod p = 0 do
        ind := 1;
        for v in vs do
          ind := ind * AddVectorToHNF(hnf, piv, v);
        od;
        if ind > 1 then
          good := good+1;
        else
          bad := bad+1;
        fi;
        index := index/ind;
        vs := next();
      od;
      Info(InfoUTable, 1, "      found index ", oldindex/index, " of ", 
                          oldindex, "   ", StringTime(Runtime()-t));
      if index = 1 then
        return finalize();
      fi;
    fi;
  od;
##    # if not yet ready we use the induced characters not yet considered
##    for i in [1..Length(mnc)] do
##      j := mnc[i][1];
##      p := mnc[i][2];
##      # not needed if p does not divide index
##      if index mod p = 0 then
##        Info(InfoUTable, 1, "Inducing remaining characters from elementary ", [j,p],
##                  " |C|=",ords[i]," |P|=",op(j, p));
##        t := Runtime();
##        idat := data[i];
##        next := idat.next;
##        oldindex := index;
##        vs := Set(next());
##        while vs <> fail and index mod p = 0 do
##          ind := 1;
##          for v in vs do
##            ind := ind * AddVectorToHNF(hnf, piv, v);
##          od;
##          index := index/ind;
##          vs := next();
##        od;
##        Info(InfoUTable, 1, "      found index ", oldindex/index, 
##                            "   ", StringTime(Runtime()-t));
##        if index = 1 then
##          return finalize();
##        fi;
##      fi;
##    od;
end;

# reverse ordering of classes for more efficient HNF
IrrUTable4 := function(UT)
  local finalize, G, t, rci, ncl, icyc, mat, hnf, pos, dim, piv, rhnf, gram, 
        c, mnc, ps, index, e, ind, vs, scen, ords, op, j, p, idat, next, 
        oldindex, In, i, v;

  # find irreducibles when whole lattice of generalized characters found
  finalize := function()
    local t, lll, norms;
    hnf := List(hnf, Reversed);
    Info(InfoUTable, 1, "Lattice complete, using LLL for irreducibles.");
    t := Runtime();
    lll := UT!.lll;
    norms := List(hnf, c-> ScalarProduct(UT,c,c));
    SortParallel(norms, hnf);
    AddVectorsLLLRecord(lll, hnf);
    ReduceUTable(UT);
    if Length(UT!.ichars) <> ncl then
      # try harder
      ReduceUTable(UT, 999999/1000000);
    fi;
    Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
    if Length(UT!.ichars) <> ncl then
      Info(InfoWarning, 1, "LLL does not find all irreducibles!");
      return fail;
    fi;
    return UT!.ichars;
  end;

  G := UnderlyingGroup(UT);
  Info(InfoUTable, 1, "Computing info on rational classes.");
  t := Runtime();
  rci := RationalClassesInfo(UT);
  ncl := NrConjugacyClasses(G);
  Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));

  # all induced characters from cyclic subgroups
  Info(InfoUTable, 1, "Inducing characters from all maximal cyclic subgroups.");
  t := Runtime();
  icyc := InducedFromAllMaximalCyclicSubgroups(G);
  mat := EncodeForUTable(UT, icyc);
  Info(InfoUTable, 1, "      ", Length(mat), " characters   ", StringTime(Runtime()-t));

  # Hermite normal form
  Info(InfoUTable, 1, "Finding Hermite normal form for character values.");
  t := Runtime();
  # From now we work with Hermite normal form of the matrix of values.
  # Since many induced characters have values on smaller oder elements we
  # reverse the order of columns for the HNF computations.
  hnf := HermiteNormalFormIntegerMat(List(mat, Reversed));
  pos := First([1..Length(hnf)], i-> IsZero(hnf[i]));
  if pos <> fail then
    hnf := hnf{[1..pos-1]};
  fi;
  dim := Length(hnf);
  piv := List(hnf, a-> First([1..Length(a)], i-> a[i]<>0));
  Info(InfoUTable, 1, "      dimension ", dim, "   ", StringTime(Runtime()-t));

  # find index
  Info(InfoUTable, 1, "Computing index of all generalized characters.");
  t := Runtime();
  rhnf := List(hnf, Reversed);
  gram := List(rhnf, a-> []);
  for i in [1..dim] do
    for j in [1..i] do
      c := ScalarProduct(UT, rhnf[i], rhnf[j]);
      gram[i][j] := c;
      gram[j][i] := c;
    od;
  od;
  rhnf := 0;
  # to find the determinant we use that its prime divisors
  # also divide the order |G|, in this particular case only primes p
  # with non-cyclic p-elementary subgroups are left 
  mnc := Reversed(MaximalNonCyclicElementarySubgroups(G));
  ps := Set(List(mnc, a-> a[2]));
  index := 1;
  for p in ps do
    e := Sum(ElementaryDivisorsPPartRk(gram, p, dim))/2;
    index := index * p^e;
  od;
  Info(InfoUTable, 1, "      index ", index, "   ", StringTime(Runtime()-t));

  # using trivial and natural characters
  Info(InfoUTable, 1, "Adding trivial and natural characters.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, NaturalCharacters(G)));
  for v in vs do
    ind := ind * AddVectorToHNF(hnf, piv, Reversed(v));
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Adding cheap characters from power maps.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, SmallPowerMapCharacters(G)));
  for v in vs do
    ind := ind * AddVectorToHNF(hnf, piv, Reversed(v));
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # Now we need non-cyclic elementary subgroups
  Info(InfoUTable, 1, "Considering maximal non-cyclic elementary subgroups.");
  # helper for info
  scen := SizesCentralizers(UT);
  ords := OrdersClassRepresentatives(UT);
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

  # in a first round we only induce a few characters from each elementary
  # subgroup
  for i in [1..Length(mnc)] do
    j := mnc[i][1];
    p := mnc[i][2];
    # not needed if p does not divide index
    if index mod p = 0 then
      Info(InfoUTable, 1, "Inducing characters from elementary ", [j,p],
                " |C|=",ords[j]," |P|=",op(j, p));
      t := Runtime();
      idat := InductionDataFromElementaryUTable(UT, j, p);
      Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
      t := Runtime();
      next := idat.next;
      oldindex := index;
      vs := Set(next());
      while vs <> fail and index mod p = 0 do
        ind := 1;
        for v in vs do
          ind := ind * AddVectorToHNF(hnf, piv, Reversed(v));
        od;
        index := index/ind;
        vs := next();
      od;
      Info(InfoUTable, 1, "      found index ", oldindex/index, " of ", 
                          oldindex, "   ", StringTime(Runtime()-t));
      if index = 1 then
        return finalize();
      fi;
    fi;
  od;
end;

MkSym := function(A)
  local n, i, j;
  n := Length(A);
  for i in [1..n] do
    for j in [Length(A[i])+1..n] do
      A[i,j] := A[j,i];
    od;
  od;
end;
IrrUTable4a := function(UT)
  local finalize, G, t, rci, ncl, icyc, mat, hnf, pos, dim, piv, rhnf, gram, 
        c, mnc, ps, index, e, ind, vs, scen, ords, op, j, p, idat, next, 
        oldindex, In, i, v;

  # find irreducibles when whole lattice of generalized characters found
  finalize := function()
    local t, lll, H;
    hnf := List(hnf, Reversed);
    Info(InfoUTable, 1, "Lattice complete, using LLL for irreducibles.");
    t := Runtime();
    lll := LLLRecord(UT!.lll.scalar);
    AddVectorsLLLRecord(lll, hnf);
    MkSym(lll.gram);
    H := LLLTransformUnimodularGram(lll.gram);
    if H <> fail then
      lll.vectors := H*lll.vectors;
      lll.gram := H*lll.gram*TransposedMat(H);
    fi;
    UT!.lll := lll;
    ReduceUTable(UT);
    if Length(UT!.ichars) <> ncl then
      # try harder
      ReduceUTable(UT, 999999/1000000);
    fi;
    Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
    if Length(UT!.ichars) <> ncl then
      Info(InfoWarning, 1, "LLL does not find all irreducibles!");
      return fail;
    fi;
    return UT!.ichars;
  end;

  G := UnderlyingGroup(UT);
  Info(InfoUTable, 1, "Computing info on rational classes.");
  t := Runtime();
  rci := RationalClassesInfo(UT);
  ncl := NrConjugacyClasses(G);
  Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));

  # all induced characters from cyclic subgroups
  Info(InfoUTable, 1, "Inducing characters from all maximal cyclic subgroups.");
  t := Runtime();
  icyc := InducedFromAllMaximalCyclicSubgroups(G);
  mat := EncodeForUTable(UT, icyc);
  Info(InfoUTable, 1, "      ", Length(mat), " characters   ", StringTime(Runtime()-t));

  # Hermite normal form
  Info(InfoUTable, 1, "Finding Hermite normal form for character values.");
  t := Runtime();
  # From now we work with Hermite normal form of the matrix of values.
  # Since many induced characters have values on smaller oder elements we
  # reverse the order of columns for the HNF computations.
  hnf := HermiteNormalFormIntegerMat(List(mat, Reversed));
  pos := First([1..Length(hnf)], i-> IsZero(hnf[i]));
  if pos <> fail then
    hnf := hnf{[1..pos-1]};
  fi;
  dim := Length(hnf);
  piv := List(hnf, a-> First([1..Length(a)], i-> a[i]<>0));
  Info(InfoUTable, 1, "      dimension ", dim, "   ", StringTime(Runtime()-t));

  # find index
  Info(InfoUTable, 1, "Computing index of all generalized characters.");
  t := Runtime();
  rhnf := List(hnf, Reversed);
  gram := List(rhnf, a-> []);
  for i in [1..dim] do
    for j in [1..i] do
      c := ScalarProduct(UT, rhnf[i], rhnf[j]);
      gram[i][j] := c;
      gram[j][i] := c;
    od;
  od;
  rhnf := 0;
  # to find the determinant we use that its prime divisors
  # also divide the order |G|, in this particular case only primes p
  # with non-cyclic p-elementary subgroups are left 
  mnc := Reversed(MaximalNonCyclicElementarySubgroups(G));
  ps := Set(List(mnc, a-> a[2]));
  index := 1;
  for p in ps do
    e := Sum(ElementaryDivisorsPPartRk(gram, p, dim))/2;
    index := index * p^e;
  od;
  Info(InfoUTable, 1, "      index ", index, "   ", StringTime(Runtime()-t));

  # using trivial and natural characters
  Info(InfoUTable, 1, "Adding trivial and natural characters.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, NaturalCharacters(G)));
  for v in vs do
    ind := ind * AddVectorToHNF(hnf, piv, Reversed(v));
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Adding cheap characters from power maps.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, SmallPowerMapCharacters(G)));
  for v in vs do
    ind := ind * AddVectorToHNF(hnf, piv, Reversed(v));
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # Now we need non-cyclic elementary subgroups
  Info(InfoUTable, 1, "Considering maximal non-cyclic elementary subgroups.");
  # helper for info
  scen := SizesCentralizers(UT);
  ords := OrdersClassRepresentatives(UT);
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

  # in a first round we only induce a few characters from each elementary
  # subgroup
  for i in [1..Length(mnc)] do
    j := mnc[i][1];
    p := mnc[i][2];
    # not needed if p does not divide index
    if index mod p = 0 then
      Info(InfoUTable, 1, "Inducing characters from elementary ", [j,p],
                " |C|=",ords[j]," |P|=",op(j, p));
      t := Runtime();
      idat := InductionDataFromElementaryUTable(UT, j, p);
      Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
      t := Runtime();
      next := idat.next;
      oldindex := index;
      vs := Set(next());
      while vs <> fail and index mod p = 0 do
        ind := 1;
        for v in vs do
          ind := ind * AddVectorToHNF(hnf, piv, Reversed(v));
        od;
        index := index/ind;
        vs := next();
      od;
      Info(InfoUTable, 1, "      found index ", oldindex/index, " of ", 
                          oldindex, "   ", StringTime(Runtime()-t));
      if index = 1 then
        return finalize();
      fi;
    fi;
  od;
end;
# In IrrUTable4 we quickly find examples where the final LLL computation
# with the HNF basis (or a HNF basis with respect to some ordering of
# classes) is a severe bottleneck.
# 
# In IrrUTable5 we just find generators of the lattice of virtual characters
# consisting of the induced characters from maximal cyclic subgroups,
# followed only by virtual characters which successively enlarge the lattice
# (which we find during the HNF extensions).
IrrUTable5 := function(UT)
  local finalize, G, t, rci, ncl, icyc, mat, useful, hnf, pos, dim, piv, 
        rhnf, new, gram, c, mnc, ps, index, e, ind, vs, scen, ords, op, j, p, 
        norms, idat, next, oldindex, In, i, v;

  # find irreducibles when whole lattice of generalized characters found
  finalize := function()
    local t, lll, norms, len, rg;
    Info(InfoUTable, 1, "Lattice complete, using LLL for irreducibles.");
    # free the memory
    hnf := 0;
    t := Runtime();
    lll := UT!.lll;
    norms := List(useful, c-> ScalarProduct(UT,c,c));
    SortParallel(norms, useful);
    # characters from cyclic subgroups first, then the other 'useful' ones
    AddVectorsLLLRecord(lll, mat);
    CleanLLLRecord(lll);
    len := Length(useful);
    rg := [1..10];
    while rg[1] <= len do
      if rg[10] > len then
        rg := [rg[1]..len];
      fi;
      AddVectorsLLLRecord(lll, useful{rg});
      CleanLLLRecord(lll);
      rg := [rg[1]+10..rg[1]+19];
    od;

    ReduceUTable(UT);
    if Length(UT!.ichars) <> ncl then
      # try harder
      ReduceUTable(UT, 999999/1000000);
    fi;
    Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
    if Length(UT!.ichars) <> ncl then
      Info(InfoWarning, 1, "LLL does not find all irreducibles!");
      return fail;
    fi;
    return UT!.ichars;
  end;

  G := UnderlyingGroup(UT);
  Info(InfoUTable, 1, "Computing info on rational classes.");
  t := Runtime();
  rci := RationalClassesInfo(UT);
  ncl := NrConjugacyClasses(G);
  Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));

  # all induced characters from cyclic subgroups (we sort them by norm)
  Info(InfoUTable, 1, "Inducing characters from all maximal cyclic subgroups.");
  t := Runtime();
  icyc := InducedFromAllMaximalCyclicSubgroups(G);
  mat := EncodeForUTable(UT, icyc);
  norms := List(mat, c-> ScalarProduct(UT, c, c));
  SortParallel(norms, mat);
  Info(InfoUTable, 1, "      ", Length(mat), " characters   ", StringTime(Runtime()-t));

  # Hermite normal form
  Info(InfoUTable, 1, "Finding Hermite normal form for character values.");
  t := Runtime();
  # From now we work with Hermite normal form of the matrix of values.
  # Since many induced characters have values on smaller oder elements we
  # reverse the order of columns for the HNF computations.
  hnf := HermiteNormalFormIntegerMat(List(mat, Reversed));
  pos := First([1..Length(hnf)], i-> IsZero(hnf[i]));
  if pos <> fail then
    hnf := hnf{[1..pos-1]};
  fi;
  dim := Length(hnf);
  piv := List(hnf, a-> First([1..Length(a)], i-> a[i]<>0));
  Info(InfoUTable, 1, "      dimension ", dim, "   ", StringTime(Runtime()-t));

  # find index
  Info(InfoUTable, 1, "Computing index of all generalized characters.");
  t := Runtime();
  rhnf := List(hnf, Reversed);
  gram := List(rhnf, a-> []);
  for i in [1..dim] do
    for j in [1..i] do
      c := ScalarProduct(UT, rhnf[i], rhnf[j]);
      gram[i][j] := c;
      gram[j][i] := c;
    od;
  od;
  rhnf := 0;
  # to find the determinant we use that its prime divisors
  # also divide the order |G|, in this particular case only primes p
  # with non-cyclic p-elementary subgroups are left 
  mnc := Reversed(MaximalNonCyclicElementarySubgroups(G));
  ps := Set(List(mnc, a-> a[2]));
  index := 1;
  for p in ps do
    e := Sum(ElementaryDivisorsPPartRk(gram, p, dim))/2;
    index := index * p^e;
  od;
  Info(InfoUTable, 1, "      index ", index, "   ", StringTime(Runtime()-t));

  # we collect useful vectors here
  useful := [];
  # using trivial and natural characters
  Info(InfoUTable, 1, "Adding trivial and natural characters.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, NaturalCharacters(G)));
  for v in vs do
    new := AddVectorToHNF(hnf, piv, Reversed(v));
    if new > 1 then
      ind := ind * new;
      Add(useful, v);
    fi;
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Adding cheap characters from power maps.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, SmallPowerMapCharacters(G)));
  for v in vs do
    new := AddVectorToHNF(hnf, piv, Reversed(v));
    if new > 1 then
      ind := ind * new;
      Add(useful, v);
    fi;
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # Now we need non-cyclic elementary subgroups
  Info(InfoUTable, 1, "Considering maximal non-cyclic elementary subgroups.");
  # helper for info
  scen := SizesCentralizers(UT);
  ords := OrdersClassRepresentatives(UT);
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
  for i in [1..Length(mnc)] do
    j := mnc[i][1];
    p := mnc[i][2];
    # not needed if p does not divide index
    if index mod p = 0 then
      Info(InfoUTable, 1, "Inducing characters from elementary ", [j,p],
                " |C|=",ords[j]," |P|=",op(j, p));
      t := Runtime();
      idat := InductionDataFromElementaryUTable(UT, j, p);
      Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
      t := Runtime();
      next := idat.next;
      oldindex := index;
      vs := Set(next());
      while vs <> fail and index mod p = 0 do
        ind := 1;
        for v in vs do
          new := AddVectorToHNF(hnf, piv, Reversed(v));
          if new > 1 then
            ind := ind * new;
            Add(useful, v);
          fi;
        od;
        index := index/ind;
        vs := next();
      od;
      Info(InfoUTable, 1, "      found index ", oldindex/index, " of ", 
                          oldindex, "   ", StringTime(Runtime()-t));
      if index = 1 then
        return finalize();
      fi;
    fi;
  od;
end;


# since HNF is only for bookkeeping we ignore non-pivot columns
IrrUTable6 := function(UT)
  local finalize, G, t, rci, ncl, icyc, mat, useful, hnf, pos, dim, piv, 
        rhnf, new, gram, c, mnc, ps, index, e, ind, vs, scen, ords, op, j, p, 
        norms, idat, next, oldindex, In, i, v;

  # find irreducibles when whole lattice of generalized characters found
  finalize := function()
    local t, lll, norms, len, rg;
    Info(InfoUTable, 1, "Lattice complete, using LLL for irreducibles.");
    # free the memory
    hnf := 0;
    t := Runtime();
    lll := UT!.lll;
    norms := List(useful, c-> ScalarProduct(UT,c,c));
    SortParallel(norms, useful);
    # characters from cyclic subgroups first, then the other 'useful' ones
    AddVectorsLLLRecord(lll, mat);
    CleanLLLRecord(lll);
    len := Length(useful);
    rg := [1..10];
    while rg[1] <= len do
      if rg[10] > len then
        rg := [rg[1]..len];
      fi;
      AddVectorsLLLRecord(lll, useful{rg});
      CleanLLLRecord(lll);
      rg := [rg[1]+10..rg[1]+19];
    od;

    ReduceUTable(UT);
    if Length(UT!.ichars) <> ncl then
      # try harder
      ReduceUTable(UT, 999999/1000000);
    fi;
    Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
    if Length(UT!.ichars) <> ncl then
      Info(InfoWarning, 1, "LLL does not find all irreducibles!");
      return fail;
    fi;
    return UT!.ichars;
  end;

  G := UnderlyingGroup(UT);
  Info(InfoUTable, 1, "Computing info on rational classes.");
  t := Runtime();
  rci := RationalClassesInfo(UT);
  ncl := NrConjugacyClasses(G);
  Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));

  # all induced characters from cyclic subgroups (we sort them by norm)
  Info(InfoUTable, 1, "Inducing characters from all maximal cyclic subgroups.");
  t := Runtime();
  icyc := InducedFromAllMaximalCyclicSubgroups(G);
  mat := EncodeForUTable(UT, icyc);
  norms := List(mat, c-> ScalarProduct(UT, c, c));
  SortParallel(norms, mat);
  Info(InfoUTable, 1, "      ", Length(mat), " characters   ", StringTime(Runtime()-t));

  # Hermite normal form
  Info(InfoUTable, 1, "Finding Hermite normal form for character values.");
  t := Runtime();
  # From now we work with Hermite normal form of the matrix of values.
  # Since many induced characters have values on smaller oder elements we
  # reverse the order of columns for the HNF computations.
  hnf := HermiteNormalFormIntegerMat(List(mat, Reversed));
  pos := First([1..Length(hnf)], i-> IsZero(hnf[i]));
  if pos <> fail then
    hnf := hnf{[1..pos-1]};
  fi;
  dim := Length(hnf);
  piv := List(hnf, a-> First([1..Length(a)], i-> a[i]<>0));
  Info(InfoUTable, 1, "      dimension ", dim, "   ", StringTime(Runtime()-t));

  # find index
  Info(InfoUTable, 1, "Computing index of all generalized characters.");
  t := Runtime();
  rhnf := List(hnf, Reversed);
  gram := List(rhnf, a-> []);
  for i in [1..dim] do
    for j in [1..i] do
      c := ScalarProduct(UT, rhnf[i], rhnf[j]);
      gram[i][j] := c;
      gram[j][i] := c;
    od;
  od;
  rhnf := 0;
  # to find the determinant we use that its prime divisors
  # also divide the order |G|, in this particular case only primes p
  # with non-cyclic p-elementary subgroups are left 
  mnc := Reversed(MaximalNonCyclicElementarySubgroups(G));
  ps := Set(List(mnc, a-> a[2]));
  index := 1;
  for p in ps do
    e := Sum(ElementaryDivisorsPPartRk(gram, p, dim))/2;
    index := index * p^e;
  od;
  Info(InfoUTable, 1, "      index ", index, "   ", StringTime(Runtime()-t));

  # from now we just compute with the pivot columns of hnf
  hnf := List(hnf, a-> a{piv});

  # we collect useful vectors here
  useful := [];
  # using trivial and natural characters
  Info(InfoUTable, 1, "Adding trivial and natural characters.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, NaturalCharacters(G)));
  for v in vs do
    new := AddVectorToHNF(hnf, [1..dim], Reversed(v){piv});
    if new > 1 then
      ind := ind * new;
      Add(useful, v);
    fi;
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Adding cheap characters from power maps.");
  ind := 1;
  t := Runtime();
  vs := EncodeForUTable(UT, [1+0*[1..ncl]]);
  Append(vs, EncodeForUTable(UT, SmallPowerMapCharacters(G)));
  for v in vs do
    new := AddVectorToHNF(hnf, [1..dim], Reversed(v){piv});
    if new > 1 then
      ind := ind * new;
      Add(useful, v);
    fi;
  od;
  index := index/ind;
  Info(InfoUTable, 1, "      found index ", ind, "   ", StringTime(Runtime()-t));
  if index = 1 then
    return finalize();
  fi;

  # Now we need non-cyclic elementary subgroups
  Info(InfoUTable, 1, "Considering maximal non-cyclic elementary subgroups.");
  # helper for info
  scen := SizesCentralizers(UT);
  ords := OrdersClassRepresentatives(UT);
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
  for i in [1..Length(mnc)] do
    j := mnc[i][1];
    p := mnc[i][2];
    # not needed if p does not divide index
    if index mod p = 0 then
      Info(InfoUTable, 1, "Inducing characters from elementary ", [j,p],
                " |C|=",ords[j]," |P|=",op(j, p));
      t := Runtime();
      idat := InductionDataFromElementaryUTable(UT, j, p);
      Info(InfoUTable, 1, "      ", StringTime(Runtime()-t));
      t := Runtime();
      next := idat.next;
      oldindex := index;
      vs := Set(next());
      while vs <> fail and index mod p = 0 do
        ind := 1;
        for v in vs do
          new := AddVectorToHNF(hnf, [1..dim], Reversed(v){piv});
          if new > 1 then
            ind := ind * new;
            Add(useful, v);
          fi;
        od;
        index := index/ind;
        vs := next();
      od;
      Info(InfoUTable, 1, "      found index ", oldindex/index, " of ", 
                          oldindex, "   ", StringTime(Runtime()-t));
      if index = 1 then
        return finalize();
      fi;
    fi;
  od;
end;

