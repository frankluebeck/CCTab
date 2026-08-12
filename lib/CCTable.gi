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
##  <#GAPDoc Label="CCTable">
##  <ManSection>
##  <Attr Name="CCTable" Arg="G"/>
##  <Returns>an <Ref Filt="IsCCTable"/> object</Returns>
##  <Filt Name="IsCCTable" Arg="CCT"/>
##  <Description>
##  For a finite group <A>G</A> <Ref Attr="CCTable"/>  returns an (initially
##  empty) <E>partial character table container</E> object, in the filter
##  <Ref Filt="IsCCTable"/>. Such an object stores incrementally growing
##  information about the (still unknown) generalized and irreducible
##  characters of <A>G</A>, and is used as the central data structure for
##  computing the irreducible characters of <A>G</A> with the tools in
##  the <Package>CCTab</Package> package. The group <A>G</A> is stored as
##  <C>UnderlyingGroup(<A>CCT</A>)</C> in the result <A>CCT</A>. 
##  Many attributes 
##  of <A>G</A> (for example <Ref Attr="RationalClassesInfo"/>) can
##  also be called with <A>CCT</A> (and delegate to <A>G</A>).
##  <P/>
##  Generalized characters are stored in an <Ref Filt="IsCCTable"/> object
##  as integer vectors (for each rational class only the value on the
##  representing conjugacy class is stored by <C>Phi(c)</C> integers where
##  <C>c</C> is the conductor of that rational class).
##  See <Ref Func="EncodeForCCTable"/> below for a more precise description
##  and for computing this
##  representation of a generalized character from a class function object.
##  <P/>
##  Generalized characters can be added to an <Ref Filt="IsCCTable"/> object 
##  with <Ref Func="ImportToCCTable"/>. The lattice spanned by the known
##  generalized characters is stored via the Hermite normal form of the
##  characters, encoded as integer vectors (in a component <C>!.hnfs</C>).
##  <P/>
##  If the group <A>G</A> has a non-trivial center it can be useful to
##  call <Ref Oper="SplitByCentre"/> with <A>CCT</A>. This is not done by 
##  default because this may cause some non-negligible computations with 
##  conjugacy classes.
##  <P/>
##  The default method for <Ref BookName="Reference" Oper="Irr"/> for an
##  <Ref Filt="IsCCTable"/> object computes the full set of irreducible
##  characters of <A>G</A>. If the <Package>CCTab</Package> package is
##  loaded then for many groups <A>G</A> its <C>CharacterTable(<A>G</A>)</C>
##  will also have an attribute <Ref Attr="CCTable"/> and delegate the
##  computation of the irreducible characters to this <Ref Attr="CCTable"/>.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> CCT := CCTable(G);
##  CCTable( Alt( [ 1 .. 5 ] ) )
##  gap> IsCCTable(CCT);
##  true
##  gap> Irr(CCT);
##  [ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ],
##    [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ],
##    [ 5, 1, -1, 0, 0, 0, 0 ] ]
##  gap> ExpandFromCCTable(CCT, Irr(CCT));
##  [ [ 1, 1, 1, 1, 1 ], [ 3, -1, 0, -E(5)^2-E(5)^3, -E(5)-E(5)^4 ],
##    [ 3, -1, 0, -E(5)-E(5)^4, -E(5)^2-E(5)^3 ], [ 4, 0, 1, -1, -1 ],
##    [ 5, 1, -1, 0, 0 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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


##  <#GAPDoc Label="EncodeForCCTable">
##  <ManSection>
##  <Func Name="EncodeForCCTable" Arg="CCT, l"/>
##  <Returns>an integer vector, or a list of integer vectors</Returns>
##  <Func Name="ExpandFromCCTable" Arg="CCT[, enc]"/>
##  <Returns>a character, or a list of characters</Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object. The argument
##  <A>l</A> is either a single character, or a list of characters, of the
##  underlying group of <A>CCT</A>, each given either as a list of values
##  (in the order of the <Ref BookName="Reference"
##  Attr="ConjugacyClasses"/> of the underlying group) or as a class 
##  function object (with values in the order of
##  <Ref BookName="Reference" Attr="IdentificationOfConjugacyClasses"/>)
##  of its character table.
##  <P/>
##  <Ref Func="EncodeForCCTable"/> returns the encoded form in 
##  which characters are stored
##  in the <Ref Filt="IsCCTable"/> object: for each rational class (see
##  <Ref Attr="RationalClassesInfo"/>) with conductor <M>1</M> this is
##  simply the integer value
##  on that class; for a rational class with conductor <M>c > 1</M> the
##  value on that class is a cyclotomic integer in the <M>c</M>-th
##  cyclotomic field, and it is encoded by the (integer) coefficients of
##  its representation as a polynomial in <M>E(c)</M> modulo the
##  <M>c</M>-th cyclotomic polynomial.  The entries of
##  <C>RationalClassesInfo(<A>CCT</A>)</C> have a component <C>.ind</C>
##  telling the positions of these integer coefficients.
##  If <A>l</A> is a single character,
##  a single integer vector is returned, otherwise a list of vectors,
##  one for each character in <A>l</A>.
##  <P/>
##  <Ref Func="ExpandFromCCTable"/> is the converse function. If the optional
##  argument <A>enc</A> is not given, all irreducible characters
##  of <A>CCT</A> found so far are expanded.
##
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> CCT := CCTable(G);;
##  gap> ind := InducedFromAllMaximalCyclicSubgroups(G);;
##  gap> enc := EncodeForCCTable(CCT, ind);
##  [ [ 12, 0, 0, 2, 0, 0, 0 ], [ 12, 0, 0, 0, 0, 1, 1 ],
##    [ 12, 0, 0, -1, 0, -1, -1 ], [ 20, 0, -1, 0, 0, 0, 0 ],
##    [ 20, 0, 2, 0, 0, 0, 0 ], [ 30, -2, 0, 0, 0, 0, 0 ],
##    [ 30, 2, 0, 0, 0, 0, 0 ] ]
##  gap> ExpandFromCCTable(CCT);
##  [  ]
##  gap> ExpandFromCCTable(CCT, enc);
##  [ [ 12, 0, 0, 2, 2 ], [ 12, 0, 0, E(5)^2+E(5)^3, E(5)+E(5)^4 ],
##    [ 12, 0, 0, E(5)+E(5)^4, E(5)^2+E(5)^3 ], [ 20, 0, -1, 0, 0 ],
##    [ 20, 0, 2, 0, 0 ], [ 30, -2, 0, 0, 0 ], [ 30, 2, 0, 0, 0 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
##  <#GAPDoc Label="ImportToCCTable">
##  <ManSection>
##  <Func Name="ImportToCCTable" Arg="CCT, chs"/>
##  <Func Name="ImportEncodedToCCTable" Arg="CCT, enc"/>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object, and let
##  <A>chs</A> be a generalized character, or list of generalized
##  characters, of the underlying group, given as for
##  <Ref Func="EncodeForCCTable"/> (that is, <E>not</E> yet encoded).
##  <Ref Func="ImportToCCTable"/> encodes <A>chs</A> via 
##  <Ref Func="EncodeForCCTable"/>
##  and imports the result into <A>CCT</A> via
##  <Ref Func="ImportEncodedToCCTable"/>.
##  <P/>
##  <Ref Func="ImportEncodedToCCTable"/> imports <A>enc</A> into
##  <A>CCT</A>: the (encoded) projections of already known irreducible
##  characters of <A>CCT</A> are subtracted, and the remaining vectors are
##  added to the list(s) of newly found generalized characters stored in
##  <A>CCT</A> (split according to the splitting centre of <A>CCT</A>, see
##  <Ref Oper="SplitByCentre"/>, if that has been set). This does not yet
##  update the Hermite normal forms describing the lattice(s) of found
##  characters, see <Ref Func="UpdateHNFCCTable"/>.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> ind := InducedFromAllMaximalCyclicSubgroups(G);;
##  gap> CCT := CCTable(G);;
##  gap> ImportToCCTable(CCT, ind);
##  gap> UpdateHNFCCTable(CCT);
##  0
##  gap> HasFullRankCCTable(CCT);
##  true
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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

##  <#GAPDoc Label="HasFullRankCCTable">
##  <ManSection>
##  <Func Name="HasFullRankCCTable" Arg="CCT"/>
##  <Returns><K>true</K> or <K>false</K></Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object. This function
##  returns <K>true</K> if the total number of characters currently
##  collected in the Hermite normal form data of <A>CCT</A> (see
##  <Ref Func="UpdateHNFCCTable"/>), together with the irreducible
##  characters already found, equals the number of conjugacy classes of
##  the underlying group, that is if the lattice of characters found so
##  far already has full rank (the index in the full lattice of
##  generalized characters is finite).
##  <P/>
##  For example, the induced characters from all (maximal) cyclic 
##  subgroups always span a lattice of full rank, see the example
##  for <Ref Func="ImportToCCTable"/>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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

##  <#GAPDoc Label="UpdateHNFCCTable">
##  <ManSection>
##  <Func Name="UpdateHNFCCTable" Arg="CCT"/>
##  <Returns>a non-negative integer</Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object. This function
##  incorporates the generalized characters recently imported via
##  <Ref Func="ImportEncodedToCCTable"/> (or
##  <Ref Func="ImportToCCTable"/>) into the Hermite normal form basis
##  (or bases, in case of a splitting centre, see
##  <Ref Oper="SplitByCentre"/>) of the lattice of generalized characters
##  of <A>CCT</A> found so far, using <Ref Func="AddVectorToHNF"/>.
##  <P/>
##  If <Ref Func="HasFullRankCCTable"/> is <K>true</K> for <A>CCT</A>, the
##  return value is the index by which the lattice found so far has
##  shrunk (that is, the product of all indices returned by the
##  individual calls to <Ref Func="AddVectorToHNF"/>); otherwise the
##  Hermite normal forms are simply recomputed from scratch and <M>0</M>
##  is returned.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
        r.hnf := HermiteIntMat(Concatenation(r.hnf, r.new));
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

##  <#GAPDoc Label="ImportInducedFromAllMaximalCyclicToCCTable">
##  <ManSection>
##  <Func Name="ImportInducedFromAllMaximalCyclicToCCTable" Arg="CCT"/>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object of a group
##  <M>G</M>. Unless this has already been done (recorded in a component
##  of <A>CCT</A>), this function computes the characters of <M>G</M>
##  induced from all maximal cyclic subgroups of <M>G</M> (via
##  <Ref Func="InducedFromAllMaximalCyclicSubgroups"/>), imports them into
##  <A>CCT</A>, and updates its Hermite normal form data. It also computes
##  and stores, for each part of the (possibly split) lattice, the index
##  of the resulting lattice of generalized characters in the full
##  lattice of generalized characters, using that this index is only
##  divisible by primes <M>p</M> for which the Sylow <M>p</M>-subgroups of
##  <M>G</M> are not cyclic. The algorithm makes use of <Ref
##  BookName="EDIM" Func="ElementaryDivisorsPPartRk"/>.
##  <Example>
##  gap> G := MathieuGroup(24);;
##  gap> CCT := CCTable(G);;
##  gap> ImportInducedFromAllMaximalCyclicToCCTable(CCT);
##  gap> FindIndexCCTable(CCT);
##  4718592
##  gap> StringCollectedFactors(FindIndexCCTable(CCT));
##  "2^19 3^2"
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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

##  <#GAPDoc Label="FindIrreduciblesInFullLattices">
##  <ManSection>
##  <Func Name="FindIrreduciblesInFullLattices" Arg="CCT"/>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object. 
##  For every orthogonal subspace in the HNF data of <A>CCT</A>
##  which contains an integer basis of the corresponding sublattice
##  this function computes the irreducible characters in that
##  sublattice using a variant of the LLL algorithm (see
##  <Ref Func="LLLTransformUnimodularGram"/>). The irreducible
##  characters are then moved into the list of known irreducibles
##  (<C>CCT!.irr</C>) and this part of the HNF data is cleared.
##  If <Ref Oper="SplitByCentre"/> was used, the function also
##  adds Galois conjugates of the found irreducibles.
##  <P/>
##  See <Ref Func="FindIndexCCTable"/> for an example.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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

##  <#GAPDoc Label="FindIndexCCTable">
##  <ManSection>
##  <Func Name="FindIndexCCTable" Arg="CCT"/>
##  <Returns>a positive integer, or <K>fail</K></Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object. 
##  If <C>HasFullRankCCTable(<A>CCT</A>) = </C><K>true</K>
##  this function returns the index of the lattice spanned
##  by the class functions stored in <A>CCT</A> in the full
##  lattice spanned by the irreducible characters of the 
##  underlying group. Otherwise, <K>fail</K> is returned.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> CCT := CCTable(G);;
##  gap> ImportInducedFromAllMaximalCyclicToCCTable(CCT);
##  gap> FindIndexCCTable(CCT);
##  2
##  gap> ImportToCCTable(CCT, SmallPowerMapCharacters(G));
##  gap> UpdateHNFCCTable(CCT);
##  2
##  gap> FindIrreduciblesInFullLattices(CCT);
##  gap> CCT!.irr;
##  [ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ],
##    [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ],
##    [ 5, 1, -1, 0, 0, 0, 0 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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


##  <#GAPDoc Label="IrrCCTableHNF">
##  <ManSection>
##  <Func Name="IrrCCTableHNF" Arg="CCT"/>
##  <Returns>a list of irreducible characters, or <K>fail</K></Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object of a group
##  <M>G</M>. This function implements an induce-reduce algorithm that
##  computes and returns the list of irreducible characters of <M>G</M>,
##  and is installed as the default method for <Ref BookName="Reference"
##  Oper="Irr"/> for <Ref Filt="IsCCTable"/> objects.
##  <P/>
##  It successively imports into <A>CCT</A> (via
##  <Ref Func="ImportToCCTable"/> and <Ref Func="UpdateHNFCCTable"/>) the
##  characters induced from all maximal cyclic subgroups (via
##  <Ref Func="ImportInducedFromAllMaximalCyclicToCCTable"/>), the trivial
##  and <Ref Attr="NaturalCharacters"/> of <M>G</M>, cheap generalized
##  characters obtained from power maps (via
##  <Ref Func="SmallPowerMapCharacters"/>), and, if still needed, the
##  characters induced from the maximal non-cyclic elementary subgroups of
##  <M>G</M> (via <Ref Attr="MaximalNonCyclicElementarySubgroups"/> and
##  <Ref Func="InductionDataFromElementaryCCTable"/>), stopping as soon as
##  <Ref Func="FindIndexCCTable"/> returns <M>1</M>. It then calls
##  <Ref Func="FindIrreduciblesInFullLattices"/> to extract the
##  irreducible characters from the completed lattice. 
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> CCT := CCTable(G);;
##  gap> IrrCCTableHNF(CCT);
##  [ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ],
##    [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ],
##    [ 5, 1, -1, 0, 0, 0, 0 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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


##  <#GAPDoc Label="AddVectorToHNF">
##  <ManSection>
##  <Func Name="AddVectorToHNF" Arg="hnf, piv, v"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  Here <A>hnf</A> is an integer matrix in Hermite normal form, already
##  of the (full) rank of the ambient lattice, <A>piv</A> is the list of
##  its pivot column positions, and <A>v</A> is a further integer vector
##  in the rational span of the rows of <A>hnf</A>. This function changes
##  <A>hnf</A> in place to a Hermite normal form of the lattice generated
##  by the old rows of <A>hnf</A> together with <A>v</A> (which, since the
##  rank does not change, still has the same number of rows), and returns
##  the index of the old lattice of <A>hnf</A> in this new lattice (which
##  is <M>1</M> if <A>v</A> was already contained in the old lattice).
##  This is used by <Ref Func="UpdateHNFCCTable"/>.
##  <Example>
##  gap> hnf := [ [ 1, 0, 1, 478, -2, -649 ], [ 0, 1, 1, 362, 2, -492 ],
##  > [ 0, 0, 0, 546, 0, -742 ] ];;
##  gap> piv := [1,2,4];;
##  gap> v := [3, 7, 1, 6, 0, -1];;
##  gap> AddVectorToHNF(hnf, piv, v);
##  39
##  gap> hnf;
##  [ [ 1, 0, 1, 2, -1090, 779 ], [ 0, 1, 1, 12, -798, 558 ], 
##    [ 0, 0, 0, 14, 32, -42 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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

