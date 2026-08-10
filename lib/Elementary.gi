###########################################################################
##  Elementary.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  Functions to parameterize the maximal non-cyclic p-elementary subgroups
##  C x P of a group G up to conjugacy.
##  
##  This file provides functions 
##     MaximalNonCyclicElementarySubgroups(G)
##     InducedFromElementary(G, i, p[, "linear"/"nonlinear")
##  

##  <#GAPDoc Label="MaximalNonCyclicElementarySubgroups">
##  <ManSection>
##  <Attr Name="MaximalNonCyclicElementarySubgroups" Arg="G"/>
##  <Returns>a list of pairs of positive integers</Returns>
##  <Description>
##  This function returns a list
##  of pairs <C>[ i, p ]</C>, where <C>i</C> is the number of a conjugacy
##  class in <A>G</A> and <C>p</C> is a prime. To each such pair we consider 
##  a subgroup <M>\langle{x}\rangle \times P</M>, where <M>x</M> is a 
##  representative of class <A>i</A> and <M>P</M> is a Sylow-<M>p</M>-subgroup
##  of the centralizer of <M>x</M>. These subgroups form, up to conjugacy in 
##  <A>G</A>, the non-cyclic maximal elementary subgroups of <A>G</A>.
##  <P/>
##  Brauer's theorem on the characterization of characters of <A>G</A> says
##  that the full lattice of generalized characters of <A>G</A> (that is
##  all integer linear combinations of irreducible characters) is spanned by
##  the characters induced from the maximal elementary subgroups of
##  <A>G</A>, that is the maximal cyclic subgroups (see <Ref
##  Attr="MaximalCyclics"/>) and the subgroups descibed by this function. See
##  <Cite Key="Isaacs" Where="Chapter 8"/> for more details.
##  <Example>
##  gap> G := SL(4,2);;
##  gap> MaximalNonCyclicElementarySubgroups(G);
##  [ [ 1, 3 ], [ 1, 2 ], [ 6, 2 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  returns list of pairs [i, p] encoding the elementary subgroups
##  <x> x P where x is an element from class i and P is a Sylow-p-subgroup
##  of the centralizer of x in G (up to conjugacy in G)
InstallMethod(MaximalNonCyclicElementarySubgroups, ["IsGroup"], function(G)
  local cls, ords, sords, sz, fac, cenords, faccen, facnoncyc, pnoncyc, pms, ratcl, 
        rord, nrat, res, notneeded, o, ncl, ps, f, op, poss, i, p, j;
  cls := ConjugacyClasses(G);
  ords := OrdersClassRepresentatives(G);
  sords := Set(ords);
  sz := Size(G);
  fac := Collected(Factors(sz));
  cenords := List(cls, c-> sz/Size(c));
  faccen := List(cenords, k-> Collected(Factors(k)));
  
  # prime divisors p of |G| with non-cyclic Sylow-p-subgroups:
  facnoncyc := Filtered(fac, a-> not a[1]^a[2] in sords);
  pnoncyc := List(facnoncyc, a-> a[1]);

  pms := PowerMapsOfAllClasses(G);
  # rational classes by positions, sort by decreasing element order
  ratcl := ShallowCopy(RationalClassSets(G));
  rord := List(ratcl, a-> ords[a[1]]);
  SortParallel(rord, ratcl, {x,y}-> y<x);
  nrat := Length(ratcl);
  
  res := [];
  notneeded := [];
  for i in [1..nrat] do
    o := rord[i];
    ncl := ratcl[i][1];
    # p with gcd(o, p) = 1
    ps := Filtered(pnoncyc, p-> o mod p <> 0 and not [i,p] in notneeded);
    for p in ps do
      f := Filtered(faccen[ncl], a-> a[1]=p);
      if Length(f) > 0 then
        # check if Sylow-p in centralizer is not cyclic
        # (then there would be an element of the order of
        # the elementary subgroup in the preimage of some
        # power map)
        op := o*f[1][1]^f[1][2];
        poss := Positions(ords, op);
        if not ForAny(poss, j-> ncl in pms[j]) then
          Add(res, [i, p]);
          # throw out smaller groups with same p-part
          # and subgroup of the cyclic part
          for j in Difference(pms[ncl], ratcl[i]) do
            if f[1] in faccen[j] then
              Add(notneeded, [First([1..nrat], m-> j in ratcl[m]), p]);
            fi;
          od;
        fi;
      fi;
    od;
  od;
  # for result translate number of rational class in number of class
  # 
  # ordering is with growing order cyclic groups
  # (in many examples we have seen that these are needed
  # anyway in the InduceRestrict algorithm, and they often
  # push down the Gram determinant significantly)
  return List(Reversed(res), a-> [ratcl[a[1]][1], a[2]]);
end);

##  <#GAPDoc Label="InducedFromElementary">
##  <ManSection>
##  <Func Name="InducedFromElementary" Arg="G, i, p[, opts...]"/>
##  <Func Name="InducedFromElementary" Arg="CCT, i, p[, opts...]"/>
##  <Returns>a list of row vectors of cyclotomic numbers, or an integer</Returns>
##  <Description>
##  In the first form <A>G</A> is a group, in the second form
##  <A>CCT</A> is an <Ref Filt="IsCCTable"/> object of a group <A>G</A>. Let
##  <A>i</A> be an integer and <A>p</A> be a prime, such that <M>x</M> 
##  contained the <A>i</A>-th conjugacy class of <M>G</M> has order
##  not divisible by <A>p</A>. We consider the <A>p</A>-elementary subgroup
##  <M>E = \langle{x}\rangle \times S</M> where <M>S</M> is a 
##  Sylow-<A>p</A>-subgroup of the centralizer of <M>x</M>.
##  <P/>
##  This function returns the pairwise distinct characters of <M>G</M>
##  induced from the irreducible characters of <M>E</M> (as lists of 
##  values, in the order of <C>ConjugacyClasses(<A>G</A>)</C>).
##  <P/>
##  The following further optional arguments may be given, in any order:
##  <List>
##  <Mark><C>"linear"</C></Mark>
##  <Item>only the characters induced from the linear characters of
##  <M>E</M> are computed</Item>
##  <Mark><C>"nonlinear"</C></Mark>
##  <Item>only the characters induced from the non-linear irreducible
##  characters of <M>E</M> are computed</Item>
##  <Mark>a positive integer <A>max</A></Mark>
##  <Item>if the number of conjugacy classes of <M>E</M> 
##  is larger than <A>max</A>, no characters are computed and this
##  number is returned instead (this can be used to skip elementary
##  subgroups that would be too expensive to handle)</Item>
##  </List>
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> InducedFromElementary(G, 1, 2);
##  [ [ 15, -1, 0, 0, 0 ], [ 15, 3, 0, 0, 0 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  computes the induced irreducible characters from an elementary subgroup
##  (given by [i, p] as above) to G
##  with optional argument "linear" only the linear characters are induced
##  with optional argument "nonlinear" only the nonlinear characters are induced
##  with an integer max in optional arguments the function returns only the
##       number of conjugacy classes of the elementary subgroup if
##       this number is larger than max
##
##  characters are returned as list of values in Ordering of ConjugacyClasses(G)
BindGlobal("InducedFromElementary", function(GorCCT, i, p, opts...)
  local G, ut, max, scen, cls, ncl, cl, x, o, cen, s, ss, t, scl, sscl, 
        fus, pms, lt, res, c, m, efus, e, j, l, k, ch, a;
  if IsGroup(GorCCT) then
    G := GorCCT;
    ut := CCTable(G);
  elif IsCCTable(GorCCT) then
    ut := GorCCT;
    G := UnderlyingGroup(ut);
  else
    Error("InducedFromElementary: First argument must be group or CCTable");
    return;
  fi;
  k := Filtered(opts, IsInt);
  if Length(k) > 0 then
    max := k[1];
  else
    max := false;
  fi;

  scen := SizesCentralizers(ut);
  cls := ConjugacyClasses(ut);
  ncl := Length(cls);

  # if arg is CCTable we store only values on reps of rational classes
  cl := cls[i];
  # generator of cyclic part
  x := Representative(cl);
  o := Order(x);
  # centralizer of representative
  cen := StabilizerOfExternalSet(cl);
  # p-part (and remove it from attribute)
  s := SylowSubgroup(cen, p);
  Remove(ComputedSylowSubgroups(cen));
  Remove(ComputedSylowSubgroups(cen));
  IsPGroup(s);
  ss := Size(s);
  if IsInt(max) and NrConjugacyClasses(s)*o > max then
    return NrConjugacyClasses(s)*o;
  fi;
  if "linear" in opts then
    t := LinearCharacters(s);
  else
    # in which cases it may be sensible to move to PcGroup?
    t := IrrBaumClausen(s);
    if "nonlinear" in opts then
      t := Filtered(t, ch-> Degree(ch) > 1);
    fi;
  fi;
  scl := ConjugacyClasses(s);
  sscl := List(scl, Size);
  # fusion of classes of x y with y reps of classes of s
  fus := List(scl, cl-> PositionConjugacyClass(G, x*Representative(cl)));

  # the rest we get from power maps
  pms := PowerMapsOfAllClasses(ut);

  # we use the character table of <x> x s without writing it down
  lt := Length(t);
  res := List([1..lt*o], i-> 0*[1..ncl]);
  c := E(o);
  for e in [0..o-1] do
    # m such that (x y)^m = x^e y
    m := ChineseRem([o, ss], [e, 1]);
    efus := List(fus, i-> pms[i][(m mod Length(pms[i]))+1]);
    for j in [1..Length(fus)] do
      for l in [0..o-1] do
        for k in [1..lt] do
          a := efus[j];
          res[l*lt+k][a] := res[l*lt+k][a] + c^(e*l)*t[k][j]*sscl[j];
        od;
      od;
    od;
  od;
  # some induced characters can be the same
  res := Set(res);
  # finally the factor coming from class lengths in G
  for j in [1..ncl] do
    c := scen[j]/ss/o;
    for ch in res do
      if not ch[j] = 0 then
        ch[j] := c*ch[j];
      fi;
    od;
  od;
  return res;
end);

##  <#GAPDoc Label="FusionElementaryCCTable">
##  <ManSection>
##  <Func Name="FusionElementaryCCTable" Arg="CCT, i, p"/>
##  <Returns>a list of length 2</Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object of a group
##  <M>G</M>. The arguments <A>i</A> and <A>p</A> decribe an elementary
##  subgroup <M>E = \langle{x}\rangle \times S</M>, as explained in <Ref
##  Func="InducedFromElementary"/>. 
##  <P/>
##  This function computes the fusion of the conjugacy classes of <M>E</M>
##  into the classes of <M>G</M>. The implementation tries to avoid
##  class identifications and uses the power maps. The result is a list
##  <C>[ fus, needed ]</C>. Here <C>fus</C> is a list with one entry of
##  form <P/><C>[ j, [ e1, k1, k2, ... ], [ e2, ... ], ... ]</C><P/> 
##  for every class <A>j</A> of <M>G</M> representing a rational class (see
##  <Ref Attr="RationalClassSets"/>) that occurs in the image of the fusion.
##  Here <C>e1, e2, ...</C> are exponents and they are followed by numbers
##  <C>k</C> such that the classes of x^ei y with y in class k of
##  S fuse into class j of G.
##  <P/>
##  The second entry <C>needed</C> is the set of numbers of classes of
##  <M>S</M> occurring in <C>fus</C>.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> FusionElementaryCCTable(CCTable(G), 1,2);
##  [ [ [ 1, [ 0, 1 ] ], [ 2, [ 0, 2, 3, 4 ] ] ], [ 1, 2, 3, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
# Fusion of elementary subgroup <x> x S (x in class i, S p-Sylow in
# centralizer of x): returns pair of lists [fus, needed] where fus is list of
# lists of form
#     [j, [e1, ...], [e2, ...] ...]
# where j is number of class in G in the image, e1, e2,... exponents,
# followed by numbers k such that the classes of x^e1 y with y in class k of
# S fuse into class j of G.
# Only classes j which represent rational classes of G are considered.
# And the second entry 'needed' contains the numbers of classes of S
# occuring in fus.
BindGlobal("FusionElementaryCCTable", function(CCT, i, p)
  local G, cls, ncl, ords, cen, s, ssz, x, o, pms, rci, todo, scl, sclr, scll, 
        oscl, e, k, excl, ko, kk, max, n, ncls, els, ngen, gens, perm, orbs, 
        orb, same, fus1, z, fus, m, efus, img, poss, needed, pp, 
        a, b, y, g, r, j;
  G := UnderlyingGroup(CCT);
  cls := ConjugacyClasses(CCT);
  ncl := NrConjugacyClasses(CCT);
  ords := OrdersClassRepresentatives(CCT);
  # p-group (it is not needed later, we remove the stored attribute)
  cen := StabilizerOfExternalSet(cls[i]);
  s := SylowSubgroup(cen, p);
  ssz := Size(s);
  # generator of cyclic group
  x := Representative(cls[i]);
  o := ords[i];
  pms := PowerMapsOfAllClasses(CCT);
  rci := RationalClassesInfo(CCT);
  # restrict information to representatives of rational classes
  todo := BlistList([1..ncl], List(rci, a-> a.classes[1]));
  # classes of s
  IsSupersolvableGroup(s);
  scl := ConjugacyClasses(s);
  sclr := List(scl, Representative);
  scll := List(scl, Size);
  oscl := OrdersClassRepresentatives(s);

  # if i<>1 we may be able to exclude some classes during identification
  e := Exponent(s);
  k := 1;
  excl := [];
  while k <= e do
    # for y in s of order k, the element 
    # x y has order k*|x| and its k-th power
    # is in the class of x^k (which we know from pms)
    ko := k*o;
    if o > 1 then
      kk := pms[i][(k mod o) + 1];
      excl[k] := Filtered([1..ncl], j-> ords[j] = ko and pms[j][k+1] <> kk);
    else
      excl[k] := [];
    fi;
    k := k*p;
  od;
  
  # compute orbit of normalizer in cen on classes of s to reduce
  # conjugacy tests
  if IsBound(CCT!.maxelmlist) then
    max := CCT!.maxelmlist;
  else
    max := 1000000;
  fi;
  if ssz <= max then
    n := Normalizer(cen, s);
    if Size(n) > ssz then
      ncls := [];
      els := [];
      for i in [1..Length(scl)] do
        for y in scl[i] do
          Add(els, y);
          Add(ncls, i);
        od;
      od;
      SortParallel(els, ncls);
      ngen := GeneratorsOfGroup(n);
      gens := [];
      for g in ngen do
        perm := [];
        for r in sclr do
          Add(perm, ncls[PositionSorted(els, r^g)]);
        od;
        Add(gens, PermList(perm));
      od;
      els := 0;
      orbs := List(Orbits(Group(gens), [1..Length(scl)]), Set);
      same := [];
      for orb in orbs do
        for i in [2..Length(orb)] do
          same[orb[i]] := orb[1];
        od;
      od;
    else
      same := [];
    fi;
  else
    same := [];
  fi;

  # fusion of classes of x y with y in reps of classes of s
  fus1 := [];
  for j in [1..Length(scl)] do
    if IsBound(same[j]) then
      Add(fus1, fus1[same[j]]);
    else
      z := x*Representative(scl[j]);
      Add(fus1, PositionConjugacyClass(G, z, excl[oscl[j]]));
    fi;
  od;

  # the rest we get from power maps
  # (e+1)-th entry is fusion of x^e y, y reps of classes of s
  fus := [];
  for e in [0..o-1] do
    # m such that (x y)^m = x^e y
    if e = 1 then
      Add(fus, fus1);
    else
      m := ChineseRem([o, ssz], [e, 1]);
      efus := List(fus1, i-> pms[i][(m mod Length(pms[i]))+1]);
      Add(fus, efus);
    fi;
  od;
  
  # collect information for representing classes in rational classes
  img := Filtered(Set(Flat(fus)), j-> todo[j]);
  poss := [];
  needed := [];
  for j in img do
    pp := [j];
    for k in [0..o-1] do
      a := [k];
      b := Positions(fus[k+1], j);
      Append(a, b);
      if Length(a) > 1 then
        Add(pp, a);
        Append(needed, b);
      fi;
    od;
    Add(poss, pp);
  od;
  needed := Set(needed);

  return [poss, needed];
end);

##  <#GAPDoc Label="InductionDataFromElementaryCCTable">
##  <ManSection>
##  <Func Name="InductionDataFromElementaryCCTable" Arg="CCT, i, p"/>
##  <Returns>a record</Returns>
##  <Description>
##  Let <A>CCT</A>, <A>i</A> and <A>p</A> be as for
##  <Ref Func="FusionElementaryCCTable"/>, describing a <M>p</M>-elementary
##  subgroup <M>E = \langle{x}\rangle \times S</M> of the group <M>G</M>
##  underlying <A>CCT</A>. This function provides an alternative, more
##  memory efficient way to compute the characters of <M>G</M> induced
##  from the irreducible characters of <M>E</M>
##  than <Ref Func="InducedFromElementary"/>. This is useful in particular
##  when <M>S</M> has a large number of conjugacy classes.
##  <P/>
##  The irreducible characters of the <A>p</A>-group
##  <M>S</M> are described via <C>BaumClausenInfo</C> (see
##  <Ref BookName="Reference" Attr="IrrBaumClausen"/>), and the record
##  returned by this function
##  contains a component <C>next</C>, a function without arguments. 
##  Each call of <C>.next()</C> returns <M>|x|</M> induced characters from
##  <M>E</M>; or <K>fail</K> when there are no more such characters.
##  <P/>
##  In contrast to <Ref Func="InducedFromElementary"/>, this function does
##  not detect and remove induced characters occurring several times.
##  <Example>
##  gap> G := SymmetricGroup(5);;
##  gap> ind := InductionDataFromElementaryCCTable(CCTable(G),1,2);;
##  gap> ind.next();
##  [ [ 15, 3, 3, 0, 1, 0, 0 ] ]
##  gap> ind.next();
##  [ [ 15, 3, -1, 0, -1, 0, 0 ] ]
##  gap> ind.next();
##  [ [ 15, -3, 3, 0, -1, 0, 0 ] ]
##  gap> ind.next();
##  [ [ 15, -3, -1, 0, 1, 0, 0 ] ]
##  gap> ind.next();
##  [ [ 30, 0, -2, 0, 0, 0, 0 ] ]
##  gap> ind.next();
##  fail
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
# Here we produce data with an iteration function which produces
# |x| induced irreducible characters at a time. We use 'BaumClausenInfo' and
# then compute character values as in 'IrrBaumClausen' later on the fly.
# This way we can handle elementary subgroups with a huge number of classes.
# The disadvantage is that we sometimes have some extra work because we do not
# detect if several induced characters are the same.
# On the other hand, for the last needed p-elementary subgroup in the
# induce-reduce process the missing p-part of the lattice index is
# often found after only a few induced characters.
BindGlobal("InductionDataFromElementaryCCTable", function(CCT, i, p)
  local fus, needed, G, sz, cls, ncl, szcen, ords, o, st, s, ssz, scls, szscls, 
        lg, bc, pcgs, exp, q, gcdq, exps, cr, eL, eE, j, next;

  # first get the fusion data
  fus := FusionElementaryCCTable(CCT, i, p);
  needed := fus[2];
  fus := fus[1];
  
  # we need class lengths of G and Sylow P
  G := UnderlyingGroup(CCT);
  sz := Size(CCT);
  cls := ConjugacyClasses(CCT);
  ncl := NrConjugacyClasses(CCT);
  szcen := SizesCentralizers(CCT);
  ords := OrdersClassRepresentatives(CCT);
  o := ords[i];
  # p-group
  st := StabilizerOfExternalSet(cls[i]);
  s := SylowSubgroup(st, p);
  Remove(ComputedSylowSubgroups(st));
  Remove(ComputedSylowSubgroups(st));
  ssz := Size(s);
  scls := ConjugacyClasses(s);
  szscls := List(scls, Size);

  # irreducibles of s described by Baum-Clausen
  # (representations as monomial matrices on pc-generators)
  bc := ShallowCopy(BaumClausenInfo(s));
  # simplify
  bc.nonlin := List(bc.nonlin, a-> List(a, b-> [b.diag, b.perm]));
  # collect relevant data in bc
  pcgs := bc.pcgs;
  exp := bc.exponent;
  q := Gcd(exp, Length(bc.lin));
  gcdq := exp/q;

  exps := List(scls, c-> ExponentsOfPcElement(pcgs, Representative(c)));
  cr := SortedList(exps{needed});
  Unbind(bc.pcgs);
  Unbind(bc.kernel);
  Unbind(bc.exponent);
  lg := Length(pcgs);
  eL := [1];
  eE := E(o);
  for j in [1..o-1] do
    Add(eL, eL[j]*eE);
  od;
  bc.pos := 1;

  # and here is a function 'next' to iterate over chi in Irr(s)
  # which returns the induced characters of {chi x zeta, zeta in Irr(<x>)}
  next := function()
    local pos, lin, rep, mul, gcd, m, deg, id, trace, l, v,
          j, perm, diag, e, vals, res, k, sums, b, f, a, i, jj, bt, t;
    # first linear characters
    pos := bc.pos;
    lin := IsBound(bc.lin);
    if lin then
      rep := bc.lin[pos];
      for a in cr do
        Add(a, (a*rep)/gcdq mod q + 1);
      od;
      if pos = Length(bc.lin) then
        bc.pos := 1;
        Unbind(bc.lin);
      else
        bc.pos := pos+1;
      fi;
    elif pos <= Length(bc.nonlin) then
      mul := function(a, b)
        local x;
        x := [[],b[2]{a[2]}];
        x[1]{b[2]} := b[1]{b[2]} + a[1];
        return x;
      end;
      rep := bc.nonlin[pos];
      gcd:= GcdInt(Gcd(List(rep, x-> Gcd(x[1]))), exp);
      m := exp/gcd;
      deg := Length(rep[1][2]);
      id := [0*[1..deg], [1..deg]];
      trace := 0*[1..m];
      trace[1] := deg;
      Add(cr[1], trace);
      l := List([1..lg], i-> id);
      # We go through sorted list of exponents and reuse
      # partial product from previous representative.
      for i in [2..Length(cr)] do
        j := 1;
        while cr[i-1][j] = cr[i][j] do
          j := j+1;
        od;
        for k in [cr[i-1][j]+1..cr[i][j]] do
          l[j] := mul(l[j], rep[j]);
        od;
        for jj in [j+1..lg] do
          l[jj] := l[jj-1];
          for k in [1..cr[i][jj]] do
            l[jj] := mul(l[jj], rep[jj]);
          od;
        od;
        # Compute the character value.
        trace:= 0*[1..m];
        perm := l[lg][2];
        diag := l[lg][1];
        for k in [1..deg] do
          if perm[k] = k then
            e := (diag[k] / gcd) mod m;
            trace[e+1]:= trace[e+1] + 1;
          fi;
        od;
        # We append the character values to the exponents lists
        # and remove them (in the right order) after this loop.
        Add(cr[i], trace);
      od;
      bc.pos := pos+1;
    else
      return fail;
    fi;

    # now we extract the values on needed classes (coefficient lists in
    # powers of some E(?))
    vals := [];
    for j in needed do
      vals[j] := Remove(exps[j]);
    od;
    bc.vals:=vals;

    # now we compute the fusion on reps of rational classes of G
    res := List([1..o], j-> 0*[1..ncl]);
    for a in fus do
      k := a[1];
      sums := [];
      for j in [2..Length(a)] do
        b := a[j];
        if lin then
          v := 0*[1..q];
          for t in [2..Length(b)] do
            bt := b[t];
            m := vals[bt];
            v[m] := v[m] + szscls[bt];
          od;
        else
          bt := b[2];
          v := szscls[bt] * vals[bt];
          for t in [3..Length(b)] do
            bt := b[t];
            v := v + szscls[bt] * vals[bt];
          od;
        fi;
        Add(sums, CycList(v));
      od;
      f := szcen[k]/o/ssz;
      for j in [0..o-1] do
        res[j+1][k] := f*(List([2..Length(a)], l-> eL[a[l][1]*j mod o + 1])*sums);
      od;
    od;
    return EncodeForCCTable(CCT, res);
  end;
  bc.next := next;
  return bc;
end);

##  # temporary test function, should behave like 
##  #     EncodeForCCTable(CCT, InducedFromElementary(CCT, i, p))
##  fu:=function(CCT,i,p)
##    local bc, next, res, a;
##    bc := InductionDataFromElementaryCCTable(CCT,i,p);
##    next := bc.next;
##    res := [];
##    a := next();
##    while a <> fail do
##      Append(res,a);
##      a := next();
##    od;
##    return res;
##  end;

