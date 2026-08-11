###########################################################################
##  PositionConjugacyClass.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  This file contains functions to find the number of the conjugacy class
##  of an element in a group G. 
##  
##  ConjugacyClassInvariants(G) produces a record r with a recursive structure 
##      r.tree
##  This is a list with 4 entries:
##      poss: a list of class positions
##      f: a function with arguments r and a group element
##         that returns a class invariant that can distinguish classes poss
##      res: the sorted list of results of f for representatives of classes poss
##      ts: a list of the same length as res, if res[i] is an invariant of
##          a unique class j in poss then ts[i] = j; otherwise ts[i] is again
##          a tree for the classes with invariant res[i].
##  
##  
##  This structure is used by PositionConjugacyClass(G, x) to identify the
##  position of the conjugacy class of x by computing class invariants until the
##  position is found.
##
##  An optional second argument of ConjugacyClassInvariants can be a list 
##  of functions of form g(r, tree)  that extend a tree that so far 
##  only contains the list poss.  There are default functions for permutation
##  and matrix groups.
##  
##  Note that a similar scheme could also be used for identifying other
##  types of equivalence classes.
##  
##  In the result of ConjugacyClassInvariants we also bind the group 
##  as r.G, classes as r.classes and  class reps as r.reps in 
##  addition to the recursive r.tree
##  (these can be used by the functions computing invariants).
##  Furthermore there is always a component .exclude, a list of class
##  positions, when PositionConjugacyClass is called, the functions that
##  compute invariants can use this as a hint, that the given element
##  is not contained in a class in r.exclude.
##  

# utility: refine the tree with function fu
CCInvFuncs.refine := function(r, tree, fu)
  local invs, s, ts, pos, a;
  invs := List(r.reps{tree[1]}, x-> fu(r, x));
  s := Set(invs);
  if Length(s) > 1 then
    Add(tree, fu);
    Add(tree, s);
    ts := [];
    for a in s do
      pos := Positions(invs, a);
      if Length(pos) = 1 then
        Add(ts, tree[1][pos[1]]);
      else
        Add(ts, [tree[1]{pos}]);
      fi;
    od;
    Add(tree, ts);
  fi;
end;

# In many practical cases it is likely that conjugacy tests are
# made with class representatives. Here is a cheap test to recognize such
# cases.
CCInvFuncs.NoticeReps := function(r, tree)
  local s, len, l, fu;
  if tree[1] = [1..Length(r.classes)] then
    s := ShallowCopy(r.reps);
    len := Length(s);
    l := [1..len];
    SortParallel(s, l);
    fu := function(r, x)
      local pos;
      pos := PositionSorted(s, x);
      if not IsBound(s[pos]) or s[pos] <> x then
        return fail;
      else
        return l[pos];
      fi;
    end;
    tree[2] := fu;
    tree[3] := [1..len];
    tree[4] := [1..len];
    # of course, we can be lucky above to identify the class, but fu
    # does not yield a class invariant, in case of 'fail' we can still
    # have any class:
    Add(tree[3], fail);
    Add(tree[4], [[1..len]]);
  fi;
end;

# fallback: try IsConjugate with all classes  but the last
CCInvFuncs.ConjTest := function(r, tree)
  local fu;
  fu := function(r, x)
    local l, i;
    if Length(r.exclude) > 0 then
      l := Filtered(tree[1], i-> not i in r.exclude);
    else
      l := tree[1];
    fi;
    for i in [1..Length(l)-1] do
      if x = r.reps[l[i]] or x in r.classes[l[i]] then
        return l[i];
      fi;
    od;
    return l[Length(l)];
  end;
  Add(tree, fu);
  Add(tree, Set(tree[1]));
  Add(tree, tree[3]);
end;

# use element order
# (note that for permutations/matrices computing the order
# needs the cycle structure/minimal polynomial, so that this 
# is only used in the fallback variant)
CCInvFuncs.Order := function(r, tree)
  local fu;
  fu := function(r, x)
    return Order(x);
  end;
  CCInvFuncs.refine(r, tree, fu);
end;

# use characteristic polynomial in matrix groups
CCInvFuncs.CharPol := function(r, tree)
  local fu;
  fu := function(r, x)
    return CharacteristicPolynomial(x);
  end;
  CCInvFuncs.refine(r, tree, fu);
end;

# use minimal polynomial in matrix groups
CCInvFuncs.MinPol := function(r, tree)
  local fu;
  fu := function(r, x)
    return MinimalPolynomial(x);
  end;
  CCInvFuncs.refine(r, tree, fu);
end;

# if "nofoma" package loaded use Frobenius normal form for matrix groups
CCInvFuncs.Frob := function(r, tree)
  local F, n, inSL, d, fu;
  F := FieldOfMatrixGroup(r.G);
  n := DimensionOfMatrixGroup(r.G);
  inSL := ForAll(GeneratorsOfGroup(r.G), x-> IsOne(DeterminantMat(x)));
  d := 1;
  if IsFinite(F) then
    d := Gcd(n, Size(F)-1);
  fi;
  if not IsBound(GAPInfo.PackagesLoaded.nofoma) then
    fu := ReturnTrue;
  elif not IsFinite(F) or not inSL or d = 1 then
    fu := function(r, x)
      return FrobeniusNormalForm(x)[1];
    end;
  else
    fu := function(r, x)
      local fr, g, e, pl;
      fr := FrobeniusNormalForm(x);
      g := d;
      for pl in fr[1] do
        if g = 1 then
          break;
        fi;
        e := List(Collected(Factors(pl)), a-> a[2]);
        g := Gcd(g, Gcd(e));
      od;
      if g = 1 then
        return [fr[1]];
      else
        return [fr[1], LogFFE(DeterminantMat(fr[2]), Z(Size(F))) mod g];
      fi;
    end;
  fi;
  CCInvFuncs.refine(r, tree, fu);
end;

# for permutation groups: cycle structures on orbits of points
CCInvFuncs.CycStruct := function(r, tree)
  local o, fu;
  # these are the orbits on moved points
  o := Orbits(r.G);
  if Length(o) = 1 then
    fu := function(r, x)
      return CycleStructurePerm(x);
    end;
  else
    fu := function(r, x)
      return List(o, a-> CycleStructurePerm(RestrictedPerm(x,a)));
    end;
  fi;
  CCInvFuncs.refine(r, tree, fu);
end;

##  <#GAPDoc Label="ConjugacyClassInvariants">
##  <ManSection>
##  <Func Name="ConjugacyClassInvariants" Arg="G[, funcs]"/>
##  <Returns>a record</Returns>
##  <Description>
##  Let <A>G</A> be a finite group. This function computes and returns a
##  record <M>r</M> that is used by <Ref Func="PositionConjugacyClass"/>
##  to quickly identify the conjugacy class of an element of <A>G</A>. The
##  result is cached in <C><A>G</A>!.ConjugacyClassInvariants</C>, so it is
##  computed only once.
##  <P/>
##  The record <M>r</M> has components <C>G</C>, <C>classes</C> (the
##  result of <Ref BookName="Reference"
##  Attr="ConjugacyClasses"/> for <A>G</A>), <C>reps</C> (their
##  representatives), and <C>tree</C>, a recursively built decision tree
##  used to distinguish the conjugacy classes of <A>G</A> by successively
##  computed class invariants (such as element order, cycle
##  structure, or characteristic and minimal polynomial for matrix
##  groups), falling back to explicit conjugacy tests if necessary.
##  <P/>
##  The optional argument <A>funcs</A>, if given, is a list of functions
##  <C>fu(r, tree)</C> used to (further) build up the tree, overriding the
##  default choices, which depend on whether <A>G</A> is a permutation
##  group, a matrix group, or neither. See <C>CCInvFuncs.CycStruct</C>
##  as an example of such a function.
##  <P/>
##  In the following example, the first function compares with the
##  stored class representatives; the second computes the cycle type
##  and the third is only relevant for 5-cycles and does one conjugacy
##  test against the representative of class 4.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> ConjugacyClassInvariants(G);
##  rec( G := Alt( [ 1 .. 5 ] ),
##    classes := [ ()^G, (1,2)(3,4)^G, (1,2,3)^G, (1,2,3,4,5)^G, (1,2,3,5,4)^G ],
##    reps := [ (), (1,2)(3,4), (1,2,3), (1,2,3,4,5), (1,2,3,5,4) ],
##    tree := [ [ 1 .. 5 ], function( r, x ) ... end, [ 1, 2, 3, 4, 5, fail ],
##        [ 1, 2, 3, 4, 5,
##            [ [ 1 .. 5 ], function( r, x ) ... end,
##                [ [  ], [ ,,, 1 ], [ , 1 ], [ 2 ] ],
##                [ 1, [ [ 4, 5 ], function( r, x ) ... end, [ 4, 5 ], [ 4, 5 ] ],
##                    3, 2 ] ] ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
BindGlobal("ConjugacyClassInvariants", function(G, args...)
  local r, funcs, tree, find;
  if IsBound(G!.ConjugacyClassInvariants) then
    return G!.ConjugacyClassInvariants;
  fi;
  r := rec(G := G);
  r.classes := ConjugacyClasses(G);
  r.reps := List(r.classes, Representative);
  r.tree := [[1..Length(r.reps)]];
  if Length(args) > 0 and IsList(args[1]) then
    funcs := ShallowCopy(args[1]);
    Add(funcs, CCInvFuncs.ConjTest);
  elif IsPermGroup(G) then
    funcs := [CCInvFuncs.NoticeReps, CCInvFuncs.CycStruct, CCInvFuncs.ConjTest];
  elif IsMatrixGroup(G) then
    funcs := [CCInvFuncs.NoticeReps, CCInvFuncs.CharPol, CCInvFuncs.MinPol, CCInvFuncs.Frob, CCInvFuncs.ConjTest];
  else
    funcs := [CCInvFuncs.NoticeReps, CCInvFuncs.Order, CCInvFuncs.ConjTest];
  fi;
  tree := r.tree;
  find := function(tree, funcs)
    local f2, a;
    funcs[1](r, tree);
    f2 := funcs{[2..Length(funcs)]};
    if Length(tree) = 1 then
      # funcs[1] did not distinguish any of the classes in tree[1]
      find(tree, f2);
    else
      for a in tree[4] do
        if IsList(a) then
          # recurse if still several classes possible
          find(a, f2);
        fi;
      od;
    fi;
  end;
  find(tree, funcs);
  G!.ConjugacyClassInvariants := r;
  return r;
end);

##  <#GAPDoc Label="PositionConjugacyClass">
##  <ManSection>
##  <Func Name="PositionConjugacyClass" Arg="G, x[, exclude]"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  Let <A>G</A> be a finite group and <A>x</A> an element of <A>G</A>.
##  This function returns the position of the conjugacy class of <A>x</A>
##  in the list <C>ConjugacyClasses(<A>G</A>)</C>. It
##  uses <Ref Func="ConjugacyClassInvariants"/> to identify the class by
##  computing class invariants of <A>x</A> until the class is uniquely
##  determined.
##  <P/>
##  If the optional argument <A>exclude</A> is given, it must be a list of
##  class positions which is guaranteed not to contain the class position
##  of the class of <A>x</A>. This information can sometimes help to 
##  speed up the identification.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> creps := List(ConjugacyClasses(G), Representative);;
##  gap> List(creps, x-> PositionConjugacyClass(G, x^Random(G)));
##  [ 1, 2, 3, 4, 5 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
# applying this is easy:
# optionally, a list of class indices can be given which can be excluded
# from the context of the application
BindGlobal("PositionConjugacyClass", function(G, x, exclude...)
  local r, tree, tr1, inv, pos;
  r := ConjugacyClassInvariants(G);
  if Length(exclude) > 0 then
    r.exclude := exclude[1];
  else
    r.exclude := [];
  fi;
  tree := r.tree;
  while IsList(tree) do
    if Length(r.exclude) > 0 then
      tr1 := List(tree[1], i-> not i in r.exclude);
      if Length(tr1) = 1 then
        return tr1[1];
      fi;
    fi;
    inv := tree[2](r, x);
    pos := PositionSorted(tree[3], inv);
    tree := tree[4][pos];
  od;
  return tree;
end);

