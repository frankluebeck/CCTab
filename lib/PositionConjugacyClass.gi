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
##  number of the conjugacy class of x by computing class invariants until the
##  number is found.
##
##  An optional second argument of ConjugacyClassInvariants can be a list 
##  of functions of form g(r, tree) ##  that extend a tree that so far 
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
    l := tree[1];
    for i in [1..Length(l)-1] do
      if not l[i] in r.exclude then
        if x = r.reps[l[i]] or x in r.classes[l[i]] then
          return l[i];
        fi;
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
        return fr[1];
      else
 Print("nontriv g ",g,"\n");       
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

BindGlobal("ConjugacyClassInvariants", function(G, args...)
  local r, funcs, tree, find;
  if IsBound(G!.ConjugacyClassInvariants) then
    return G!.ConjugacyClassInvariants;
  fi;
  r := rec(G := G);
  r.classes := ConjugacyClasses(G);
  r.reps := List(r.classes, Representative);
  r.tree := [[1..Length(r.reps)]];
  if Length(args) > 0 then
    funcs := ShallowCopy(args);
    Add(funcs, CCInvFuncs.ConjTest);
  elif IsPermGroup(G) then
    funcs := [CCInvFuncs.NoticeReps, CCInvFuncs.CycStruct, CCInvFuncs.ConjTest];
  elif IsMatrixGroup(G) then
    funcs := [CCInvFuncs.NoticeReps, CCInvFuncs.CharPol, CCInvFuncs.MinPol, CCInvFuncs.ConjTest];
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

# applying this is easy:
# optionally, a list of class indices can be given which can be excluded
# from the context of the application
BindGlobal("PositionConjugacyClass", function(G, x, exclude...)
  local r, tree, inv, pos;
  r := ConjugacyClassInvariants(G);
  if Length(exclude) > 0 then
    r.exclude := exclude[1];
  else
    r.exclude := [];
  fi;
  tree := r.tree;
  while IsList(tree) do
    inv := tree[2](r, x);
    pos := PositionSorted(tree[3], inv);
    tree := tree[4][pos];
  od;
  return tree;
end);

