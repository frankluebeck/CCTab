###########################################################################
##  WallTests.g
##
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##
##  Tests of the basic functionality of the functions for conjugacy classes
##  of classical groups (Classical/Wall.gi) for all groups with at most M
##  conjugacy classes, and a table of the runtimes.
##
##  Usage:
##    LoadPackage("CCTab");
##    Read(Filename(DirectoriesPackageLibrary("CCTab", "tst"), "WallTests.g"));
##    res := WallTestRun(30);;          # all groups with <= 30 conjugacy
##                                      # classes (the bound M is on the
##                                      # number of classes, not the order)
##    WallTestTable(res);               # or WallTestTable(res, "markdown")
##                                      # or WallTestTable(res, "latex")
##    # with comparison with GAP's own class computation for the groups
##    # of order at most 10^5:
##    res := WallTestRun(30, rec(gapBound := 10^5));;
##
##  The kinds of groups (option 'kinds', default: all):
##    "GL", "SL"           GL(n,q), SL(n,q)
##    "GU", "SU"           GU(n,r), SU(n,r)          (field GF(r^2))
##    "Sp"                 Sp(n,q)
##    "GO", "SO", "Omega"  GO(n,q), GO+-(n,q) and the subgroups SO (q odd),
##                         Omega (not in odd dimension for even q)
##    "CSp", "CGO", "CGU"  the conformal groups
##    "Spin"               Spin(n,q), Spin+-(n,q), q odd, n >= 3
##
##  For each group the following is tested (and the time measured):
##    nr    the number of classes from the generating function
##    inv   the list of class invariants; its length must be the number nr,
##          and the invariants must be pairwise different
##    rep   for each invariant a representative; it must lie in the group
##          and have the given invariant
##    conj  for each representative r a random conjugate x = r^g (g random
##          in the group); x must have the same invariant, the conjugating
##          element record c of x must have c.invariant = inv,
##          c.representative = r, c.conjugator in the group and
##          c.conjugator * x * c.conjugator^-1 = r
##    sizes the class sizes must add up to the group order
##    gap   (optional, only if the option 'gapBound' is given and the group
##          order is at most gapBound) the number of classes must be the
##          number computed
##          by GAP's generic methods for the permutation action of the group
##          on the orbits of the standard basis vectors
##
##  Options (record, second argument of WallTestRun and WallTestCase):
##    kinds     list of kinds (see above)
##    gapBound  bound for the group order for the comparison with GAP
##              (default 0, that is no comparison)
##    conj      false: skip the 'conj' test
##    verbose   false: no output for each group
##    logfile   name of a file, after each group a line with the results
##              is appended to it (useful for long runs)
##
##  Each test is run with CALL_WITH_CATCH, errors are reported in the
##  table (status "ERROR") and do not stop the run.
##

BindGlobal("WALLTEST_Kinds", ["GL", "SL", "GU", "SU", "Sp", "GO", "SO",
        "Omega", "CSp", "CGO", "CGU", "Spin"]);

# similitude test for conformal groups (for even q and orthogonal forms the
# Gram matrix is the matrix of the quadratic form)
BindGlobal("WALLTEST_IsSimilitude", function(f, x)
  local lam, M;
  if not IsMatrix(x) or Length(x) <> f.n or IsZero(DeterminantMat(x)) then
    return false;
  fi;
  lam := WallConformalMultiplier(f, x);
  if IsZero(lam) then
    return false;
  fi;
  if f.type = "O" and IsEvenInt(f.q) then
    # Q(vx) = lam Q(v) iff x Q x^tr - lam Q is alternating
    M := x * f.gram * TransposedMat(x) - lam * f.gram;
    return M = -TransposedMat(M) and ForAll([1..f.n], i-> IsZero(M[i][i]));
  fi;
  return x * f.gram * WALL_Star(f, x) = lam * f.gram;
end);

# name of a group
BindGlobal("WALLTEST_Name", function(kind, n, q, e)
  local s;
  if e = 1 then s := "+"; elif e = -1 then s := "-"; else s := ""; fi;
  return Concatenation(kind, s, "(", String(n), ",", String(q), ")");
end);

# Number of conjugacy classes of a matrix group g of order ord, computed
# by GAP's generic methods for the permutation action on the orbits of the
# standard basis vectors.  We do not use a nice monomorphism of g: with
# GAP 4.17dev the following hangs (the image of the nice monomorphism is
# inconsistent after this random state):
#   Reset(GlobalMersenneTwister, 1);; Reset(GlobalRandomSource, 1);;
#   NrConjugacyClasses(Group(GeneratorsOfGroup(Sp(4,2))));
BindGlobal("WALLTEST_GAPNrClasses", function(g, ord)
  local gens, orb, one, i, v, P;
  gens := GeneratorsOfGroup(g);
  orb := [];
  one := One(g);
  for i in [1..Length(one)] do
    v := one[i];
    if not v in orb then
      Append(orb, Orbit(g, v, OnRight));
    fi;
  od;
  P := Group(List(gens, x-> Permutation(x, orb, OnRight)), ());
  if Size(P) <> ord then
    Error("WALLTEST_GAPNrClasses: permutation group has wrong order");
  fi;
  return NrConjugacyClasses(P);
end);

# A record with the operations for a group of the given kind:
#   nr(), invariants(), rep(inv), inv(x), conj(x), isin(x), random(),
#   classSize(inv), order(), group() (a GAP group, only used for the
#   comparison with GAP's generic methods).
BindGlobal("WALLTEST_Ops", function(kind, n, q, e)
  local ops, f, S, G, pow, randomS, sp;
  ops := rec(kind := kind, n := n, q := q, e := e,
             name := WALLTEST_Name(kind, n, q, e));
  if kind = "Spin" then
    if IsOddInt(n) then sp := WallSpinGroup(n, q);
    else sp := WallSpinGroup(e, n, q); fi;
    ops.nr := {}-> WallSpinNrClasses(sp);
    ops.invariants := {}-> WallSpinClassInvariants(sp);
    ops.rep := inv-> WallSpinRepresentative(sp, inv);
    ops.inv := x-> WallSpinInvariant(sp, x);
    ops.conj := x-> WallSpinConjugatingElement(sp, x);
    ops.isin := x-> x in sp;
    ops.random := {}-> PseudoRandom(sp);
    ops.classSize := inv-> WallSpinClassSize(sp, inv);
    ops.order := {}-> Size(sp);
    ops.group := {}-> sp;
    return ops;
  fi;

  # the form record
  if kind in ["GL", "SL"] then
    f := WallClassicalForm("L", n, GF(q));
  elif kind in ["GU", "SU", "CGU"] then
    f := WallFormOfGroup(GU(n, q));
  elif kind in ["Sp", "CSp"] then
    f := WallFormOfGroup(Sp(n, q));
  elif e = 0 then
    f := WallFormOfGroup(GO(n, q));
  else
    f := WallFormOfGroup(GO(e, n, q));
  fi;
  ops.f := f;

  if kind in ["GL", "GU", "Sp", "GO"] then
    ops.nr := {}-> WallNrClasses(f);
    ops.invariants := {}-> WallClassInvariants(f);
    ops.rep := inv-> WallRepresentative(f, inv);
    ops.inv := x-> WallInvariant(f, x);
    ops.conj := x-> WallConjugatingElement(f, x);
    ops.isin := x-> WallIsInGroup(f, x);
    ops.random := function()
      if not IsBound(ops.G) then ops.G := WallGroup(f); fi;
      return PseudoRandom(ops.G);
    end;
    ops.classSize := inv-> WallClassSize(f, inv);
    ops.order := {}-> WallGroupOrder(f);
    ops.group := function()
      if not IsBound(ops.G) then ops.G := WallGroup(f); fi;
      return ops.G;
    end;
  elif kind in ["CSp", "CGO", "CGU"] then
    ops.nr := {}-> WallConformalNrClasses(f);
    ops.invariants := {}-> WallConformalClassInvariants(f);
    ops.rep := ci-> WallConformalRepresentative(f, ci);
    ops.inv := x-> WallConformalInvariant(f, x);
    ops.conj := x-> WallConformalConjugatingElement(f, x);
    ops.isin := x-> WALLTEST_IsSimilitude(f, x);
    ops.random := function()
      if not IsBound(ops.G) then ops.G := WallConformalGroup(f); fi;
      return PseudoRandom(ops.G);
    end;
    ops.classSize := ci-> WallConformalClassSize(f, ci);
    ops.order := {}-> WallConformalGroupOrder(f);
    ops.group := function()
      if not IsBound(ops.G) then ops.G := WallConformalGroup(f); fi;
      return ops.G;
    end;
  else
    # subgroups SL, SU, SO, Omega of G(F)
    S := kind;
    ops.nr := {}-> WallSubgroupNrClasses(f, S);
    ops.invariants := {}-> WallSubgroupClassInvariants(f, S);
    ops.rep := sinv-> WallSubgroupRepresentative(f, S, sinv);
    ops.inv := x-> WallSubgroupInvariant(f, S, x);
    ops.conj := x-> WallSubgroupConjugatingElement(f, S, x);
    ops.isin := x-> WallIsInSubgroup(f, S, x);
    ops.classSize := sinv-> WallSubgroupClassSize(f, S, sinv);
    ops.order := {}-> WallSubgroupOrder(f, S);
    # random elements: random elements of G(F) lying in S, otherwise a
    # power which lies in S
    if S = "SL" then pow := q - 1;
    elif S = "SU" then pow := q + 1;
    else pow := 2; fi;
    randomS := function()
      local i, g;
      if not IsBound(ops.G) then ops.G := WallGroup(f); fi;
      for i in [1..10] do
        g := PseudoRandom(ops.G);
        if WallIsInSubgroup(f, S, g) then
          return g;
        fi;
      od;
      g := g^pow;
      if not WallIsInSubgroup(f, S, g) then
        Error("WALLTEST_Ops: no random element in ", S);
      fi;
      return g;
    end;
    ops.random := randomS;
    ops.group := function()
      local gens, H, ord;
      if not IsBound(ops.H) then
        gens := [];
        ord := ops.order();
        repeat
          Add(gens, randomS());
          H := Group(gens, One(gens[1]));
        until Size(H) = ord;
        ops.H := H;
      fi;
      return ops.H;
    end;
  fi;
  return ops;
end);

##  WallTestCases(M[, kinds])
##  returns the list of records rec(kind, n, q, e, name, nr) for all groups
##  of the given kinds with at most M conjugacy classes.
##  (The number of classes is not monotonous in q for the subgroups, e.g.,
##  k(SL(2,7)) = 11 > k(SL(2,8)) = 9, so we only stop when the number of
##  classes exceeds 2M+10.)
BindGlobal("WallTestCases", function(arg)
  local M, kinds, stop, res, series, kind, s, n, q, nr, any, qs, ops;
  M := arg[1];
  if Length(arg) > 1 then kinds := arg[2]; else kinds := WALLTEST_Kinds; fi;
  stop := 2 * M + 10;
  res := [];
  for kind in kinds do
    # series: [first n, step, sign e, condition on q]
    if kind = "GL" then series := [[1, 1, 0, IsInt]];
    elif kind = "SL" then series := [[2, 1, 0, IsInt]];
    elif kind in ["GU", "CGU"] then series := [[1, 1, 0, IsInt]];
    elif kind = "SU" then series := [[2, 1, 0, IsInt]];
    elif kind in ["Sp", "CSp"] then series := [[2, 2, 0, IsInt]];
    elif kind in ["GO", "CGO"] then
      series := [[3, 2, 0, IsInt], [2, 2, 1, IsInt], [2, 2, -1, IsInt]];
    elif kind = "SO" then
      series := [[3, 2, 0, IsOddInt], [2, 2, 1, IsOddInt],
                 [2, 2, -1, IsOddInt]];
    elif kind = "Omega" then
      series := [[3, 2, 0, IsOddInt], [2, 2, 1, IsInt], [2, 2, -1, IsInt]];
    elif kind = "Spin" then
      series := [[3, 2, 0, IsOddInt], [4, 2, 1, IsOddInt],
                 [4, 2, -1, IsOddInt]];
    else
      Error("WallTestCases: unknown kind ", kind);
    fi;
    for s in series do
      n := s[1];
      repeat
        any := false;
        q := 1;
        repeat
          repeat
            q := q + 1;
          until IsPrimePowerInt(q) and s[4](q);
          ops := WALLTEST_Ops(kind, n, q, s[3]);
          nr := ops.nr();
          if nr <= M then
            Add(res, rec(kind := kind, n := n, q := q, e := s[3],
                         name := ops.name, nr := nr));
            any := true;
          fi;
        until nr > stop;
        n := n + s[2];
      until not any;
    od;
  od;
  return res;
end);

##  WallTestCase(c[, opts])
##  runs the tests for one group, c is a record as returned by
##  WallTestCases (only the components kind, n, q, e are used).
##  Returns a record with components name, kind, nr, status ("ok", "FAIL"
##  or "ERROR"), failures (list of strings), times (record of runtimes in
##  ms: nr, inv, rep, conj, sizes, gap, total).
BindGlobal("WallTestCase", function(arg)
  local c, opts, gapBound, doConj, res, t, ops, fail, body, r, brk;
  c := arg[1];
  if Length(arg) > 1 then opts := arg[2]; else opts := rec(); fi;
  if IsBound(opts.gapBound) then gapBound := opts.gapBound;
  else gapBound := 0; fi;
  doConj := not IsBound(opts.conj) or opts.conj <> false;
  res := rec(kind := c.kind, name := WALLTEST_Name(c.kind, c.n, c.q, c.e),
             n := c.n, q := c.q, e := c.e, failures := [],
             times := rec(nr := 0, inv := 0, rep := 0, conj := 0,
                          sizes := 0, gap := 0, total := 0),
             gap := "-", status := "ok");
  fail := function(str)
    Add(res.failures, str);
    res.status := "FAIL";
  end;
  body := function()
    local nr, invs, reps, inv, x, g, cc, i, ord, k, ok, t;
    ops := WALLTEST_Ops(c.kind, c.n, c.q, c.e);
    # number of classes from the generating function
    t := Runtime();
    nr := ops.nr();
    res.times.nr := Runtime() - t;
    res.nr := nr;
    # invariants
    t := Runtime();
    invs := ops.invariants();
    res.times.inv := Runtime() - t;
    if Length(invs) <> nr then
      fail(Concatenation("number of invariants ", String(Length(invs)),
                         " <> ", String(nr)));
    fi;
    if Length(Set(invs)) <> Length(invs) then
      fail("invariants not pairwise different");
    fi;
    # representatives
    t := Runtime();
    reps := [];
    for i in [1..Length(invs)] do
      x := ops.rep(invs[i]);
      reps[i] := x;
      if not ops.isin(x) then
        fail(Concatenation("representative ", String(i), " not in group"));
      elif ops.inv(x) <> invs[i] then
        fail(Concatenation("representative ", String(i),
                           " has wrong invariant"));
      fi;
    od;
    res.times.rep := Runtime() - t;
    # random conjugates and conjugating elements
    if doConj then
      t := Runtime();
      for i in [1..Length(invs)] do
        g := ops.random();
        x := reps[i]^g;
        if ops.inv(x) <> invs[i] then
          fail(Concatenation("conjugate of representative ", String(i),
                             " has wrong invariant"));
          continue;
        fi;
        cc := ops.conj(x);
        if cc.invariant <> invs[i] then
          fail(Concatenation("conjugating element ", String(i),
                             ": wrong invariant"));
        fi;
        if cc.representative <> reps[i] then
          fail(Concatenation("conjugating element ", String(i),
                             ": wrong representative"));
        fi;
        if not ops.isin(cc.conjugator) then
          fail(Concatenation("conjugating element ", String(i),
                             " not in group"));
        fi;
        if cc.conjugator * x * cc.conjugator^-1 <> cc.representative then
          fail(Concatenation("conjugating element ", String(i),
                             " does not conjugate"));
        fi;
      od;
      res.times.conj := Runtime() - t;
    fi;
    # class equation
    t := Runtime();
    ord := ops.order();
    if Sum(invs, ops.classSize) <> ord then
      fail("class sizes do not add up to the group order");
    fi;
    res.times.sizes := Runtime() - t;
    # comparison with GAP's generic methods
    if ord <= gapBound then
      t := Runtime();
      g := ops.group();
      k := WALLTEST_GAPNrClasses(g, ord);
      res.times.gap := Runtime() - t;
      if k <> nr then
        fail(Concatenation("GAP finds ", String(k), " classes"));
        res.gap := "differs";
      else
        res.gap := "ok";
      fi;
    fi;
    return true;
  end;
  t := Runtime();
  brk := BreakOnError;
  BreakOnError := false;
  r := CALL_WITH_CATCH(body, []);
  BreakOnError := brk;
  res.times.total := Runtime() - t;
  if r[1] <> true then
    res.status := "ERROR";
    Add(res.failures, "error during the tests");
  fi;
  if not IsBound(res.nr) then
    res.nr := "?";
  fi;
  return res;
end);

##  WallTestRun(M[, opts])
##  runs WallTestCase for all groups with at most M classes, returns the
##  list of result records.
BindGlobal("WallTestRun", function(arg)
  local M, opts, kinds, verbose, cases, res, c, r, nfail;
  M := arg[1];
  if Length(arg) > 1 then opts := arg[2]; else opts := rec(); fi;
  if IsBound(opts.kinds) then kinds := opts.kinds;
  else kinds := WALLTEST_Kinds; fi;
  verbose := not IsBound(opts.verbose) or opts.verbose <> false;
  cases := WallTestCases(M, kinds);
  if verbose then
    Print("#I  ", Length(cases), " groups with at most ", M,
          " classes\n");
  fi;
  res := [];
  for c in cases do
    r := WallTestCase(c, opts);
    Add(res, r);
    if IsBound(opts.logfile) then
      AppendTo(opts.logfile, String(r.name, -16), String(r.nr, 8),
               " classes", String(r.times.total, 10), " ms  ", r.status,
               "  ", JoinStringsWithSeparator(r.failures, "; "), "\n");
    fi;
    if verbose then
      Print("#I  ", String(r.name, -16), String(r.nr, 6), " classes  ",
            String(r.times.total, 8), " ms  ", r.status, "\n");
      if r.status <> "ok" then
        Print("#I      ", JoinStringsWithSeparator(r.failures, "; "), "\n");
      fi;
    fi;
  od;
  if verbose then
    nfail := Number(res, r-> r.status <> "ok");
    Print("#I  ", Length(res), " groups tested, ", nfail,
          " with failures or errors\n");
  fi;
  return res;
end);

##  WallTestTable(res[, format[, file]])
##  prints a table of the results res (from WallTestRun) with the runtimes
##  in ms. format is "text" (default), "markdown" or "latex". If file is
##  given, the table is appended to this file (otherwise it is printed).
##  The table is also returned as a string.
##  Columns: number of classes, runtimes of the tests nr, inv, rep, conj,
##  sizes, gap (column "GAP") and total, and the result of the comparison
##  with GAP ("ok", "differs" or "-" if not done).
BindGlobal("WallTestTable", function(arg)
  local res, format, file, head, rows, r, w, i, str, line, sep, tot, k,
        keys, out;
  res := arg[1];
  if Length(arg) > 1 then format := arg[2]; else format := "text"; fi;
  if Length(arg) > 2 then file := arg[3]; else file := fail; fi;
  keys := ["nr", "inv", "rep", "conj", "sizes", "gap", "total"];
  head := ["group", "classes", "nr", "inv", "rep", "conj", "sizes", "GAP",
           "total", "GAP check", "status"];
  rows := [];
  for r in res do
    Add(rows, Concatenation([r.name, String(r.nr)],
              List(keys, k-> String(r.times.(k))),
              [String(r.gap), r.status]));
  od;
  # line with sums
  tot := Concatenation(["total", String(Sum(res, r-> r.nr))],
            List(keys, k-> String(Sum(res, r-> r.times.(k)))),
            ["", Concatenation(String(Number(res, r-> r.status = "ok")),
                               "/", String(Length(res)), " ok")]);
  w := List([1..Length(head)], i-> Maximum(Concatenation([Length(head[i]),
           Length(tot[i])], List(rows, row-> Length(row[i])))));
  str := "";
  line := function(row, sepb, sepm, sepe)
    local i, s;
    Append(str, sepb);
    for i in [1..Length(row)] do
      if i in [1, Length(row)] then
        s := String(row[i], -w[i]);    # left aligned
      else
        s := String(row[i], w[i]);     # right aligned
      fi;
      Append(str, s);
      if i < Length(row) then Append(str, sepm); fi;
    od;
    Append(str, sepe);
    Append(str, "\n");
  end;
  if format = "markdown" then
    line(head, "| ", " | ", " |");
    sep := List([1..Length(head)], i-> Concatenation(ListWithIdenticalEntries(
             w[i]-1, '-'), ":"));
    sep[1] := ListWithIdenticalEntries(w[1], '-');
    sep[Length(sep)] := ListWithIdenticalEntries(w[Length(sep)], '-');
    line(sep, "| ", " | ", " |");
    for r in rows do line(r, "| ", " | ", " |"); od;
    line(tot, "| ", " | ", " |");
  elif format = "latex" then
    Append(str, Concatenation("\\begin{tabular}{l",
           Concatenation(ListWithIdenticalEntries(Length(head)-2, "r")),
           "l}\n"));
    line(head, "", " & ", " \\\\ \\hline");
    for r in rows do
      r := ShallowCopy(r);
      r[1] := ReplacedString(r[1], "+(", "^+(");
      r[1] := ReplacedString(r[1], "-(", "^-(");
      r[1] := Concatenation("$\\mathrm{", r[1], "}$");
      r[1] := ReplacedString(r[1], "^+(", "}^+\\mathrm{(");
      r[1] := ReplacedString(r[1], "^-(", "}^-\\mathrm{(");
      line(r, "", " & ", " \\\\");
    od;
    line(tot, "\\hline ", " & ", " \\\\");
    Append(str, "\\end{tabular}\n");
  elif format = "text" then
    line(head, "", "  ", "");
    Append(str, Concatenation(ListWithIdenticalEntries(Sum(w) +
                2 * (Length(w) - 1), '-'), "\n"));
    for r in rows do line(r, "", "  ", ""); od;
    Append(str, Concatenation(ListWithIdenticalEntries(Sum(w) +
                2 * (Length(w) - 1), '-'), "\n"));
    line(tot, "", "  ", "");
  else
    Error("WallTestTable: format must be \"text\", \"markdown\" or \"latex\"");
  fi;
  # write without GAP's line breaking
  if file <> fail then
    out := OutputTextFile(file, true);
  else
    out := OutputTextUser();
  fi;
  SetPrintFormattingStatus(out, false);
  WriteAll(out, str);
  if file <> fail then
    CloseStream(out);
  fi;
  return str;
end);
