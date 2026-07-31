###########################################################################
##  cctab.tst
##
##  Tests for the character table computations of the CCTab package.
##
gap> START_TEST("cctab.tst");
gap> SetInfoLevel(InfoCCTable, 0);

##  A self contained check that 'Irr(G)' really returns the irreducible
##  characters of 'G': there must be one for each conjugacy class, the sum of
##  the squares of the degrees must be |G|, each degree must divide |G|, and
##  the first orthogonality relation must hold.
gap> CheckIrr := function(G)
>      local t, irr, n, sp, i, j;
>      t := OrdinaryCharacterTable(G);
>      irr := Irr(G);
>      n := NrConjugacyClasses(G);
>      if Length(irr) <> n then
>        return "wrong number of irreducible characters";
>      fi;
>      if Sum(irr, chi -> chi[1]^2) <> Size(G) then
>        return "sum of squares of degrees is not |G|";
>      fi;
>      if not ForAll(irr, chi -> Size(G) mod chi[1] = 0) then
>        return "some degree does not divide |G|";
>      fi;
>      for i in [1..n] do
>        for j in [i..n] do
>          if i = j then sp := 1; else sp := 0; fi;
>          if ScalarProduct(t, irr[i], irr[j]) <> sp then
>            return Concatenation("orthogonality fails for ", String([i,j]));
>          fi;
>        od;
>      od;
>      return true;
>    end;;

##  supersolvable groups take a shortcut via 'IrrBaumClausen'
gap> CheckIrr(DihedralGroup(16));
true

##  the interesting cases go through 'CCTable'
gap> CheckIrr(AlternatingGroup(5));
true
gap> CheckIrr(SymmetricGroup(5));
true
gap> CheckIrr(SL(2,5));
true
gap> CheckIrr(PSL(3,2));
true
gap> CheckIrr(SymmetricGroup(6));
true
gap> CheckIrr(PSL(2,11));
true
gap> CheckIrr(MathieuGroup(11));
true

##  degrees of some well known character tables
gap> SortedList(List(Irr(AlternatingGroup(5)), chi -> chi[1]));
[ 1, 3, 3, 4, 5 ]
gap> SortedList(List(Irr(PSL(3,2)), chi -> chi[1]));
[ 1, 3, 3, 6, 7, 8 ]
gap> SortedList(List(Irr(MathieuGroup(11)), chi -> chi[1]));
[ 1, 10, 10, 10, 11, 16, 16, 44, 45, 55 ]

##  the table computed by CCTab must agree with the one from the character
##  table library (only checked if the CTblLib package is available)
gap> t := OrdinaryCharacterTable(AlternatingGroup(5));;
gap> Irr(t);;
gap> InfoText(t);
"origin: computed by CCTable"
gap> if LoadPackage("ctbllib", false) = true then
>      Print(TransformingPermutationsCharacterTables(t,
>                                     CharacterTable("A5")) <> fail, "\n");
>    else
>      Print(true, "\n");
>    fi;
true

##  power maps are provided by the package as well
gap> G := AlternatingGroup(5);;
gap> t := OrdinaryCharacterTable(G);;
gap> PowerMap(t, 1) = [1..NrConjugacyClasses(G)];
true
gap> OrdersClassRepresentatives(t);
[ 1, 2, 3, 5, 5 ]
gap> PowerMap(t, 2);
[ 1, 1, 3, 5, 4 ]
gap> ForAll([1..5], n -> PowerMap(t, n) = PowerMap(t, n + Exponent(G)));
true

##
gap> STOP_TEST("cctab.tst");
