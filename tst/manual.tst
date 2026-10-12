# This file was created automatically, do not edit!
#############################################################################
##
#W  manual.tst               GAP 4 package CCTab                Frank Lübeck
##
#Y  Copyright (C) 2026,  Lehrstuhl f. Alg. u. Zahlenth., RWTH Aachen, Germany
##
##  This file contains the GAP code of the examples in the package
##  documentation.
##  
##  In order to run the tests, one starts GAP from the `tst' subdirectory
##  of the `pkg/CCTab' directory, and calls `Test( "manual.tst" );'.
##  
gap> LoadPackage( "CCTab", false );
true
gap> LoadPackage( "ctbllib", false );
true
gap> save:= SizeScreen();;
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "Input file: manual.tst" );

##  doc/../lib/PositionConjugacyClass.gi (307-311)
gap> G := AlternatingGroup(5);;
gap> creps := List(ConjugacyClasses(G), Representative);;
gap> List(creps, x-> PositionConjugacyClass(G, x^Random(G)));
[ 1, 2, 3, 4, 5 ]

##  doc/../lib/PositionConjugacyClass.gi (231-246)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> ConjugacyClassInvariants(G);
rec( G := Alt( [ 1 .. 5 ] ), 
  classes := [ ()^G, (1,2)(3,4)^G, (1,2,3)^G, (1,2,3,4,5)^G, 
      (1,2,3,5,4)^G ], 
  reps := [ (), (1,2)(3,4), (1,2,3), (1,2,3,4,5), (1,2,3,5,4) ], 
  tree := [ [ 1 .. 5 ], function( r, x ) ... end, 
      [ 1, 2, 3, 4, 5, fail ], 
      [ 1, 2, 3, 4, 5, 
          [ [ 1 .. 5 ], function( r, x ) ... end, 
              [ [  ], [ ,,, 1 ], [ , 1 ], [ 2 ] ], 
              [ 1, 
                  [ [ 4, 5 ], function( r, x ) ... end, [ 4, 5 ], 
                      [ 4, 5 ] ], 3, 2 ] ] ] ] )

##  doc/../lib/PowerMaps.gi (56-68)
gap> G := AlternatingGroup(5);;
gap> List(ConjugacyClasses(G), c-> Order(Representative(c)));
[ 1, 2, 3, 5, 5 ]
gap> PowerMapsOfAllClasses(G);
[ [ 1 ], [ 1, 2 ], [ 1, 3, 3 ], [ 1, 4, 5, 5, 4 ], [ 1, 5, 4, 4, 5 ] ]
gap> t := CharacterTable("M11");
CharacterTable( "M11" )
gap> PowerMapsOfAllClasses(t);
[ [ 1 ], [ 1, 2 ], [ 1, 3, 3 ], [ 1, 4, 2, 4 ], [ 1, 5, 5, 5, 5 ], 
  [ 1, 6, 3, 2, 3, 6 ], [ 1, 7, 4, 7, 2, 8, 4, 8 ], 
  [ 1, 8, 4, 8, 2, 7, 4, 7 ], [ 1, 9, 10, 9, 9, 9, 10, 10, 10, 9, 10 ]
    , [ 1, 10, 9, 10, 10, 10, 9, 9, 9, 10, 9 ] ]

##  doc/../lib/PowerMaps.gi (422-427)
gap> G := AlternatingGroup(5);;
gap> List(ConjugacyClasses(G), c-> Order(Representative(c)));
[ 1, 2, 3, 5, 5 ]
gap> RationalClassSets(G);
[ [ 1 ], [ 2 ], [ 3 ], [ 4, 5 ] ]

##  doc/../lib/PowerMaps.gi (464-466)
gap> NrRationalClasses(AlternatingGroup(5));
4

##  doc/../lib/PowerMaps.gi (603-614)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> rci := RationalClassesInfo(G);;
gap> rci[2];
rec( classes := [ 2 ], classlen := 15, conductor := 1, 
  exponents := [ 2, 2 ], ind := 2, order := 2 )
gap> rci[4];
rec( classes := [ 4, 5 ], classlen := 12, conductor := 5, 
  cpol := [ 1, 1, 1, 1, 1 ], dim := 4, exponents := [ 4, 4, 2 ], 
  field := NF(5,[ 1, 4 ]), ind := [ 4 .. 7 ], order := 5, 
  ratvec := [ 0, 2, 2, -1, 4, -1 ], stabilizer := [ 1, 4 ] )

##  doc/../lib/PowerMaps.gi (342-344)
gap> MaximalCyclics(AlternatingGroup(5));
[ 4, 3, 2 ]

##  doc/../lib/PowerMaps.gi (274-283)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> T := CCTable(G);;
gap> InduceAllFromCyclicSubgroup(G, 4);
[ [ 12, 0, 0, 2, 2 ], [ 12, 0, 0, E(5)+E(5)^4, E(5)^2+E(5)^3 ], 
  [ 12, 0, 0, E(5)^2+E(5)^3, E(5)+E(5)^4 ] ]
gap> InduceAllFromCyclicSubgroup(T, 4);
[ [ 12, 0, 0, 2 ], [ 12, 0, 0, E(5)+E(5)^4 ], 
  [ 12, 0, 0, E(5)^2+E(5)^3 ] ]

##  doc/../lib/PowerMaps.gi (386-394)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> indcyc := InducedFromAllMaximalCyclicSubgroups(G);
[ [ 12, 0, 0, 2, 2 ], [ 12, 0, 0, E(5)^2+E(5)^3, E(5)+E(5)^4 ], 
  [ 12, 0, 0, E(5)+E(5)^4, E(5)^2+E(5)^3 ], [ 20, 0, -1, 0, 0 ], 
  [ 20, 0, 2, 0, 0 ], [ 30, -2, 0, 0, 0 ], [ 30, 2, 0, 0, 0 ] ]
gap> Rank(indcyc);
5

##  doc/../lib/PowerMaps.gi (740-745)
gap> G := AlternatingGroup(5);;
gap> pmchars := PowerMapCharacters(G, 2);
[ [ 30, 30, 0, 0, 0 ], [ 0, 0, 30, 0, 0 ], [ 0, 0, 0, 30, 30 ] ]
gap> MatScalarProducts(Irr(G), pmchars);
[ [ 8, 2, 10, -6, -6 ], [ 10, 10, -10, 0, 0 ], [ 12, -12, 0, 6, 6 ] ]

##  doc/../lib/PowerMaps.gi (798-803)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> SmallPowerMapCharacters(G);
[ [ 0, 0, 0, 5, 5 ], [ 0, 0, 3, 0, 0 ], [ 0, 4, 0, 0, 0 ], 
  [ 4, 0, 4, 4, 4 ], [ 3, 3, 0, 3, 3 ], [ 5, 5, 5, 0, 0 ] ]

##  doc/../lib/PowerMaps.gi (860-867)
gap> G := AlternatingGroup(5);;
gap> A := AutomorphismGroup(G);
<group of size 120 with 3 generators>
gap> ActionAutomorphismsOnConjugacyClasses(G, A);
Group([ (4,5), (), () ])
gap> ActionAutomorphismsOnRationalClasses(G, A);
Group(())

##  doc/../lib/Elementary.gi (34-37)
gap> G := SL(4,2);;
gap> MaximalNonCyclicElementarySubgroups(G);
[ [ 1, 3 ], [ 1, 2 ], [ 6, 2 ] ]

##  doc/../lib/Elementary.gi (136-139)
gap> G := AlternatingGroup(5);;
gap> InducedFromElementary(G, 1, 2);
[ [ 15, -1, 0, 0, 0 ], [ 15, 3, 0, 0, 0 ] ]

##  doc/../lib/Elementary.gi (263-266)
gap> G := AlternatingGroup(5);;
gap> FusionElementaryCCTable(CCTable(G), 1,2);
[ [ [ 1, [ 0, 1 ] ], [ 2, [ 0, 2, 3, 4 ] ] ], [ 1, 2, 3, 4 ] ]

##  doc/../lib/Elementary.gi (439-453)
gap> G := SymmetricGroup(5);;
gap> ind := InductionDataFromElementaryCCTable(CCTable(G),1,2);;
gap> ind.next();
[ [ 15, 3, 3, 0, 1, 0, 0 ] ]
gap> ind.next();
[ [ 15, 3, -1, 0, -1, 0, 0 ] ]
gap> ind.next();
[ [ 15, -3, 3, 0, -1, 0, 0 ] ]
gap> ind.next();
[ [ 15, -3, -1, 0, 1, 0, 0 ] ]
gap> ind.next();
[ [ 30, 0, -2, 0, 0, 0, 0 ] ]
gap> ind.next();
fail

##  doc/../lib/LLL.gi (78-80)
gap> HermiteIntMat(RandomUnimodularMat(4));
[ [ 1, 0, 0, 0 ], [ 0, 1, 0, 0 ], [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ] ]

##  doc/../lib/LLL.gi (199-204)
gap> A := [ [ 9, -3, 1, -2 ], [ -3, 3, 1, 1 ], [ 1, 1, 13, -2 ],
>   [ -2, 1, -2, 5 ] ];;
gap> PermutedFractionFreeIntegerGaussPositiveDefinite(A);
[ [ [ 3, 1, -3, 1 ], [ 0, 14, -3, -7 ], [ 0, 0, 81, 21 ], 
      [ 0, 0, 0, 900 ] ], (1,3,4,2) ]

##  doc/../lib/LLL.gi (279-284)
gap> A := RandomUnimodularMat(5);;
gap> A := RandomUnimodularMat(5);;
gap> A * InverseUnimodularMat(A);
[ [ 1, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0 ], [ 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 1 ] ]

##  doc/../lib/LLL.gi (528-535)
gap> A := RandomUnimodularMat(5);;
gap> A := RandomUnimodularMat(5);;
gap> gr := A * TransposedMat(A);;
gap> h := LLLTransformUnimodularGram(gr);;
gap> h * gr * TransposedMat(h);
[ [ 1, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0 ], [ 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 1 ] ]

##  doc/../lib/CCTable.gi (82-96)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> CCT := CCTable(G);
CCTable( Alt( [ 1 .. 5 ] ) )
gap> IsCCTable(CCT);
true
gap> Irr(CCT);
[ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ], 
  [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ], 
  [ 5, 1, -1, 0, 0, 0, 0 ] ]
gap> ExpandFromCCTable(CCT, Irr(CCT));
[ [ 1, 1, 1, 1, 1 ], [ 3, -1, 0, -E(5)^2-E(5)^3, -E(5)-E(5)^4 ], 
  [ 3, -1, 0, -E(5)-E(5)^4, -E(5)^2-E(5)^3 ], [ 4, 0, 1, -1, -1 ], 
  [ 5, 1, -1, 0, 0 ] ]

##  doc/../lib/CCTable.gi (192-207)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> CCT := CCTable(G);;
gap> ind := InducedFromAllMaximalCyclicSubgroups(G);;
gap> enc := EncodeForCCTable(CCT, ind);
[ [ 12, 0, 0, 2, 0, 0, 0 ], [ 12, 0, 0, 0, 0, 1, 1 ], 
  [ 12, 0, 0, -1, 0, -1, -1 ], [ 20, 0, -1, 0, 0, 0, 0 ], 
  [ 20, 0, 2, 0, 0, 0, 0 ], [ 30, -2, 0, 0, 0, 0, 0 ], 
  [ 30, 2, 0, 0, 0, 0, 0 ] ]
gap> ExpandFromCCTable(CCT);
[  ]
gap> ExpandFromCCTable(CCT, enc);
[ [ 12, 0, 0, 2, 2 ], [ 12, 0, 0, E(5)^2+E(5)^3, E(5)+E(5)^4 ], 
  [ 12, 0, 0, E(5)+E(5)^4, E(5)^2+E(5)^3 ], [ 20, 0, -1, 0, 0 ], 
  [ 20, 0, 2, 0, 0 ], [ 30, -2, 0, 0, 0 ], [ 30, 2, 0, 0, 0 ] ]

##  doc/../lib/CCTable.gi (353-361)
gap> G := AlternatingGroup(5);;
gap> ind := InducedFromAllMaximalCyclicSubgroups(G);;
gap> CCT := CCTable(G);;
gap> ImportToCCTable(CCT, ind);
gap> UpdateHNFCCTable(CCT);
0
gap> HasFullRankCCTable(CCT);
true

##  doc/../lib/CCTable.gi (668-682)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> CCT := CCTable(G);;
gap> ImportInducedFromAllMaximalCyclicToCCTable(CCT);
gap> FindIndexCCTable(CCT);
2
gap> ImportToCCTable(CCT, SmallPowerMapCharacters(G));
gap> UpdateHNFCCTable(CCT);
2
gap> FindIrreduciblesInFullLattices(CCT);
gap> CCT!.irr;
[ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ], 
  [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ], 
  [ 5, 1, -1, 0, 0, 0, 0 ] ]

##  doc/../lib/CCTable.gi (527-534)
gap> G := MathieuGroup(24);;
gap> CCT := CCTable(G);;
gap> ImportInducedFromAllMaximalCyclicToCCTable(CCT);
gap> FindIndexCCTable(CCT);
4718592
gap> StringCollectedFactors(FindIndexCCTable(CCT));
"2^19 3^2"

##  doc/../lib/CCTable.gi (734-741)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> CCT := CCTable(G);;
gap> IrrCCTableHNF(CCT);
[ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ], 
  [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ], 
  [ 5, 1, -1, 0, 0, 0, 0 ] ]

##  doc/../lib/CCTable.gi (883-892)
gap> hnf := [ [ 1, 0, 1, 478, -2, -649 ], [ 0, 1, 1, 362, 2, -492 ],
> [ 0, 0, 0, 546, 0, -742 ] ];;
gap> piv := [1,2,4];;
gap> v := [3, 7, 1, 6, 0, -1];;
gap> AddVectorToHNF(hnf, piv, v);
39
gap> hnf;
[ [ 1, 0, 1, 2, -1090, 779 ], [ 0, 1, 1, 12, -798, 558 ], 
  [ 0, 0, 0, 14, 32, -42 ] ]

##  doc/../lib/ScalarProducts.gi (67-77)
gap> G := AlternatingGroup(5);;
gap> G := AlternatingGroup(5);;
gap> CCT := CCTable(G);;
gap> irr := Irr(CCT);
[ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ], 
  [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ], 
  [ 5, 1, -1, 0, 0, 0, 0 ] ]
gap> List(irr, c-> List(irr, d-> ScalarProduct(CCT, c, d)));
[ [ 1, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0 ], [ 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 1 ] ]

##  doc/../lib/SplitByCentre.gi (44-51)
gap> G := SL(4,5);;
gap> CCT := CCTable(G);;
gap> SplitByCentre(CCT);
gap> HasSplittingCentre(CCT);
true
gap> SplittingCentre(CCT);
[ 1, 10, 19, 28 ]

##  doc/../lib/SplitByCentre.gi (172-187)
gap> G := SmallGroup(96, 14);;
gap> G := SmallGroup(96, 14);;
gap> CCT := CCTable(G);;
gap> SplitByCentre(CCT);
gap> U := TrivialSubgroup(G);;
gap> reg := InducedClassFunction(TrivialCharacter(U), G);;
gap> SplitCharacterByCentre(CCT, reg);
[ [ 24, 0, 0, 24, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 
      0, 0, 0, 0 ], 
  [ 24, 0, 0, -24, 0, 24, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0, 0, 0, 0, 0, 
      0, 0, 0, 0 ], 
  [ 24, 0, 0, 24, 0, -24, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0, 0, 0, 0, 0, 
      0, 0, 0, 0 ], 
  [ 24, 0, 0, -24, 0, -24, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 
      0, 0, 0, 0 ] ]

##  doc/../lib/SomeCharacters.gi (46-62)
gap> NaturalCharacters(AlternatingGroup(5));
[ Character( CharacterTable( Alt( [ 1 .. 5 ] ) ),
  [ 4, 0, 1, -1, -1 ] ) ]
gap> NaturalCharacters(SL(3,5));
[ Character( CharacterTable( SL(3,5) ),
  [ 124, 4, 4, 0, 0, 4, 24, 4, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
      0, 0, 0, 0, 0, 0, 0, 0, 0 ] ), 
  Character( CharacterTable( SL(3,5) ),
  [ 15624, 24, 24, 0, 0, 24, 624, 24, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ), 
  Character( CharacterTable( SL(3,5) ),
  [ 30, 6, 0, 6, 6, 2, 5, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, -1, 
      -1, -1, -1, -1, -1, -1, -1, -1, -1 ] ) ]
gap> NaturalCharacters(SmallGroup(24,4));
[ Character( CharacterTable( <pc group of size 24 with 
    4 generators> ), [ 24, 0, 0, 0, 0, 0, 0, 0, 0 ] ) ]

##
gap> STOP_TEST( "manual.tst", 10000000 );
gap> SizeScreen( save );;

#############################################################################
##
#E
