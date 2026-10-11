#############################################################################
##
#W  cctab.tst                GAP 4 package CCTab                Frank Lübeck
##
#Y  Copyright (C) 2026,  Lehrstuhl f. Alg. u. Zahlenth., RWTH Aachen, Germany
##
##  This file contains tests for (essentially) all functions provided by
##  the CCTab package. It uses the example groups defined in
##  'testgroups.g' and, where available, compares results with the
##  character table library (CTblLib).
##
##  In order to run the tests, run 'gap' with 'gap tst/testall.g'
##  from the pkg/CCTab directory. Or use in a GAP session
##  'TestPackage("CCTab");'.
##
gap> LoadPackage( "CCTab", false );
true
gap> LoadPackage( "ctbllib", false );
true
gap> save:= SizeScreen();;
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "Input file: cctab.tst" );
gap> Read(Filename(DirectoriesPackageLibrary("CCTab", "tst"), "testgroups.g"));

##  Basic 'CCTable' object and attributes delegated to the underlying group.
gap> CCT:= CCTable( GA5 );;
gap> IsCCTable( CCT );
true
gap> Size( CCT ) = Size( GA5 );
true
gap> NrConjugacyClasses( CCT ) = NrConjugacyClasses( GA5 );
true
gap> OrdersClassRepresentatives( CCT ) = OrdersClassRepresentatives( GA5 );
true
gap> SizesConjugacyClasses( CCT ) = List( ConjugacyClasses( GA5 ), Size );
true
gap> NrRationalClasses( GA5 ) = NrRationalClasses( CCT );
true
gap> RatClassExps( GA5 ) = RatClassExps( CCT );
true
gap> RationalClassesInfo( GA5 ) = RationalClassesInfo( CCT );
true
gap> ScalarInfo( GA5 ) = ScalarInfo( CCT );
true

##  'PositionConjugacyClass' and 'ConjugacyClassInvariants': identifying
##  the class of a random conjugate must always return the original class.
gap> crepsmax:= List( ConjugacyClasses( Gmax24 ), Representative );;
gap> ForAll( [ 1 .. Length( crepsmax ) ], i->
>        PositionConjugacyClass( Gmax24, crepsmax[i]^Random( Gmax24 ) ) = i );
true
gap> Length( ConjugacyClassInvariants( Gmax24 ).classes )
>        = NrConjugacyClasses( Gmax24 );
true

##  'PowerMapsOfAllClasses': brute force correctness check.
gap> CheckPowerMaps:= function( G )
>     local cls, reps, pm, i, x, k;
>     cls:= ConjugacyClasses( G );
>     reps:= List( cls, Representative );
>     pm:= PowerMapsOfAllClasses( G );
>     for i in [ 1 .. Length( reps ) ] do
>       x:= reps[i];
>       for k in [ 0 .. Length( pm[i] )-1 ] do
>         if not x^k in cls[pm[i][k+1]] then
>           return false;
>         fi;
>       od;
>     od;
>     return true;
>   end;;
gap> CheckPowerMaps( GA5 );
true
gap> CheckPowerMaps( Gmax24 );
true

# And an example with more complicated rational classes.
gap> CheckPowerMaps(Sp(4,7));
true

##  'RationalClassSets', 'MaximalCyclics', 'InducedFromAllMaximalCyclicSubgroups':
##  the classes partition all conjugacy classes, 'MaximalCyclics' returns
##  first entries of 'RationalClassSets', and the induced characters from
##  all maximal cyclic subgroups span the full space of class functions.
gap> Sum( RationalClassSets( GSL313 ), Length ) = NrConjugacyClasses( GSL313 );
true
gap> ForAll( MaximalCyclics( GSL313 ),
>            i-> i in List( RationalClassSets( GSL313 ), a-> a[1] ) );
true
gap> indmax := InducedFromAllMaximalCyclicSubgroups( Gmax24 );;
gap> Rank( indmax ) = NrConjugacyClasses( Gmax24 );
true
gap> Rank( indmax ) = Rank(EncodeForCCTable(CCTable( Gmax24 ), indmax));
true

##  'RatPartVec': coefficient at 1 of E(n)^i modulo the n-th cyclotomic
##  polynomial, as a vector for i in [0..n-1].
gap> RatPartVec( 5 );
[ 1, 0, 0, 0, -1 ]
gap> RatPartVec( 12 );
[ 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0 ]

##  'PowerMapCharacters', 'SmallPowerMapCharacters': these must be
##  generalized characters, i.e., their scalar products with all
##  irreducibles are integers. Also compare 'CCTScalarProduct' (the plain
##  &GAP; implementation) with 'ScalarProduct' (which uses a kernel
##  extension when available).
gap> ir:= Irr( CCT );;
gap> pmc:= EncodeForCCTable( CCT, PowerMapCharacters( GA5, 2 ) );;
gap> ForAll( pmc, v-> ForAll( ir, ch-> IsInt( ScalarProduct( CCT, ch, v ) ) ) );
true
gap> spc:= EncodeForCCTable( CCT, SmallPowerMapCharacters( GA5 ) );;
gap> ForAll( spc, v-> ForAll( ir, ch-> IsInt( ScalarProduct( CCT, ch, v ) ) ) );
true
gap> ForAll( ir, c-> ForAll( ir, d->
>        CCTScalarProduct( CCT, c, d ) = ScalarProduct( CCT, c, d ) ) );
true
gap> tab := CharacterTable( GA5 );; 
gap> perm := IdentificationOfConjugacyClasses(tab);;
gap> irr := List(ExpandFromCCTable(CCT, ir), ch-> ch{perm});;
gap> ForAll([1..NrConjugacyClasses(CCT)], i-> ForAll([1..i], j-> 
>        ScalarProduct(tab, irr[i], irr[j]) = ScalarProduct(CCT, ir[i], ir[j])));
true

##  'NaturalCharacters', 'pPrimeCharacter', 'pPrimeRestriction' for a
##  permutation group.
gap> nc:= NaturalCharacters( GA5 );;
gap> List( nc, AsList );
[ [ 4, 0, 1, -1, -1 ] ]
gap> AsList( pPrimeCharacter( nc[1], 2 ) );
[ 4, 4, 1, -1, -1 ]
gap> AsList( pPrimeRestriction( nc[1], 2 ) );
[ 4, 0, 1, -1, -1 ]

##  Full pipeline via the &GAP; library interface ('OrdinaryCharacterTable',
##  'Irr', 'PowerMap' for a table with 'CCTable'), and comparison with the
##  character table library.
gap> tGA5:= CharacterTable( GA5 );;
gap> IsInternallyConsistent( tGA5 );
true
gap> TransformingPermutationsCharacterTables( tGA5, CharacterTable( "A5" ) )
>        <> fail;
true

##  Step by step construction of the character table of 'Gmax24' (the
##  maximal subgroup "2^6:3.s6" of M24): induction from maximal cyclic
##  subgroups alone does not yet give the full lattice of generalized
##  characters, so 'NaturalCharacters' and 'SmallPowerMapCharacters' are
##  added as well (this still does not suffice, the remaining work is done
##  automatically, using non-cyclic elementary subgroups, inside 'Irr').
gap> CCTmax:= CCTable( Gmax24 );;
gap> ImportInducedFromAllMaximalCyclicToCCTable( CCTmax );;
gap> HasFullRankCCTable( CCTmax );
true
gap> StringCollectedFactors( FindIndexCCTable( CCTmax ) );
"2^42 3^2"
gap> ImportToCCTable( CCTmax, NaturalCharacters( Gmax24 ) );;
gap> ImportToCCTable( CCTmax, SmallPowerMapCharacters( Gmax24 ) );;
gap> UpdateHNFCCTable( CCTmax );
294912
gap> StringCollectedFactors( FindIndexCCTable( CCTmax ) );
"2^27"
gap> irmax:= Irr( CCTmax );;
gap> Length( irmax ) = NrConjugacyClasses( Gmax24 );
true
gap> tmax := CharacterTable( Gmax24 );; Length(Irr(tmax));
33
gap> IsInternallyConsistent( tmax );
true
gap> TransformingPermutationsCharacterTables( tmax, CharacterTable( "2^6:3.s6" ) )
>        <> fail;
true

##  'SplitByCentre', 'SplittingCentre', 'SplitEncodedCharacterByCentre':
##  for 'GSL313' = SL(3,13) the centre has order gcd(3,13-1) = 3; every
##  irreducible character must be "pure" for exactly one irreducible
##  character of the (chosen) central subgroup.
gap> CCTsl:= CCTable( GSL313 );;
gap> SplitByCentre( CCTsl );;
gap> HasSplittingCentre( CCTsl );
true
gap> SplittingCentre( CCTsl );
[ 1, 6, 11 ]
gap> irsl:= Irr( CCTsl );;
gap> Length( irsl ) = NrConjugacyClasses( GSL313 );
true
gap> tsl := CharacterTable( GSL313 );; Length(Irr(tsl));
190
gap> IsInternallyConsistent( tsl );
true
gap> AllPureCentre:= function( CCT, irr )
>     local ch, r;
>     for ch in irr do
>       r := SplitEncodedCharacterByCentre( CCT, ch );
>       if Number( [ 1 .. Length( r ) ], i-> IsBound( r[i] ) ) <> 1 then
>         return false;
>       fi;
>     od;
>     return true;
>   end;;
gap> AllPureCentre( CCTsl, irsl );
true

##  'NaturalCharacters' for a matrix group over a finite field (three
##  characters: permutation characters on non-zero vectors over the field
##  and its quadratic extension, and on one dimensional subspaces).
gap> ncsl:= NaturalCharacters( GSL313 );;
gap> Length( ncsl );
3
gap> encnc:= EncodeForCCTable( CCTsl, ncsl );;
gap> ForAll( encnc, v-> ForAll( irsl, ch-> IsInt( ScalarProduct( CCTsl, ch, v ) ) ) );
true

##  'GPSL313' = PSL(3,13): direct consistency check and delegated
##  attributes, without a comparison with the character table library
##  (this table is not contained in the library).
gap> CCTpsl:= CCTable( GPSL313 );;
gap> NrRationalClasses( GPSL313 ) = NrRationalClasses( CCTpsl );
true
gap> tpsl := CharacterTable( GPSL313 );; Length(Irr(tpsl));
64
gap> IsInternallyConsistent( tpsl );
true

##  'MaximalNonCyclicElementarySubgroups', 'InducedFromElementary',
##  'InductionDataFromElementaryCCTable': induced (generalized) characters
##  from non-cyclic elementary subgroups.
gap> G42:= SL( 4, 2 );;
gap> CCT42:= CCTable( G42 );;
gap> ir42:= Irr( CCT42 );;
gap> mnc:= MaximalNonCyclicElementarySubgroups( G42 );
[ [ 1, 3 ], [ 1, 2 ], [ 6, 2 ] ]
gap> inde:= EncodeForCCTable( CCT42, InducedFromElementary( G42, mnc[1][1], mnc[1][2] ) );;
gap> ForAll( inde, v-> ForAll( ir42, ch-> IsInt( ScalarProduct( CCT42, ch, v ) ) ) );
true
gap> idat:= InductionDataFromElementaryCCTable( CCT42, mnc[1][1], mnc[1][2] );;
gap> AllGenElementary:= function( idat, CCT, irr )
>     local v;
>     v:= idat.next();
>     while v <> fail do
>       if not ForAll( v, w-> ForAll( irr, ch-> IsInt( ScalarProduct( CCT, ch, w ) ) ) ) then
>         return false;
>       fi;
>       v:= idat.next();
>     od;
>     return true;
>   end;;
gap> AllGenElementary( idat, CCT42, ir42 );
true

##  'ActionAutomorphismsOnConjugacyClasses', 'ActionAutomorphismsOnRationalClasses':
##  'SymmetricGroup(6)' has an outer automorphism, so its automorphism
##  group interchanges some (rational) classes.
gap> AutS6:= AutomorphismGroup( SymmetricGroup( 6 ) );;
gap> Size( ActionAutomorphismsOnConjugacyClasses( SymmetricGroup( 6 ), AutS6 ) );
2
gap> Size( ActionAutomorphismsOnRationalClasses( SymmetricGroup( 6 ), AutS6 ) );
2

##  'EncodeForCCTable' / 'ExpandFromCCTable': pure roundtrip, and roundtrip
##  via 'InducedFromAllMaximalCyclicSubgroups' (cyclotomic character values).
gap> enc:= EncodeForCCTable( CCT, ExpandFromCCTable( CCT, ir ) );;
gap> enc = ir;
true
gap> indA5:= InducedFromAllMaximalCyclicSubgroups( GA5 );;
gap> ExpandFromCCTable( CCT, EncodeForCCTable( CCT, indA5 ) ) = indA5;
true

##  The plain &GAP; implementations of the FLINT-based standalone programs
##  ('..._GAP' variants of functions in 'LLL.gi') must agree with the
##  (possibly multithreaded, standalone) default versions. This loop only
##  produces output if a mismatch is found.
gap> for n in [ 4, 7, 100 ] do
>     A:= RandomUnimodularMat( n );
>     gr:= A * TransposedMat( A );
>     if PermutedFractionFreeIntegerGaussPositiveDefinite_GAP( gr )
>            <> PermutedFractionFreeIntegerGaussPositiveDefinite( gr ) then
>       Print( "MISMATCH PermutedFractionFreeIntegerGaussPositiveDefinite, n=", n, "\n" );
>     fi;
>     if InverseUnimodularMat_GAP( A ) <> InverseUnimodularMat( A ) then
>       Print( "MISMATCH InverseUnimodularMat, n=", n, "\n" );
>     fi;
>     if not IsOne( A * InverseUnimodularMat( A ) ) then
>       Print( "WRONG InverseUnimodularMat, n=", n, "\n" );
>     fi;
>     H1:= LLLTransformUnimodularGram_GAP( gr );
>     H2:= LLLTransformUnimodularGram( gr );
>     if not IsOne( H1*gr*TransposedMat( H1 ) )
>            or not IsOne( H2*gr*TransposedMat( H2 ) ) then
>       Print( "WRONG LLLTransformUnimodularGram, n=", n, "\n" );
>     fi;
>     if HermiteNormalFormIntegerMat( A ) <> HermiteIntMat( A ) then
>       Print( "MISMATCH HermiteIntMat, n=", n, "\n" );
>     fi;
>   od;

##  Test for 'AddVectorToHNF'.
gap> h := [ [ 6, 82, 36, 28, 0, 12 ], [ 0, 238, 98, 84, 0, 42 ],
>         [ 0, 0, 0, 0, 28, 0 ] ];
[ [ 6, 82, 36, 28, 0, 12 ], [ 0, 238, 98, 84, 0, 42 ], 
  [ 0, 0, 0, 0, 28, 0 ] ]
gap> piv := [1,2,5];
[ 1, 2, 5 ]
gap> AddVectorToHNF(h, piv, [ 270, 18, 108, -36, -46, -108 ]);
14
gap> h;
[ [ 6, 14, 8, 4, -12, 0 ], [ 0, 34, 14, 12, 6, 6 ], 
  [ 0, 0, 0, 0, 14, 0 ] ]

##
gap> STOP_TEST( "cctab.tst", 10000000 );
gap> SizeScreen( save );;

#############################################################################
##
#E
