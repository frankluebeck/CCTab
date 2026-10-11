###########################################################################
##  SomeCharacters.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contain functions to compute some (generalized) characters
##  of finite groups (some derived from already known ones).

DeclareAttribute("NaturalCharacters", IsGroup);

DeclareGlobalFunction ("pPrimeDecompositionPower");

DeclareAttribute( "pPrimeDecompositions", IsCharacterTable, "mutable" );
DeclareOperation( "pPrimeDecomposition", [ IsCharacterTable, IsPosInt ]  );
DeclareOperation( "pPrimeDecomposition", [ IsGroup, IsPosInt ]  );


DeclareGlobalFunction ("pPrimeCharacter");
DeclareGlobalFunction ("pPrimeRestriction");
