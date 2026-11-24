###########################################################################
##  SomeCharacters.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contain functions to compute some (generalized) characters
##  of finite groups (some derived from already known ones).

DeclareAttribute("NaturalCharacters", IsGroup);

DeclareGlobalFunction ("PPrimeDecompositionPower");

DeclareAttribute( "PPrimeDecompositions", IsCharacterTable, "mutable" );
DeclareOperation( "PPrimeDecomposition", [ IsCharacterTable, IsPosInt ]  );
DeclareOperation( "PPrimeDecomposition", [ IsGroup, IsPosInt ]  );


DeclareGlobalFunction ("PPrimeCharacter");
DeclareGlobalFunction ("PPrimeRestriction");
