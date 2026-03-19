###########################################################################
##  PowerMaps.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to find all power maps of the conjugacy
##  classes of a finite group.
##  

DeclareAttribute("PowerMapsOfAllClasses", IsGroup);

# missing in GAP library
DeclareAttribute("NrRationalClasses", IsGroup);

# class positions of rational classes
DeclareAttribute("RationalClassSets", IsGroup);

# more detailed information about rational classes
DeclareAttribute("RatClassExps", IsGroup);
DeclareGlobalName("RatPartVec");
DeclareAttribute("RationalClassesInfo", IsGroup);    

DeclareAttribute("MaximalCyclics", IsGroup);

DeclareGlobalName("InduceAllFromCyclicSubgroup");
DeclareGlobalName("InducedFromAllMaximalCyclicSubgroups");

DeclareGlobalName("PowerMapCharacters");
DeclareGlobalName("SmallPowerMapCharacters");

DeclareGlobalName("ActionAutomorphismsOnConjugacyClasses");
DeclareGlobalName("ActionAutomorphismsOnRationalClasses");
