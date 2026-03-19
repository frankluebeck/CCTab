###########################################################################
##  CCTable.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to create a CCTable for a finite group.
##  This will be used as a container for computing the irreducible characters
##  of the group without using 'CharacterTable'.
##  

##  Filter for partial character tables that can be completed interactively
##  and with the Unger algorithm (induction from elementary subgroups and LLL
##  reduction).
DeclareFilter("IsCCTable", IsComponentObjectRep and IsAttributeStoringRep and IsNearlyCharacterTable);
DeclareAttribute("CCTable", IsGroup, "mutable");
BindGlobal("CCTableType", NewType(NearlyCharacterTablesFamily, IsCCTable));

# will be delegated to underlying group
DeclareAttribute("NrRationalClasses", IsNearlyCharacterTable);
DeclareAttribute("RatClassExps", IsNearlyCharacterTable);
DeclareAttribute("RationalClassesInfo", IsNearlyCharacterTable);    

DeclareGlobalName("EncodeForCCTable");
DeclareGlobalName("ImportToCCTable");
DeclareGlobalName("ExpandFromCCTable");
DeclareGlobalName("HasFullRankCCTable");
DeclareGlobalName("AddVectorToHNF");
DeclareGlobalName("UpdateHNFCCTable");

DeclareGlobalName("ImportInducedFromAllMaximalCyclicToCCTable");
DeclareGlobalName("FindIndexCCTable");

DeclareGlobalName("ExtendLLLCCTable");
DeclareGlobalName("ReduceCCTable");
DeclareGlobalName("DeterminantGramCCTable");

# Info class
DeclareInfoClass("InfoCCTable");
# during development
SetInfoLevel(InfoCCTable, 4);
