###########################################################################
##  SplitByCentre.gd
##  
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  Orthogonal decomposition of the lattice of generalized characters
##  according to the characters of (a subgroup of) the center.
##  

DeclareOperation("SplitByCentre", [IsCCTable]);
DeclareOperation("SplitByCentre", [IsCCTable, IsList]);
DeclareAttribute("SplittingCentre", IsCCTable);
DeclareOperation("SplitCharacterByCentre", 
                        [IsCCTable and HasSplittingCentre, IsList]);
DeclareOperation("SplitEncodedCharacterByCentre", 
                        [IsCCTable and HasSplittingCentre, IsList]);
