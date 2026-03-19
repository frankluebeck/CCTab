


DeclareOperation("SplitByCentre", [IsCCTable]);
DeclareOperation("SplitByCentre", [IsCCTable, IsList]);
DeclareAttribute("SplittingCentre", IsCCTable);
DeclareOperation("SplitCharacterByCentre", 
                        [IsCCTable and HasSplittingCentre, IsList]);
DeclareOperation("SplitEncodedCharacterByCentre", 
                        [IsCCTable and HasSplittingCentre, IsList]);
