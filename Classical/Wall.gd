#############################################################################
##
##  wall.gd   declarations for the conjugacy classes of finite classical
##            groups following G. E. Wall (1963)
##
##  Files:  wall.gd          declarations of all global names
##          wall.gi          implementation, with GAPDoc documentation of
##                           the API functions
##          wallmethods.gi   methods for GAP's classical groups (optional)
##  Load with  Read("wall.gd"); Read("wall.gi");  (in this order), then
##  optionally  Read("wallmethods.gi");
##
##  Public names start with Wall, internal ones with WALL_, WALL2_
##  (characteristic 2) and WALL3_ (conformal groups).
##
#############################################################################

## public functions (documented by GAPDoc sections in wall.gi)

#############################################################################
##  Forms and groups
#############################################################################
DeclareGlobalName( "WallClassicalForm" );
DeclareGlobalName( "WallFormOfGroup" );
DeclareGlobalName( "WallGroup" );
DeclareGlobalName( "WallConformalGroup" );
DeclareGlobalName( "WallIsInGroup" );
DeclareGlobalName( "WallGroupOrder" );
DeclareGlobalName( "WallFormIsometry" );
DeclareGlobalName( "IsomorphismSymplecticGroup" );

#############################################################################
##  Conjugacy classes of the isometry group G(F)
#############################################################################
DeclareGlobalName( "WallClassInvariants" );
DeclareGlobalName( "WallNrClasses" );
DeclareGlobalName( "WallInvariant" );
DeclareGlobalName( "WallDisplayInvariant" );
DeclareGlobalName( "WallRepresentative" );
DeclareGlobalName( "WallModel" );
DeclareGlobalName( "WallCentralizerOrder" );
DeclareGlobalName( "WallClassSize" );
DeclareGlobalName( "WallRepresentativeWithCentralizer" );
DeclareGlobalName( "WallCentralizerGenerators" );
DeclareGlobalName( "WallConjugatingElement" );
DeclareGlobalName( "WallIsConjugate" );
DeclareGlobalName( "WallCentralizer" );
DeclareGlobalName( "WallCertifyChar2" );

#############################################################################
##  Subgroups SO, Omega and SU
#############################################################################
DeclareGlobalName( "WallSpinorNorm" );
DeclareGlobalName( "WallSpinorNormOfInvariant" );
DeclareGlobalName( "WallDeterminantOfInvariant" );
DeclareGlobalName( "WallDicksonInvariant" );
DeclareGlobalName( "WallDicksonInvariantOfInvariant" );
DeclareGlobalName( "WallPiImageOfCentralizer" );
DeclareGlobalName( "WallIsInSubgroup" );
DeclareGlobalName( "WallSubgroupOrder" );
DeclareGlobalName( "WallSubgroupClassInvariants" );
DeclareGlobalName( "WallSubgroupNrClasses" );
DeclareGlobalName( "WallSubgroupInvariant" );
DeclareGlobalName( "WallSubgroupRepresentative" );
DeclareGlobalName( "WallSubgroupRepresentativeWithCentralizer" );
DeclareGlobalName( "WallSubgroupConjugatingElement" );
DeclareGlobalName( "WallSubgroupCentralizerOrder" );
DeclareGlobalName( "WallSubgroupClassSize" );

#############################################################################
##  Conformal groups
#############################################################################
DeclareGlobalName( "WallMultiplier" );
DeclareGlobalName( "WallConformalMultiplier" );
DeclareGlobalName( "WallConformalGroupOrder" );
DeclareGlobalName( "WallConformalClassInvariants" );
DeclareGlobalName( "WallConformalNrClasses" );
DeclareGlobalName( "WallConformalInvariant" );
DeclareGlobalName( "WallConformalRepresentative" );
DeclareGlobalName( "WallConformalRepresentativeWithCentralizer" );
DeclareGlobalName( "WallConformalConjugatingElement" );
DeclareGlobalName( "WallConformalCentralizer" );
DeclareGlobalName( "WallConformalCentralizerOrder" );
DeclareGlobalName( "WallConformalClassSize" );

## internal functions
DeclareGlobalName( "WALL_Frob" );
DeclareGlobalName( "WALL_K" );
DeclareGlobalName( "WALL_KMat" );
DeclareGlobalName( "WALL_ExtField" );
DeclareGlobalName( "WALL_Star" );
DeclareGlobalName( "WALL_Leg" );
DeclareGlobalName( "WALL_Sqrt" );
DeclareGlobalName( "WALL_BlockDiag" );
DeclareGlobalName( "WALL_OrderGL" );
DeclareGlobalName( "WALL_OrderGU" );
DeclareGlobalName( "WALL_OrderSp" );
DeclareGlobalName( "WALL_OrderO" );
DeclareGlobalName( "WALL_CanonicalBaseChange" );
DeclareGlobalName( "WALL_DualCoeffs" );
DeclareGlobalName( "WALL_PolString" );
DeclareGlobalName( "WALL_SignData" );
DeclareGlobalName( "WALL_Partition" );
DeclareGlobalName( "WALL_MakeInvariant" );
DeclareGlobalName( "WALL_Mults" );
DeclareGlobalName( "WALL_E2" );
DeclareGlobalName( "WALL_SeriesMul" );
DeclareGlobalName( "WALL_SeriesGeom" );
DeclareGlobalName( "WALL_SeriesBinom" );
DeclareGlobalName( "WALL_OrbitOf" );
DeclareGlobalName( "WALL_Atoms" );
DeclareGlobalName( "WALL_PlusMinusOptions" );
DeclareGlobalName( "WALL_DetClassOfInvariant" );
DeclareGlobalName( "WALL_LambdaData" );
DeclareGlobalName( "WALL_Realize" );
DeclareGlobalName( "WALL_RealizeForm" );
DeclareGlobalName( "WALL_Shift" );
DeclareGlobalName( "WALL_Delta" );
DeclareGlobalName( "WALL_Cayley" );
DeclareGlobalName( "WALL_SelfDualComponent" );
DeclareGlobalName( "WALL_PairComponent" );
DeclareGlobalName( "WALL_LeviPartGens" );
DeclareGlobalName( "WALL_RadicalBasis" );
DeclareGlobalName( "WALL_PrimeBasis" );
DeclareGlobalName( "WALL_FixedFieldCoords" );
DeclareGlobalName( "WALL_FromFixedFieldCoords" );
DeclareGlobalName( "WALL_UnipotentGensL" );
DeclareGlobalName( "WALL_LeviGensL" );
DeclareGlobalName( "WALL_RealizeCentralizing" );
DeclareGlobalName( "WALL_Embed" );
DeclareGlobalName( "WALL_PartName" );
DeclareGlobalName( "WALL_RepWithCentFromModel" );
DeclareGlobalName( "WALL_LambdaAct" );
DeclareGlobalName( "WALL_LambdaStructure" );
DeclareGlobalName( "WALL_HFromF" );
DeclareGlobalName( "WALL_StarL" );
DeclareGlobalName( "WALL_Tops" );
DeclareGlobalName( "WALL_PartFormRecord" );
DeclareGlobalName( "WALL_AdaptedSelfDual" );
DeclareGlobalName( "WALL_AdaptedPair" );
DeclareGlobalName( "WALL_ComponentRows" );
DeclareGlobalName( "WALL_PiS" );
DeclareGlobalName( "WALL_PiMul" );
DeclareGlobalName( "WALL_PiClosure" );
DeclareGlobalName( "WALL_CheckS" );
DeclareGlobalName( "WALL_ProjS" );
DeclareGlobalName( "WALL_Labels" );
DeclareGlobalName( "WALL_LabelOf" );
DeclareGlobalName( "WALL_PiElements" );
DeclareGlobalName( "WALL_ElementWithPi" );
DeclareGlobalName( "WALL_KernelGens" );
DeclareGlobalName( "WALL_SUOmega" );
DeclareGlobalName( "WALL_SUDetExp" );
DeclareGlobalName( "WALL_SUDetExpOfInvariant" );
DeclareGlobalName( "WALL_SUGcd" );
DeclareGlobalName( "WALL_SUIsInSubgroup" );
DeclareGlobalName( "WALL_SUOrder" );
DeclareGlobalName( "WALL_SUClassInvariants" );
DeclareGlobalName( "WALL_SUCentralizerOrder" );
DeclareGlobalName( "WALL_SUElementWithDet" );
DeclareGlobalName( "WALL_SUKernelGens" );
DeclareGlobalName( "WALL_SURepresentativeWithCentralizer" );
DeclareGlobalName( "WALL_SURepresentative" );
DeclareGlobalName( "WALL_SUConjugatingElement" );
DeclareGlobalName( "WALL2_Tr2" );
DeclareGlobalName( "WALL2_Form" );
DeclareGlobalName( "WALL2_SOf" );
DeclareGlobalName( "WALL2_ComponentSets" );
DeclareGlobalName( "WALL2_DeltaFree" );
DeclareGlobalName( "WALL2_UnipotentOptions" );
DeclareGlobalName( "WALL2_OptionArf" );
DeclareGlobalName( "WALL2_MakeInvariant" );
DeclareGlobalName( "WALL2_ClassInvariants" );
DeclareGlobalName( "WALL2_NrClasses" );
DeclareGlobalName( "WALL2_UnipotentCentralizerOrder" );
DeclareGlobalName( "WALL2_CentralizerOrder" );
DeclareGlobalName( "WALL2_Piece" );
DeclareGlobalName( "WALL2_PartPieces" );
DeclareGlobalName( "WALL2_HasParam" );
DeclareGlobalName( "WALL2_DesignatedPart" );
DeclareGlobalName( "WALL2_ParamsFromLabels" );
DeclareGlobalName( "WALL2_UnipotentPieces" );
DeclareGlobalName( "WALL2_SumPieces" );
DeclareGlobalName( "WALL2_SBits" );
DeclareGlobalName( "WALL2_Invariant" );
DeclareGlobalName( "WALL2_StdAniso" );
DeclareGlobalName( "WALL2_CanonicalQuad" );
DeclareGlobalName( "WALL2_FormIsometry" );
DeclareGlobalName( "WALL2_InducedQuad" );
DeclareGlobalName( "WALL2_Model" );
DeclareGlobalName( "WALL2_Representative" );
DeclareGlobalName( "WALL2_Sqrt" );
DeclareGlobalName( "WALL2_Bits" );
DeclareGlobalName( "WALL2_PieceIsometry" );
DeclareGlobalName( "WALL2_UnipotentAdapted" );
DeclareGlobalName( "WALL2_ConjugatingElement" );
DeclareGlobalName( "WALL2_Group" );
DeclareGlobalName( "WALL2_CentralizerCapped" );
DeclareGlobalName( "WALL2_RepresentativeWithCentralizer" );
DeclareGlobalName( "WALL3_TwistedForm" );
DeclareGlobalName( "WALL3_IsSimilitude" );
DeclareGlobalName( "WALL3_SpecialLD" );
DeclareGlobalName( "WALL3_SpecialSigns" );
DeclareGlobalName( "WALL3_Invariant" );
DeclareGlobalName( "WALL3_Atoms" );
DeclareGlobalName( "WALL3_DetClass" );
DeclareGlobalName( "WALL3_SpecialOptions" );
DeclareGlobalName( "WALL3_ClassInvariants" );
DeclareGlobalName( "WALL3_CentralizerOrder" );
DeclareGlobalName( "WALL3_SpecialComponent" );
DeclareGlobalName( "WALL3_Model" );
DeclareGlobalName( "WALL3_Representative" );
DeclareGlobalName( "WALL3_ConjugatingElement" );
DeclareGlobalName( "WALL3_ConfKind" );
DeclareGlobalName( "WALL3_MultGen" );
DeclareGlobalName( "WALL3_ScalarFactor" );
DeclareGlobalName( "WALL3_ScalarPart" );
DeclareGlobalName( "WALL3_Delta" );
DeclareGlobalName( "WALL3_DeltaImage" );
DeclareGlobalName( "WALL3_FusionCanonical" );
DeclareGlobalName( "WALL2_QuotientData" );
DeclareGlobalName( "WALL2_IsIrredAS" );
DeclareGlobalName( "WALL2_BlockBeta" );
DeclareGlobalName( "WALL2_UnipotentLabelsDLO" );
DeclareGlobalName( "WALL2_LSCentralizerOrder" );
DeclareGlobalName( "WALL2_OddForm" );
DeclareGlobalName( "WALL2_OddImage" );
DeclareGlobalName( "WALL2_OddPreImage" );
DeclareGlobalName( "WALL2_OddGroup" );
DeclareGlobalName( "WALL2_OddConjugatingElement" );
DeclareGlobalName( "WALL2_OddRepresentativeWithCentralizer" );
DeclareGlobalName( "WALL_SetFormAttributes" );

## used by wallmethods.gi
DeclareGlobalName( "WALL_KnownTrue" );
DeclareGlobalName( "WALL_FormOfClassicalGroup" );
DeclareGlobalName( "WALL_NrConjugacyClassesIsometryGroup" );
DeclareGlobalName( "WALL_ClassesFromInvariants" );
DeclareGlobalName( "WALL_ConjugacyClassesIsometryGroup" );
DeclareGlobalName( "WALL_ClassicalGroupData" );
DeclareAttribute( "WallClassicalGroupData", IsGroup, "mutable" );
DeclareAttribute( "WallClassInvariant", IsConjugacyClassGroupRep );
DeclareGlobalName( "WALL_IsInClassicalGroup" );
DeclareGlobalName( "WALL_ConjugatingData" );
DeclareGlobalName( "WALL_ClassInvariant" );
DeclareGlobalName( "WALL_RepWithCentralizer" );
DeclareGlobalName( "WALL_CentralizerInClassicalGroup" );
DeclareGlobalName( "WALL_IsConjugateMethod" );
DeclareGlobalName( "WALL_RepresentativeActionMethod" );
DeclareGlobalName( "WALL_CentralizerOpMethod" );
