###########################################################################
##  LLL.gd
##  
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  Utilities for LLL reduction of integer lattices.
##  

# Configure number of threads for various standalone programs which 
# use the FLINT library and several threads.
NRFlintThreads := 8;

DeclareGlobalName("SMod");
DeclareGlobalName("SModList");
DeclareGlobalName("PrintIntegerMatToFlint");
DeclareGlobalName("HermiteIntMat");
DeclareGlobalName("HNFThreaded");
DeclareGlobalName("PermutedFractionFreeIntegerGaussPositiveDefinite");
DeclareGlobalName("PermutedFractionFreeIntegerGaussPositiveDefinite_GAP");
DeclareGlobalName("PFFIGThreaded");
DeclareGlobalName("InverseUnimodularMat");
DeclareGlobalName("InverseUnimodularMat_GAP");
DeclareGlobalName("InvUniThreaded");
DeclareGlobalName("LLLTransformUnimodularGram");
DeclareGlobalName("LLLTransformUnimodularGram_GAP");
DeclareGlobalName("LLLTUGIT");


##  # removed, no longer needed?
##  DeclareGlobalName("LLLRecord");
##  DeclareGlobalName("AddVectorsLLLRecord");
##  DeclareGlobalName("AddGramLLLRecord");
##  DeclareGlobalName("ReduceLLLRecord");
##  DeclareGlobalName("CleanLLLRecord");

