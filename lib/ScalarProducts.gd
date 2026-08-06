###########################################################################
##  ScalarProducts.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to compute the scalar products of
##  generalized characters (Z-linear combinations of irreducible characters) 
##  of a finite group (also works for Q-linear combinations).
##  

DeclareAttribute("ScalarInfo", IsGroup);    
DeclareAttribute("ScalarInfo", IsCCTable);    

DeclareGlobalName("CCTScalarProduct");
    
