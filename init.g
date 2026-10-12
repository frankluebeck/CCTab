##  (C) 2025 Frank Lübeck (Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen)
##  
##  Read declaration files of the 'CCTab' package
##  

ReadPackage( "CCTab", "lib/CCTable.gd");
ReadPackage( "CCTab", "lib/PositionConjugacyClass.gd");
ReadPackage( "CCTab", "lib/PowerMaps.gd");
ReadPackage( "CCTab", "lib/SomeCharacters.gd");
ReadPackage( "CCTab", "lib/Elementary.gd");
ReadPackage( "CCTab", "lib/ScalarProducts.gd");
ReadPackage( "CCTab", "lib/LLL.gd");
ReadPackage( "CCTab", "lib/SplitByCentre.gd");

if (not IsBound(CCTScalarProductInternal)) and
        IsKernelExtensionAvailable("CCTab","scalar") then
  LoadKernelExtension("CCTab", "scalar");
fi;
