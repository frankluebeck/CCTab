###########################################################################
##  testall.g
##
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##
##  This file runs the tests of the CCTab package; it is also referred to
##  by the 'TestFile' entry in 'PackageInfo.g'. Run the tests with
##
##      make test
##
##  or, from within GAP, with 'TestPackage("CCTab");'.
##

##  'make test' is called in the package directory, which need not lie in one
##  of the GAP root directories; in that case we point GAP to it explicitly
if TestPackageAvailability("CCTab") = fail and
        IsReadableFile("PackageInfo.g") then
  SetPackagePath("CCTab", ".");
fi;

if LoadPackage("CCTab") <> true then
  Print("#I  cannot load the CCTab package, no tests were run\n");
  FORCE_QUIT_GAP(1);
fi;

##  the package sets this to a positive value while it is under development,
##  but for the tests we do not want to see the progress reports
SetInfoLevel(InfoCCTable, 0);

TestDirectory(DirectoriesPackageLibrary("CCTab", "tst"),
              rec(exitGAP := true));

FORCE_QUIT_GAP(1);   # only reached if 'TestDirectory' did not exit
