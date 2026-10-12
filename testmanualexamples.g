##  this runs the examples in the manual and shows where their output
##  differs from the documented one, needs: GAPDoc package

LoadPackage("CCTab");
LoadPackage("GAPDoc");
# the example for PowerMapsOfAllClasses uses a library table
LoadPackage("ctbllib");
exs := ExtractExamples("doc", "cctab.xml", ["../lib/PowerMaps.gi", "../lib/Elementary.gi",
    "../lib/PositionConjugacyClass.gi", "../lib/ScalarProducts.gi",
    "../lib/SomeCharacters.gi", "../lib/SplitByCentre.gi",
    "../lib/CCTable.gi", "../lib/LLL.gi"], "Chapter", true);

RunExamples(exs);

# RunExamples(exs,rec(compareFunction := "uptowhitespace"));

# RunExamples(exs,rec(changeSources:=true));

#QUIT;
