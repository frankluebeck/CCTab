##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex

# substitute this by path to main GAP directory, if this package is not
# in standard location
if IsBound(pathtoroot) then
  relpath := pathtoroot;
else
  relpath:="../../..";
fi;
LoadPackage("GAPDoc");
MakeGAPDocDoc("doc", "cctab", ["../lib/PowerMaps.gi"], "CCTab", relpath, "MathJax");
GAPDocManualLab("CCTab");
CopyHTMLStyleFiles("doc");
QUIT;
