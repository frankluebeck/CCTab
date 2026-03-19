#############################################################################
##  
##  PackageInfo.g for the package 'CCTab'
##                                                            
##  (C) 2025 Frank Lübeck (Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen)
##

SetPackageInfo( rec(

PackageName := "CCTab",
Subtitle := "Constructing character tables",
Version := "0.3.dev",
Date := "02/09/2025", # dd/mm/yyyy format
License := "GPL-3.0-or-later",

Persons := [
  rec(
    IsAuthor := true,
    IsMaintainer := true,
    FirstNames := "Frank",
    LastName := "Lübeck",
    Email := "Frank.Luebeck@math.rwth-aachen.de",
    Place := "Aachen",
    Institution := "RWTH Aachen",
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/frankluebeck/CCTab",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),

PackageWWWHome :="https://TODO",

PackageInfoURL := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL     := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL     := Concatenation( ~.PackageWWWHome, "CCTab-", ~.Version ),

ArchiveFormats := ".tar.gz",

Status := "experimental",

AbstractHTML   :=  "Interactive and non-interactive construction of \
the ordinary character table of a finite group.",

PackageDoc := rec(
  BookName  := "CCTab",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Constructing character tables",
),

Dependencies := rec(
  GAP := ">= 4.14",
  NeededOtherPackages := [ [ "GAPDoc", ">= 1.5" ] ],
  SuggestedOtherPackages := [ ],
  ExternalConditions := [ ["libflint", ">= 3.1.3" ] ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

Keywords := [ ],

) );
