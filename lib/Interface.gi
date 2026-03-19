###########################################################################
##  Interface.gi
##  
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  
##  These files connect functionality of this package with the GAP library,
##  in particular the operations 'Irr' for groups and character tables 
##  and 'PowerMap(tab, n)'.
##  

# We overwrite the library method for initializing a character table.
# We use the CCTable and RationalClassesInfo to find a good ordering
# of the conjugacy classes.
InstallOtherMethod(OrdinaryCharacterTable, ["IsGroup"],
function( G )
  local CCT, tbl, ccl, rcl, bijection;

  if IsSupersolvable(G) then
    TryNextMethod();
  fi;

  CCT := CCTable(G);

  # Make the object.
  tbl:= Objectify( NewType( NearlyCharacterTablesFamily,
                            IsOrdinaryTable and IsAttributeStoringRep ),
                   rec() );

  # Store the attribute values of the interface.
  SetUnderlyingGroup( tbl, G );
  SetUnderlyingCharacteristic( tbl, 0 );
  SetCCTable( tbl, CCT );
  IsFinite(G);
  ccl:= ConjugacyClasses( G );
  rcl := RationalClassesInfo(CCT);
  bijection := Concatenation(List(rcl, a-> a.classes));
  ccl := ccl{bijection};
  SetConjugacyClasses( tbl, ccl );
  SetIdentificationOfConjugacyClasses( tbl, bijection );

  return tbl;
end );

InstallOtherMethod(Irr, ["IsOrdinaryTable and HasCCTable"],
function(ct)
  local CCT, ir, irr, perm, chs;
  CCT := CCTable(ct);
  ir := Irr(CCT);
  irr := ExpandFromCCTable(CCT, ir);
  perm := IdentificationOfConjugacyClasses(ct);
  chs := List(irr, l-> Character(ct, l{perm}));
  SetIrr(ct, chs);
  SetInfoText(ct, "origin: computed by CCTable");
  return chs;
end);

InstallMethod(Irr, ["IsGroup", "IsZeroCyc"], 
function(G, zero)
  local CCT, ir, irr, t, perm, chs;
  # test for a very efficient case
  if IsSupersolvable(G) then
    return IrrBaumClausen(G);
  fi;
  # otherwise use the default strategy from CCTable package
  CCT := CCTable(G);
  ir := Irr(CCT);
  irr := ExpandFromCCTable(CCT, ir);
  t := OrdinaryCharacterTable(G);
  perm := IdentificationOfConjugacyClasses(t);
  chs := List(irr, l-> Character(t, l{perm}));
  SetIrr(t, chs); 
  SetInfoText(t, "origin: computed by CCTable");
  return chs;
end);

BindGlobal("PowerMapByPowerMapsOfAllClasses", 
function(t, n)
  local CCT, ord, pm, perm, inv, res, j, nj, i;
  CCT := CCTable(t);
  ord := OrdersClassRepresentatives(CCT);
  pm := PowerMapsOfAllClasses(CCT);
  perm := IdentificationOfConjugacyClasses(t);
  inv := PermList(perm)^-1;
  res := [];
  for i in [1..Length(pm)] do
    j := perm[i];
    nj := (n mod ord[j]) + 1;
    Add(res, pm[j][nj]^inv);
  od;
  return res;
end);
InstallMethod(PowerMapOp,
             ["IsOrdinaryTable and HasUnderlyingGroup and HasCCTable", "IsInt"],
PowerMapByPowerMapsOfAllClasses);
InstallMethod(PowerMap,
             ["IsOrdinaryTable and HasUnderlyingGroup and HasCCTable", "IsInt"],
PowerMapByPowerMapsOfAllClasses);

