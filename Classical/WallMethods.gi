#############################################################################
##  WallMethods.gi
##
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##
##  Methods for GAP's classical groups, based on the functions in
##  Wall.gd / Wall.gi.
##
##  The type of a group is recognized by the filters of the GAP library:
##    IsFullSubgroupGLorSLRespectingBilinearForm       Sp, GO, SO (q odd)
##    IsFullSubgroupGLorSLRespectingQuadraticForm      GO, SO
##    IsFullSubgroupGLRespectingBilinearFormUpToScalars  CSp
##    IsFullSubgroupGLorSLRespectingSesquilinearForm   GU, SU
##    IsSubgroupSL                                     distinguishes SO from GO
##                                                     and SU from GU
##    IsNaturalGL, IsNaturalSL                         GL, SL (no form)
##    HasWallSpinData                                  spin groups from
##                                                     WallSpinGroup / Spin
##  Methods: NrConjugacyClasses (not for GU, SU, GL, SL: GAP's own fast
##  methods are used; for spin groups via the generating function),
##  ConjugacyClasses, Centralizer (via CentralizerOp),
##  IsConjugate, RepresentativeAction (via RepresentativeActionOp, for
##  OnPoints = conjugation).  For elements not in G the next method is used.
##  Membership in conjugacy classes: classes store their invariant in the
##  attribute WallClassInvariant (set by ConjugacyClasses, computed on
##  demand otherwise); if it is known, x in cl compares invariants (for
##  other classes GAP uses RepresentativeAction, i.e., the method above).
##
#############################################################################

# true if the property is known and true (these properties have no
# general method to compute them)
BindGlobal( "WALL_KnownTrue", function( prop, G )
  return Tester( prop )( G ) and prop( G );
end );

# the form record of a group with one of the filters above, or fail
BindGlobal( "WALL_FormOfClassicalGroup", function( G )
  local frm, F, K, conformal, quad;
  conformal := false;
  # only matrices over finite fields (e.g. not SL(2, Integers mod 4))
  if not IsFFECollColl( G ) then return fail; fi;
  if WALL_KnownTrue( IsNaturalGL, G ) or WALL_KnownTrue( IsNaturalSL, G ) then
    return WallClassicalForm( "L", DimensionOfMatrixGroup( G ), DefaultFieldOfMatrixGroup( G ) );
  fi;
  if WALL_KnownTrue( IsFullSubgroupGLorSLRespectingSesquilinearForm, G ) then
    frm := InvariantSesquilinearForm( G );
    if IsBound( frm.baseDomain ) then K := frm.baseDomain;
    else
      K := DefaultFieldOfMatrixGroup( G );
      if IsOddInt( DegreeOverPrimeField( K ) ) then
        K := GF( Characteristic( K ), 2 * DegreeOverPrimeField( K ) );
      fi;
    fi;
    return WallClassicalForm( "U", frm.matrix, K );
  fi;
  quad := WALL_KnownTrue( IsFullSubgroupGLorSLRespectingQuadraticForm, G );
  if quad then
    frm := InvariantQuadraticForm( G );
  elif WALL_KnownTrue( IsFullSubgroupGLorSLRespectingBilinearForm, G ) then
    frm := InvariantBilinearForm( G );
  elif WALL_KnownTrue( IsFullSubgroupGLRespectingBilinearFormUpToScalars, G ) then
    frm := InvariantBilinearFormUpToScalars( G ); conformal := true;
  else
    return fail;
  fi;
  F := frm.matrix;
  if IsBound( frm.baseDomain ) then K := frm.baseDomain;
  else K := DefaultFieldOfMatrixGroup( G ); fi;
  if quad then
    if IsEvenInt( Size( K ) ) then return WallClassicalForm( "O", F, K ); fi;
    # q odd: use the symmetric bilinear form
    return WallClassicalForm( "O", InvariantBilinearForm( G ).matrix, K );
  fi;
  if TransposedMat( F ) = -F and ForAll( [ 1 .. Length( F ) ], i -> IsZero( F[ i ][ i ] ) ) then
    return WallClassicalForm( "Sp", F, K );
  fi;
  if not conformal and IsOddInt( Size( K ) ) and TransposedMat( F ) = F then
    return WallClassicalForm( "O", F, K );
  fi;
  return fail;
end );

#############################################################################
##  NrConjugacyClasses
#############################################################################

# isometry groups Sp, GO and (q odd) SO: Wall's generating functions for
# Sp and GO, enumeration of the invariants for SO
BindGlobal( "WALL_NrConjugacyClassesIsometryGroup", function( G )
  local f;
  f := WALL_FormOfClassicalGroup( G );
  if f = fail then TryNextMethod(); fi;
  if f.type = "O" and not IsBound( f.char2 ) and IsSubgroupSL( G ) then
    return WallSubgroupNrClasses( f, "SO" );
  fi;
  return WallNrClasses( f );
end );

InstallMethod( NrConjugacyClasses,
  "for Sp, GO, SO (q odd) via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingBilinearForm ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_NrConjugacyClassesIsometryGroup );

InstallMethod( NrConjugacyClasses,
  "for GO, SO via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingQuadraticForm ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_NrConjugacyClassesIsometryGroup );

# conformal symplectic groups: enumeration of the invariants
InstallMethod( NrConjugacyClasses,
  "for CSp via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLRespectingBilinearFormUpToScalars ],
  RankFilter( IsHandledByNiceMonomorphism ),
  function( G )
    local f;
    f := WALL_FormOfClassicalGroup( G );
    if f = fail then TryNextMethod(); fi;
    return WallConformalNrClasses( f );
  end );

#############################################################################
##  ConjugacyClasses
#############################################################################

# classes of G from a list of invariants, a representative function and a
# class size function; the class of the identity comes first
BindGlobal( "WALL_ClassesFromInvariants", function( G, K, invs, repfun, sizefun )
  local res, one, inv, x, cl, pos;
  res := [];
  one := One( G );
  for inv in invs do
    x := ImmutableMatrix( K, repfun( inv ) );
    cl := ConjugacyClass( G, x );
    SetSize( cl, sizefun( inv ) );
    SetWallClassInvariant( cl, inv );
    Add( res, cl );
  od;
  pos := PositionProperty( res, cl -> IsOne( Representative( cl ) ) );
  if pos <> 1 then res := Concatenation( [ res[ pos ] ], res{ Difference( [ 1 .. Length( res ) ], [ pos ] ) } ); fi;
  return res;
end );

BindGlobal( "WALL_ConjugacyClassesIsometryGroup", function( G )
  local f;
  f := WALL_FormOfClassicalGroup( G );
  if f = fail then TryNextMethod(); fi;
  if f.type = "O" and not IsBound( f.char2 ) and IsSubgroupSL( G ) then
    return WALL_ClassesFromInvariants( G, f.field, WallSubgroupClassInvariants( f, "SO" ),
             inv -> WallSubgroupRepresentative( f, "SO", inv ),
             inv -> WallSubgroupClassSize( f, "SO", inv ) );
  fi;
  return WALL_ClassesFromInvariants( G, f.field, WallClassInvariants( f ),
           inv -> WallRepresentative( f, inv ), inv -> WallClassSize( f, inv ) );
end );

InstallMethod( ConjugacyClasses,
  "for Sp, GO, SO (q odd) via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingBilinearForm ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_ConjugacyClassesIsometryGroup );

InstallMethod( ConjugacyClasses,
  "for GO, SO via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingQuadraticForm ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_ConjugacyClassesIsometryGroup );

InstallMethod( ConjugacyClasses,
  "for CSp via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLRespectingBilinearFormUpToScalars ],
  RankFilter( IsHandledByNiceMonomorphism ),
  function( G )
    local f;
    f := WALL_FormOfClassicalGroup( G );
    if f = fail then TryNextMethod(); fi;
    return WALL_ClassesFromInvariants( G, f.field, WallConformalClassInvariants( f ),
             ci -> WallConformalRepresentative( f, ci ), ci -> WallConformalClassSize( f, ci ) );
  end );

# unitary groups GU, SU
InstallMethod( ConjugacyClasses,
  "for GU, SU via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingSesquilinearForm ],
  RankFilter( IsHandledByNiceMonomorphism ),
  function( G )
    local f;
    f := WALL_FormOfClassicalGroup( G );
    if f = fail then TryNextMethod(); fi;
    if IsSubgroupSL( G ) then
      return WALL_ClassesFromInvariants( G, f.field, WallSubgroupClassInvariants( f, "SU" ),
               inv -> WallSubgroupRepresentative( f, "SU", inv ),
               inv -> WallSubgroupClassSize( f, "SU", inv ) );
    fi;
    return WALL_ClassesFromInvariants( G, f.field, WallClassInvariants( f ),
             inv -> WallRepresentative( f, inv ), inv -> WallClassSize( f, inv ) );
  end );

# GL, SL
BindGlobal( "WALL_ConjugacyClassesGLSL", function( G )
  local d, f;
  d := WALL_ClassicalGroupData( G );
  if d = fail then TryNextMethod(); fi;
  f := d.f;
  if d.kind = "SL" then
    return WALL_ClassesFromInvariants( G, f.field, WallSubgroupClassInvariants( f, "SL" ),
             inv -> WallSubgroupRepresentative( f, "SL", inv ),
             inv -> WallSubgroupClassSize( f, "SL", inv ) );
  fi;
  return WALL_ClassesFromInvariants( G, f.field, WallClassInvariants( f ),
           inv -> WallRepresentative( f, inv ), inv -> WallClassSize( f, inv ) );
end );

InstallMethod( ConjugacyClasses, "for GL via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsNaturalGL ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_ConjugacyClassesGLSL );

InstallMethod( ConjugacyClasses, "for SL via Wall's classification",
  [ IsMatrixGroup and IsFinite and IsNaturalSL ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_ConjugacyClassesGLSL );

#############################################################################
##  Centralizer( G, x )   (via CentralizerOp)
#############################################################################

# the form record of G and the kind of group: "G" (isometry group),
# "SO", "SU" (q odd resp. unitary: functions WallSubgroup...) or
# "conformal"; fail if G is not recognized.  Cached in the attribute
# WallClassicalGroupData.
BindGlobal( "WALL_ClassicalGroupData", function( G )
  if not IsMatrixGroup( G ) then return fail; fi;
  return WallClassicalGroupData( G );
end );

##
##  <#GAPDoc Label="WallClassicalGroupData">
##  <ManSection>
##  <Attr Name="WallClassicalGroupData" Arg="G"/>
##  <Returns>a record or <K>fail</K></Returns>
##  <Description>
##  For a matrix group <A>G</A> recognized as a
##  classical group by the filters of the &GAP; library (for example
##  <C>IsFullSubgroupGLorSLRespectingBilinearForm</C>), returns
##  <C>rec( f, kind )</C> with the form record <C>f</C> and <C>kind</C> one of
##  <C>"G"</C> (isometry group, or <M>GL</M>), <C>"SO"</C>, <C>"SU"</C>,
##  <C>"SL"</C> or <C>"conformal"</C>; otherwise <K>fail</K>. For a spin group
##  from <Ref Func="WallSpinGroup" Label="for type, dimension, q"/> it is <C>rec( f, kind := "spin", group )</C>
##  with the form record <C>f</C> of the image <M>\Omega</M>. The groups
##  <C>GL(n,q)</C> and <C>SL(n,q)</C> are recognized by the properties
##  <C>IsNaturalGL</C> and <C>IsNaturalSL</C>. The value is mutable, since the
##  form record caches further data. The methods for <C>ConjugacyClasses</C>,
##  <C>NrConjugacyClasses</C>, <C>Centralizer</C>, <C>IsConjugate</C>,
##  <C>RepresentativeAction</C> and <C>\in</C> described in
##  Section&nbsp;<Ref Sect="Sect-WallMethods"/> use it.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
InstallMethod( WallClassicalGroupData, "for a matrix group", [ IsMatrixGroup ],
function( G )
  local f, kind;
  f := WALL_FormOfClassicalGroup( G );
  if f = fail then return fail; fi;
  kind := "G";
  if f.type = "L" then
    if not WALL_KnownTrue( IsNaturalGL, G ) then kind := "SL"; fi;
  elif WALL_KnownTrue( IsFullSubgroupGLRespectingBilinearFormUpToScalars, G ) then
    kind := "conformal";
  elif IsSubgroupSL( G ) and not IsBound( f.char2 ) and not IsBound( f.oddChar2 ) then
    if f.type = "U" then kind := "SU"; elif f.type = "O" then kind := "SO"; fi;
  fi;
  return rec( f := f, kind := kind );
end );

# spin groups (WallSpinGroup): kind "spin", f = the form of Omega
InstallMethod( WallClassicalGroupData, "for a spin group", [ IsMatrixGroup and HasWallSpinData ],
  S -> rec( f := WallSpinData( S ).fOmega, kind := "spin", group := S ) );

# is the matrix x in the group described by d?
BindGlobal( "WALL_IsInClassicalGroup", function( d, x )
  local f;
  if d.kind = "spin" then return x in d.group; fi;
  f := d.f;
  if not IsMatrix( x ) or Length( x ) <> f.n or IsZero( DeterminantMat( x ) ) then
    return false;
  fi;
  if d.kind = "conformal" then
    return x * f.gram * WALL_Star( f, x ) = WallMultiplier( f, x ) * f.gram;
  elif d.kind = "G" then
    return WallIsInGroup( f, x );
  fi;
  return WallIsInSubgroup( f, d.kind, x );
end );

# rec( invariant, conjugator ) with conjugator * x * conjugator^-1 the
# class representative
BindGlobal( "WALL_ConjugatingData", function( d, x )
  if d.kind = "spin" then return WallSpinConjugatingElement( d.group, x ); fi;
  if d.kind = "conformal" then return WallConformalConjugatingElement( d.f, x );
  elif d.kind = "G" then return WallConjugatingElement( d.f, x ); fi;
  return WallSubgroupConjugatingElement( d.f, d.kind, x );
end );

BindGlobal( "WALL_ClassInvariant", function( d, x )
  if d.kind = "spin" then return WallSpinInvariant( d.group, x ); fi;
  if d.kind = "conformal" then return WallConformalInvariant( d.f, x );
  elif d.kind = "G" then return WallInvariant( d.f, x ); fi;
  return WallSubgroupInvariant( d.f, d.kind, x );
end );

BindGlobal( "WALL_RepWithCentralizer", function( d, inv )
  if d.kind = "spin" then return WallSpinRepresentativeWithCentralizer( d.group, inv ); fi;
  if d.kind = "conformal" then return WallConformalRepresentativeWithCentralizer( d.f, inv );
  elif d.kind = "G" then return WallRepresentativeWithCentralizer( d.f, inv ); fi;
  return WallSubgroupRepresentativeWithCentralizer( d.f, d.kind, inv );
end );

# the centralizer of x in G as subgroup with known size, or fail if x is
# not in G (or G is not recognized)
BindGlobal( "WALL_CentralizerInClassicalGroup", function( G, x )
  local d, a, r, gens, yi, C;
  d := WALL_ClassicalGroupData( G );
  if d = fail or not WALL_IsInClassicalGroup( d, x ) then return fail; fi;
  a := WALL_ConjugatingData( d, x );
  r := WALL_RepWithCentralizer( d, a.invariant );
  yi := a.conjugator^-1;
  gens := List( r.generators, g -> ImmutableMatrix( d.f.field, yi * g * a.conjugator ) );
  C := SubgroupNC( G, gens );
  SetSize( C, r.centralizerOrder );
  return C;
end );

BindGlobal( "WALL_CentralizerOpMethod", function( G, x )
  local C;
  C := WALL_CentralizerInClassicalGroup( G, x );
  if C = fail then TryNextMethod(); fi;
  return C;
end );

InstallMethod( CentralizerOp,
  "for Sp, GO, SO and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingBilinearForm, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

InstallMethod( CentralizerOp,
  "for GO, SO and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingQuadraticForm, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

InstallMethod( CentralizerOp,
  "for GU, SU and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingSesquilinearForm, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

InstallMethod( CentralizerOp,
  "for CSp and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLRespectingBilinearFormUpToScalars, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

InstallMethod( CentralizerOp,
  "for GL and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and IsNaturalGL, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

InstallMethod( CentralizerOp,
  "for SL and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and IsNaturalSL, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

#############################################################################
##  IsConjugate( G, x, y ), RepresentativeAction( G, x, y )
#############################################################################

BindGlobal( "WALL_IsConjugateMethod", function( G, x, y )
  local d;
  d := WALL_ClassicalGroupData( G );
  if d = fail or not WALL_IsInClassicalGroup( d, x ) or not WALL_IsInClassicalGroup( d, y ) then
    TryNextMethod();
  fi;
  return WALL_ClassInvariant( d, x ) = WALL_ClassInvariant( d, y );
end );

# g in G with x^g = g^-1 x g = y, or fail
BindGlobal( "WALL_RepresentativeActionMethod", function( G, x, y, act )
  local d, a, b;
  if not IsIdenticalObj( act, OnPoints ) then TryNextMethod(); fi;
  d := WALL_ClassicalGroupData( G );
  if d = fail or not WALL_IsInClassicalGroup( d, x ) or not WALL_IsInClassicalGroup( d, y ) then
    TryNextMethod();
  fi;
  a := WALL_ConjugatingData( d, x );
  b := WALL_ConjugatingData( d, y );
  if a.invariant <> b.invariant then return fail; fi;
  return ImmutableMatrix( d.f.field, a.conjugator^-1 * b.conjugator );
end );

InstallMethod( IsConjugate,
  "for Sp, GO, SO and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingBilinearForm, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for Sp, GO, SO and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingBilinearForm, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );

InstallMethod( IsConjugate,
  "for GO, SO and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingQuadraticForm, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for GO, SO and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingQuadraticForm, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );

InstallMethod( IsConjugate,
  "for GU, SU and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingSesquilinearForm, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for GU, SU and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLorSLRespectingSesquilinearForm, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );

InstallMethod( IsConjugate,
  "for CSp and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLRespectingBilinearFormUpToScalars, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for CSp and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and IsFullSubgroupGLRespectingBilinearFormUpToScalars, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );

InstallMethod( IsConjugate,
  "for GL and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and IsNaturalGL, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for GL and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and IsNaturalGL, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );

InstallMethod( IsConjugate,
  "for SL and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and IsNaturalSL, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for SL and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and IsNaturalSL, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );

#############################################################################
##  membership in conjugacy classes
#############################################################################

##
##  <#GAPDoc Label="WallClassInvariant">
##  <ManSection>
##  <Attr Name="WallClassInvariant" Arg="cl"/>
##  <Returns>a record</Returns>
##  <Description>
##  For a conjugacy class <A>cl</A> of a group
##  recognized by <Ref Attr="WallClassicalGroupData"/>, returns its invariant
##  (as in <Ref Func="WallClassInvariants"/>,
##  <Ref Func="WallSubgroupClassInvariants"/> or
##  <Ref Func="WallConformalClassInvariants"/>, depending on the group). It is
##  set for the classes returned by <C>ConjugacyClasses</C>, and then
##  membership tests <C>x in cl</C> compare invariants.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
InstallMethod( WallClassInvariant, "for a conjugacy class of a classical group",
  [ IsConjugacyClassGroupRep ],
function( cl )
  local d;
  d := WALL_ClassicalGroupData( ActingDomain( cl ) );
  if d = fail then TryNextMethod(); fi;
  return WALL_ClassInvariant( d, Representative( cl ) );
end );

InstallMethod( \in, "for an element and a class with Wall's invariant", IsElmsColls,
  [ IsMatrix, IsConjugacyClassGroupRep and HasWallClassInvariant ],
function( x, cl )
  local d;
  d := WALL_ClassicalGroupData( ActingDomain( cl ) );
  if d = fail then TryNextMethod(); fi;
  if not WALL_IsInClassicalGroup( d, x ) then return false; fi;
  return WALL_ClassInvariant( d, x ) = WallClassInvariant( cl );
end );

#############################################################################
##  spin groups (WallSpinGroup / Spin)
#############################################################################

InstallMethod( NrConjugacyClasses, "for a spin group via Wall's classification",
  [ IsMatrixGroup and IsFinite and HasWallSpinData ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WallSpinNrClasses );

InstallMethod( ConjugacyClasses, "for a spin group via Wall's classification",
  [ IsMatrixGroup and IsFinite and HasWallSpinData ],
  RankFilter( IsHandledByNiceMonomorphism ),
  S -> WALL_ClassesFromInvariants( S, WallSpinData( S ).field, WallSpinClassInvariants( S ),
         inv -> WallSpinRepresentative( S, inv ), inv -> WallSpinClassSize( S, inv ) ) );

InstallMethod( CentralizerOp,
  "for a spin group and an element, via Wall's classification", IsCollsElms,
  [ IsMatrixGroup and IsFinite and HasWallSpinData, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_CentralizerOpMethod );

InstallMethod( IsConjugate,
  "for a spin group and two elements, via Wall's classification", IsCollsElmsElms,
  [ IsMatrixGroup and IsFinite and HasWallSpinData, IsMatrix, IsMatrix ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_IsConjugateMethod );

InstallOtherMethod( RepresentativeActionOp,
  "for a spin group and two elements, via Wall's classification", IsCollsElmsElmsX,
  [ IsMatrixGroup and IsFinite and HasWallSpinData, IsMatrix, IsMatrix, IsFunction ],
  RankFilter( IsHandledByNiceMonomorphism ),
  WALL_RepresentativeActionMethod );
