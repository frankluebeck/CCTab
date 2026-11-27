#############################################################################
##
##  wall.gi   conjugacy classes of finite classical groups following
##            G. E. Wall (1963) and, for unipotent classes in characteristic
##            2, De Franceschi, Liebeck, O'Brien (2025).
##
##  This file contains the implementation.  The declarations of all
##  global names are in wall.gd; the mathematical
##  description is in wall-classes.tex.  The API functions are documented by
##  GAPDoc sections directly in front of their implementation; the section
##  "WallIntro" below explains form records, conventions and invariants.
##
#############################################################################

##  <#GAPDoc Label="WallIntro">
##  The functions described here compute conjugacy classes of finite classical
##  groups following G.&nbsp;E.&nbsp;Wall, <Q>On the conjugacy classes in the
##  unitary, symplectic and orthogonal groups</Q> (J. Austral. Math. Soc. 3, 1963),
##  and, for unipotent classes in characteristic <M>2</M>, De&nbsp;Franceschi,
##  Liebeck, O'Brien, <Q>Conjugacy in Finite Classical Groups</Q> (2025).
##  The mathematical background is described in the document
##  <F>wall-classes.pdf</F>.
##  <P/>
##  A group is given by a <E>form record</E> <A>f</A>, created by
##  <Ref Func="WallClassicalForm"/> or <Ref Func="WallFormOfGroup"/>, for an
##  arbitrary non-degenerate form. Conventions are as in &GAP;: vectors are rows,
##  and <M>x</M> is an isometry of the form with Gram matrix <M>F</M> iff
##  <M>x F \bar{x}^{tr} = F</M>, where <M>\bar{x}</M> applies the field
##  automorphism <M>z \mapsto z^r</M> of <M>GF(r^2)</M> in the unitary case and
##  nothing otherwise. The form record also caches data; use the same record for
##  all computations concerning the same group.
##  <P/>
##  Classes are described by <E>invariants</E>, which are plain records and can be
##  listed without constructing matrices, also for large groups. Two group
##  elements are conjugate if and only if their invariants are equal.
##  For the isometry group <M>G(F)</M> an invariant has the components
##  <C>polys</C> (a sorted list of pairs: the coefficient list of an irreducible
##  polynomial <M>\varphi</M>, lowest degree first, and the partition
##  <M>\lambda_\varphi</M> of the exponents of its elementary divisors) and
##  <C>signs</C> (a sorted list of triples <M>[a, m, s_{a,m}]</M>, the sign
##  invariants for the eigenvalues <M>a = \pm 1</M>); for even <M>q</M> there are
##  the additional components <C>s</C>, <C>deltas</C> and <C>delta0</C>.
##  Classes of the subgroups <M>SO</M>, <M>\Omega</M>, <M>SU</M> are given by
##  records <C>rec( inv, label )</C>, and classes of conformal groups by records
##  <C>rec( mult, twisted, inv )</C>.
##  <P/>
##  Covered are <M>GU(n,r)</M> (all <M>r</M>), <M>Sp(2m,q)</M>,
##  <M>GO(2m+1,q)</M>, <M>GO^\pm(2m,q)</M> (all <M>q</M>), their subgroups
##  <M>SO</M> and <M>\Omega</M> (except in odd dimension for even <M>q</M>),
##  <M>SU(n,r)</M>, and the conformal groups.
##  <#/GAPDoc>


#############################################################################
##  small helpers
#############################################################################

BindGlobal( "WALL_Frob", function( M, e )
  if e = 1 then return M; fi;
  return List( M, row -> List( row, z -> z^e ) );
end );

# GAP keeps elements of large fields GF(p^d) (> 2^16 elements) in a
# representation of that field even if they lie in a subfield; mixing two
# such fields forces a common overfield.  Convert values back to the small
# internal representation whenever possible.
BindGlobal( "WALL_K", function( z )
  local y;
  if IsInternalRep( z ) then return z; fi;
  y := AsInternalFFE( z );
  if y = fail then return z; fi;
  return y;
end );
BindGlobal( "WALL_KMat", M -> List( M, row -> List( row, WALL_K ) ) );

# the field GF(Q^d); GAP needs a Conway polynomial for large fields
BindGlobal( "WALL_ExtField", function( Q, d )
  local p, e;
  p := SmallestRootInt( Q ); e := LogInt( Q, p ) * d;
  if p^e > 2^16 and not IsCheapConwayPolynomial( p, e ) then
    Error( "the field GF(", p, "^", e, ") is needed (an irreducible factor of ",
           "degree ", d, "), but GAP has no Conway polynomial for it" );
  fi;
  return GF( p, e );
end );

# M^* = (M^sigma)^T
BindGlobal( "WALL_Star", function( f, M )
  return TransposedMat( WALL_Frob( M, f.sigma ) );
end );

# Legendre symbol on GF(q), q odd: 1 for squares, -1 for non-squares
BindGlobal( "WALL_Leg", function( z, q )
  if IsZero( z ) then Error( "WALL_Leg: zero" ); fi;
  if IsOne( z^( (q-1)/2 ) ) then return 1; else return -1; fi;
end );

BindGlobal( "WALL_Sqrt", function( z, K )
  local w, l;
  w := PrimitiveRoot( K );
  if IsZero( z ) then return z; fi;
  l := LogFFE( z, w );
  if IsOddInt( l ) then
    if IsEvenInt( Size( K ) ) then return z^( Size( K ) / 2 ); fi;
    return fail;
  fi;
  return w^( l / 2 );
end );

BindGlobal( "WALL_BlockDiag", function( K, blocks )
  local n, M, pos, b, i, j;
  n := Sum( blocks, Length );
  M := NullMat( n, n, K );
  pos := 0;
  for b in blocks do
    for i in [ 1 .. Length( b ) ] do
      for j in [ 1 .. Length( b ) ] do
        M[ pos + i ][ pos + j ] := b[ i ][ j ];
      od;
    od;
    pos := pos + Length( b );
  od;
  return M;
end );

# group orders
BindGlobal( "WALL_OrderGL", function( m, Q )
  return Q^( m * ( m - 1 ) / 2 ) * Product( [ 1 .. m ], i -> Q^i - 1 );
end );
BindGlobal( "WALL_OrderGU", function( m, r )      # GU(m,r), defined over GF(r^2)
  return r^( m * ( m - 1 ) / 2 ) * Product( [ 1 .. m ], i -> r^i - (-1)^i );
end );
BindGlobal( "WALL_OrderSp", function( m, q )      # Sp(m,q), m even
  local k;
  k := m / 2;
  return q^( k^2 ) * Product( [ 1 .. k ], i -> q^( 2 * i ) - 1 );
end );
BindGlobal( "WALL_OrderO", function( m, q, e )    # full orthogonal group, e = +1/-1
  local k;
  if m = 0 then return 1; fi;
  if IsOddInt( m ) then
    k := ( m - 1 ) / 2;
    return 2 * q^( k^2 ) * Product( [ 1 .. k ], i -> q^( 2 * i ) - 1 );
  fi;
  k := m / 2;
  return 2 * q^( k * ( k - 1 ) ) * ( q^k - e )
           * Product( [ 1 .. k - 1 ], i -> q^( 2 * i ) - 1 );
end );

#############################################################################
##  forms
#############################################################################

##
##  <#GAPDoc Label="WallClassicalForm">
##  <ManSection>
##  <Func Name="WallClassicalForm" Arg="type, F, K"/>
##  <Returns>a form record</Returns>
##  <Description>
##  <A>type</A> is one of <C>"U"</C>, <C>"Sp"</C>, <C>"O"</C>, <A>F</A> is a
##  non-degenerate Gram matrix over the finite field <A>K</A>: hermitian for
##  <C>"U"</C> (then <A>K</A> <M>= GF(r^2)</M>), alternating for <C>"Sp"</C>, and
##  symmetric for <C>"O"</C> with odd <M>q</M>. For <C>"O"</C> and even <M>q</M>,
##  <A>F</A> is the matrix of the quadratic form <M>Q(v) = v F v^{tr}</M> (any
##  matrix, for example as returned by <Ref Attr="InvariantQuadraticForm" BookName="ref"/>).
##  The result describes the isometry group <M>G(F)</M> and is the first argument
##  of all other functions.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallClassicalForm", function( type, F, K )
  local f, q, r, n;
  n := Length( F );
  q := Size( K );
  f := rec( type := type, gram := Immutable( F ), field := K, n := n,
            p := Characteristic( K ), one := One( K ) );
  if type = "U" then
    r := RootInt( q );
    if r^2 <> q then Error( "WallClassicalForm: field size must be a square for U" ); fi;
    f.r := r; f.sigma := r; f.eps := 1;
  elif type = "Sp" or type = "O" then
    if IsEvenInt( q ) then
      # characteristic 2: see the section "characteristic 2" below
      return WALL2_Form( type, F, K );
    fi;
    f.sigma := 1;
    if type = "Sp" then f.eps := -1; else f.eps := 1; fi;
  else
    Error( "WallClassicalForm: type must be \"U\", \"Sp\" or \"O\"" );
  fi;
  f.q := q;   # size of the field of definition K
  if WALL_Star( f, F ) <> f.eps * F then
    Error( "WallClassicalForm: Gram matrix has wrong symmetry" );
  fi;
  if type = "Sp" and ForAny( [ 1 .. n ], i -> not IsZero( F[ i ][ i ] ) ) then
    Error( "WallClassicalForm: not alternating" );
  fi;
  if IsZero( DeterminantMat( F ) ) then
    Error( "WallClassicalForm: degenerate form" );
  fi;
  if type = "O" then
    f.det := WALL_Leg( DeterminantMat( F ), q );
    if IsEvenInt( n ) then
      # Witt type: +1 iff det = (-1)^(n/2) modulo squares
      f.sign := f.det * WALL_Leg( (-1)^( n / 2 ) * One( K ), q );
    else
      f.sign := 0;
    fi;
  fi;
  return f;
end );

##
##  <#GAPDoc Label="WallFormOfGroup">
##  <ManSection>
##  <Func Name="WallFormOfGroup" Arg="G"/>
##  <Returns>a form record</Returns>
##  <Description>
##  returns the form record of the matrix group <A>G</A> from its stored
##  invariant form (<Ref Attr="InvariantSesquilinearForm" BookName="ref"/>,
##  <Ref Attr="InvariantQuadraticForm" BookName="ref"/> for even <M>q</M>,
##  otherwise <Ref Attr="InvariantBilinearForm" BookName="ref"/>), for example
##  for &GAP;'s <C>GU</C>, <C>Sp</C>, <C>GO</C> and their subgroups.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallFormOfGroup", function( G )
  local K, F;
  K := DefaultFieldOfMatrixGroup( G );
  if HasInvariantSesquilinearForm( G ) then
    F := InvariantSesquilinearForm( G ).matrix;
    if IsOddInt( DegreeOverPrimeField( K ) ) then
      K := GF( Characteristic( K ), 2 * DegreeOverPrimeField( K ) );
    fi;
    return WallClassicalForm( "U", F, K );
  fi;
  if IsEvenInt( Size( K ) ) then
    if HasInvariantQuadraticForm( G ) then
      return WallClassicalForm( "O", InvariantQuadraticForm( G ).matrix, K );
    fi;
    return WallClassicalForm( "Sp", InvariantBilinearForm( G ).matrix, K );
  fi;
  F := InvariantBilinearForm( G ).matrix;
  if TransposedMat( F ) = F then
    return WallClassicalForm( "O", F, K );
  fi;
  return WallClassicalForm( "Sp", F, K );
end );

##
##  <#GAPDoc Label="WallIsInGroup">
##  <ManSection>
##  <Func Name="WallIsInGroup" Arg="f, x"/>
##  <Returns><K>true</K> or <K>false</K></Returns>
##  <Description>
##  tests whether the matrix <A>x</A> lies in <M>G(F)</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallIsInGroup", function( f, x )
  if Length( x ) <> f.n or x * f.gram * WALL_Star( f, x ) <> f.gram then
    return false;
  fi;
  if IsBound( f.quad ) then          # characteristic 2, orthogonal
    # Q(e_i x) = Q(e_i) for all basis vectors (B is preserved already)
    return ForAll( [ 1 .. f.n ], i -> x[ i ] * f.quad * x[ i ] = f.quad[ i ][ i ] );
  fi;
  return true;
end );

#############################################################################
##  canonical bases for forms  (P * F * P^* = C, C depends only on the
##  equivalence class of the form)
#############################################################################

BindGlobal( "WALL_CanonicalBaseChange", function( f, F )
  local K, n, W, res, G, i, j, v, c, zeta, d, lam, w, beta, nu, z, x, y,
        P, C, ones, nus, s, k, es, fs, e1, f1;
  K := f.field; n := Length( F );
  W := List( IdentityMat( n, K ), ShallowCopy );
  if f.type = "Sp" then
    es := []; fs := [];
    while Length( W ) > 0 do
      e1 := W[ 1 ];
      j := First( [ 2 .. Length( W ) ],
                  k -> not IsZero( e1 * F * W[ k ] ) );
      if j = fail then Error( "degenerate" ); fi;
      f1 := W[ j ] / ( e1 * F * W[ j ] );          # B(e1,f1) = 1
      Add( es, e1 ); Add( fs, f1 );
      W := W{ Difference( [ 2 .. Length( W ) ], [ j ] ) };
      # project onto <e1,f1>^perp : w -> w - B(w,f1) e1 + B(w,e1) f1
      W := List( W, w -> w - ( w * F * f1 ) * e1 + ( w * F * e1 ) * f1 );
    od;
    P := Concatenation( es, fs );
    k := n / 2;
    C := NullMat( n, n, K );
    for i in [ 1 .. k ] do
      C[ i ][ k + i ] := One( K ); C[ k + i ][ i ] := -One( K );
    od;
    return rec( P := P, C := C );
  fi;
  # orthogonal / unitary: diagonalise
  if f.type = "U" then
    # an element of non-zero trace over GF(r)
    if IsOddInt( f.p ) then zeta := One( K ); else zeta := PrimitiveRoot( K ); fi;
  else
    zeta := One( K );
  fi;
  res := [];
  while Length( W ) > 0 do
    G := W * F * WALL_Star( f, W );
    i := First( [ 1 .. Length( W ) ], k -> not IsZero( G[ k ][ k ] ) );
    if i <> fail then
      v := W[ i ];
      W := W{ Difference( [ 1 .. Length( W ) ], [ i ] ) };
    else
      i := First( [ 1 .. Length( W ) ],
                  k -> ForAny( G[ k ], z -> not IsZero( z ) ) );
      if i = fail then Error( "degenerate" ); fi;
      j := PositionProperty( G[ i ], z -> not IsZero( z ) );
      c := ( zeta / G[ i ][ j ] )^f.sigma;
      v := W[ i ] + c * W[ j ];
      W := W{ Difference( [ 1 .. Length( W ) ], [ i ] ) };
    fi;
    d := ( [ v ] * F * WALL_Star( f, [ v ] ) )[ 1 ][ 1 ];
    W := List( W, w -> w -
           ( ( [ w ] * F * WALL_Star( f, [ v ] ) )[ 1 ][ 1 ] / d ) * v );
    Add( res, [ v, d ] );
  od;
  if f.type = "U" then
    w := PrimitiveRoot( K );
    P := List( res, function( vd )
           local l;
           l := LogFFE( vd[ 2 ]^-1, w );         # vd[2] lies in GF(r)
           return w^( l / ( f.r + 1 ) ) * vd[ 1 ];
         end );
    return rec( P := P, C := IdentityMat( n, K ) );
  fi;
  # orthogonal, q odd
  nu := PrimitiveRoot( K );
  ones := []; nus := [];
  for v in res do
    s := WALL_Sqrt( v[ 2 ]^-1, K );
    if s <> fail then Add( ones, s * v[ 1 ] );
    else Add( nus, WALL_Sqrt( nu / v[ 2 ], K ) * v[ 1 ] ); fi;
  od;
  if Length( nus ) >= 2 then
    # find x,y with x^2+y^2 = nu^-1
    x := Zero( K ); y := WALL_Sqrt( nu^-1, K );
    while y = fail do
      x := x + One( K );            # x runs through the prime field
      y := WALL_Sqrt( nu^-1 - x^2, K );
    od;
    while Length( nus ) >= 2 do
      v := nus[ 1 ]; w := nus[ 2 ];
      Add( ones, x * v + y * w ); Add( ones, -y * v + x * w );
      nus := nus{ [ 3 .. Length( nus ) ] };
    od;
  fi;
  P := Concatenation( ones, nus );
  C := IdentityMat( n, K );
  if Length( nus ) = 1 then C := List( C, ShallowCopy ); C[ n ][ n ] := nu; fi;
  return rec( P := P, C := C );
end );

#############################################################################
##  polynomials (stored as monic coefficient lists, low degree first)
#############################################################################

# the "dual" polynomial: roots are sigma(alpha)^-1
BindGlobal( "WALL_DualCoeffs", function( f, c )
  local rc, d;
  if IsBound( f.twist ) then
    # twisted dual: roots nu/alpha, nu = f.twist
    d := Length( c ) - 1;
    rc := List( [ 0 .. d ], j -> c[ d - j + 1 ] * f.twist^( d - j ) );
    return rc / rc[ Length( rc ) ];
  fi;
  rc := Reversed( c );
  if f.type = "U" then rc := List( rc, z -> z^f.r ); fi;
  return rc / rc[ Length( rc ) ];
end );

BindGlobal( "WALL_PolString", function( f, c )
  return String( UnivariatePolynomial( f.field, c ) );
end );

#############################################################################
##  invariants of a given element
#############################################################################

# Sign data at eigenvalue a = +-1 (Sp/O only).
# x, F: an isometry and the Gram matrix; part: partition of the
# (t-a)-part of x.  Returns list of [ a, m, s ] where m runs over the parts
# carrying a symmetric multiplicity form (m even for Sp, m odd for O) and
# s = Legendre symbol of the determinant of
#     h_m(u,v) = B(u, v Y^(m-1)),  Y = x - x^-1,
# on ker Y^m / ( ker Y^(m-1) + (ker Y^(m+1)) Y )  inside the a-part of V.
BindGlobal( "WALL_SignData", function( f, x, F, a, part )
  local K, n, s, Bas, Y, Ya, Ga, res, m, Km, Km1, Kp, S, comp, Ym1, H, sb;
  K := f.field; n := Length( x );
  s := Sum( part );
  Bas := NullspaceMat( ( x - a * IdentityMat( n, K ) )^s );
  Y := x - x^-1;
  Ya := List( Bas, b -> SolutionMat( Bas, b * Y ) );
  Ga := Bas * F * TransposedMat( Bas );
  res := [];
  for m in Set( part ) do
    if ( f.type = "Sp" and IsEvenInt( m ) ) or
       ( f.type = "O" and IsOddInt( m ) ) then
      Km  := NullspaceMat( Ya^m );
      Km1 := NullspaceMat( Ya^( m - 1 ) );
      Kp  := NullspaceMat( Ya^( m + 1 ) ) * Ya;
      S := Concatenation( Km1, Kp );
      if Length( S ) = 0 then
        comp := Km;
      else
        S := BaseMat( S );
        comp := BaseSteinitzVectors( Km, S ).factorspace;
      fi;
      Ym1 := Ya^( m - 1 );
      H := List( comp, u -> List( comp, v -> u * Ga * ( v * Ym1 ) ) );
      if Length( H ) <> Number( part, i -> i = m ) then
        Error( "WALL_SignData: wrong dimension" );
      fi;
      Add( res, [ a, m, WALL_Leg( DeterminantMat( H ), f.q ) ] );
    fi;
  od;
  return res;
end );

BindGlobal( "WALL_Partition", function( f, x, pol, mult )
  local n, M, P, dims, d;
  n := Length( x );
  d := Degree( pol );
  M := Value( pol, x );
  P := M;
  dims := [ 0 ];
  repeat
    Add( dims, ( n - RankMat( P ) ) / d );
    P := P * M;
  until dims[ Length( dims ) ] = mult;
  return AssociatedPartition(
           List( [ 2 .. Length( dims ) ], i -> dims[ i ] - dims[ i - 1 ] ) );
end );

BindGlobal( "WALL_MakeInvariant", function( f, polys, signs )
  return rec( type := f.type, n := f.n, q := f.q,
              polys := Immutable( SortedList( polys ) ),
              signs := Immutable( SortedList( signs ) ) );
end );

##
##  <#GAPDoc Label="WallInvariant">
##  <ManSection>
##  <Func Name="WallInvariant" Arg="f, x"/>
##  <Returns>a record</Returns>
##  <Description>
##  returns the class invariant of <A>x</A> <M>\in G(F)</M>. Two elements of
##  <M>G(F)</M> are conjugate if and only if their invariants are equal.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallInvariant", function( f, x )
  local K, chi, facs, polys, signs, pr, c, part, a;
  if IsBound( f.oddChar2 ) then return WallInvariant( f.sp, WALL2_OddImage( f, x ) ); fi;
  if IsBound( f.twist ) then return WALL3_Invariant( f, x ); fi;
  if IsBound( f.char2 ) then return WALL2_Invariant( f, x ); fi;
  if not WallIsInGroup( f, x ) then
    Error( "WallInvariant: x does not preserve the form" );
  fi;
  K := f.field;
  chi := CharacteristicPolynomial( K, K, x );
  facs := Collected( Factors( PolynomialRing( K ), chi ) );
  polys := []; signs := [];
  for pr in facs do
    c := CoefficientsOfUnivariatePolynomial( pr[ 1 ] );
    c := c / c[ Length( c ) ];
    part := WALL_Partition( f, x, pr[ 1 ], pr[ 2 ] );
    Add( polys, [ c, part ] );
    if f.type <> "U" and Length( c ) = 2 and
       ( IsOne( c[ 1 ] ) or IsOne( -c[ 1 ] ) ) then
      a := -c[ 1 ];
      Append( signs, WALL_SignData( f, x, f.gram, a, part ) );
    fi;
  od;
  return WALL_MakeInvariant( f, polys, signs );
end );

##
##  <#GAPDoc Label="WallDisplayInvariant">
##  <ManSection>
##  <Func Name="WallDisplayInvariant" Arg="f, inv"/>
##  <Returns>nothing</Returns>
##  <Description>
##  prints the class invariant <A>inv</A>: each polynomial with its
##  partition and, where present, the sign invariants <C>[m:s]</C>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallDisplayInvariant", function( f, inv )
  local p, s;
  if IsBound( f.oddChar2 ) then return WallDisplayInvariant( f.sp, inv ); fi;
  for p in inv.polys do
    Print( "  ", WALL_PolString( f, p[ 1 ] ), " : ", p[ 2 ] );
    for s in Filtered( inv.signs, s -> Length( p[ 1 ] ) = 2 and
                                      s[ 1 ] = -p[ 1 ][ 1 ] ) do
      Print( "  [", s[ 2 ], ":", s[ 3 ], "]" );
    od;
    Print( "\n" );
  od;
end );

#############################################################################
##  centralizer orders (Wall 2.6 (iv) in all three cases)
#############################################################################

BindGlobal( "WALL_Mults", function( part )
  return List( Set( part ), m -> [ m, Number( part, i -> i = m ) ] );
end );

# 2 * (sum_{mu<nu} mu m_mu m_nu + 1/2 sum_mu (mu-1) m_mu^2)
BindGlobal( "WALL_E2", function( part )
  local ml, e, i, j;
  ml := WALL_Mults( part );
  e := 0;
  for i in [ 1 .. Length( ml ) ] do
    for j in [ i + 1 .. Length( ml ) ] do
      e := e + 2 * ml[ i ][ 1 ] * ml[ i ][ 2 ] * ml[ j ][ 2 ];
    od;
    e := e + ( ml[ i ][ 1 ] - 1 ) * ml[ i ][ 2 ]^2;
  od;
  return e;
end );

##
##  <#GAPDoc Label="WallCentralizerOrder">
##  <ManSection>
##  <Func Name="WallCentralizerOrder" Arg="f, inv"/>
##  <Func Name="WallClassSize" Arg="f, inv"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  return the order of the centralizer in <M>G(F)</M> and the size of the
##  class with invariant <A>inv</A>, computed from Wall's formulas.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallCentralizerOrder", function( f, inv )
  local res, Q, p, c, d, dual, part, ml, e2, a, mm, s, sg, ord;
  if IsBound( f.oddChar2 ) then return WallCentralizerOrder( f.sp, inv ); fi;
  if IsBound( f.twist ) then return WALL3_CentralizerOrder( f, inv ); fi;
  if IsBound( f.char2 ) then return WALL2_CentralizerOrder( f, inv ); fi;
  res := 1;
  Q := f.q;
  for p in inv.polys do
    c := p[ 1 ]; part := p[ 2 ]; d := Length( c ) - 1;
    ml := WALL_Mults( part );
    e2 := WALL_E2( part );
    dual := WALL_DualCoeffs( f, c );
    if f.type <> "U" and d = 1 and dual = c then        # t -+ 1
      a := -c[ 1 ];
      if f.type = "Sp" then
        e2 := e2 + Sum( Filtered( ml, x -> IsEvenInt( x[ 1 ] ) ), x -> x[ 2 ] );
      else
        e2 := e2 - Sum( Filtered( ml, x -> IsEvenInt( x[ 1 ] ) ), x -> x[ 2 ] );
      fi;
      res := res * Q^( e2 / 2 );
      for mm in ml do
        if ( f.type = "Sp" ) = IsOddInt( mm[ 1 ] ) then
          res := res * WALL_OrderSp( mm[ 2 ], Q );
        else
          s := First( inv.signs, x -> x[ 1 ] = a and x[ 2 ] = mm[ 1 ] )[ 3 ];
          if IsEvenInt( mm[ 2 ] ) then
            sg := s * WALL_Leg( (-1)^( mm[ 2 ] / 2 ) * f.one, Q );
          else
            sg := 0;
          fi;
          res := res * WALL_OrderO( mm[ 2 ], Q, sg );
        fi;
      od;
    elif dual = c then                                  # self-dual
      # Wall's Q = |K|^d, A = |U(m, Q)| = GU(m, sqrt(Q))
      if f.type = "U" then ord := f.r^d; else ord := Q^( d / 2 ); fi;
      res := res * ord^e2 * Product( ml, x -> WALL_OrderGU( x[ 2 ], ord ) );
    elif c < dual then                                  # pair, counted once
      res := res * ( Q^d )^e2 * Product( ml, x -> WALL_OrderGL( x[ 2 ], Q^d ) );
    fi;
  od;
  return res;
end );

##
##  <#GAPDoc Label="WallGroupOrder">
##  <ManSection>
##  <Func Name="WallGroupOrder" Arg="f"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  returns the order of <M>G(F)</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallGroupOrder", function( f )
  if IsBound( f.oddChar2 ) then return WallGroupOrder( f.sp ); fi;
  if f.type = "U" then return WALL_OrderGU( f.n, f.r );
  elif f.type = "Sp" then return WALL_OrderSp( f.n, f.q );
  else return WALL_OrderO( f.n, f.q, f.sign ); fi;
end );

BindGlobal( "WallClassSize", function( f, inv )
  return WallGroupOrder( f ) / WallCentralizerOrder( f, inv );
end );

#############################################################################
##  number of classes (Wall 2.6 (iii)), via generating functions
#############################################################################

BindGlobal( "WALL_SeriesMul", function( a, b, N )
  local c, i, j;
  c := ListWithIdenticalEntries( N + 1, 0 );
  for i in [ 0 .. N ] do
    if a[ i + 1 ] <> 0 then
      for j in [ 0 .. N - i ] do
        c[ i + j + 1 ] := c[ i + j + 1 ] + a[ i + 1 ] * b[ j + 1 ];
      od;
    fi;
  od;
  return c;
end );

# 1 / (1 - c t^k) and (1 + s t^k)
BindGlobal( "WALL_SeriesGeom", function( c, k, N )
  local a, i;
  a := ListWithIdenticalEntries( N + 1, 0 );
  for i in [ 0 .. QuoInt( N, k ) ] do a[ i * k + 1 ] := c^i; od;
  return a;
end );
BindGlobal( "WALL_SeriesBinom", function( s, k, N )
  local a;
  a := ListWithIdenticalEntries( N + 1, 0 );
  a[ 1 ] := 1;
  if k <= N then a[ k + 1 ] := s; fi;
  return a;
end );

##
##  <#GAPDoc Label="WallNrClasses">
##  <ManSection>
##  <Func Name="WallNrClasses" Arg="f"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  returns the number of conjugacy classes of <M>G(F)</M>, computed from
##  Wall's generating functions (without enumerating the classes).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallNrClasses", function( f )
  local N, S, D, l, i, q;
  if IsBound( f.oddChar2 ) then return WallNrClasses( f.sp ); fi;
  if IsBound( f.char2 ) then return WALL2_NrClasses( f ); fi;
  N := f.n; q := f.q;
  S := ListWithIdenticalEntries( N + 1, 0 ); S[ 1 ] := 1;
  if f.type = "U" then
    for l in [ 1 .. N ] do
      S := WALL_SeriesMul( S, WALL_SeriesBinom( 1, l, N ), N );
      S := WALL_SeriesMul( S, WALL_SeriesGeom( f.r, l, N ), N );
    od;
    return S[ N + 1 ];
  elif f.type = "Sp" then
    for l in [ 1 .. N ] do
      for i in [ 1 .. 4 ] do
        S := WALL_SeriesMul( S, WALL_SeriesBinom( 1, 2 * l, N ), N );
      od;
      S := WALL_SeriesMul( S, WALL_SeriesGeom( q, 2 * l, N ), N );
    od;
    return S[ N + 1 ];
  fi;
  # orthogonal: k+ + k-  and  k+ - k-
  for l in [ 1 .. N ] do
    for i in [ 1 .. 4 ] do
      S := WALL_SeriesMul( S, WALL_SeriesBinom( 1, 2 * l - 1, N ), N );
    od;
    S := WALL_SeriesMul( S, WALL_SeriesGeom( q, 2 * l, N ), N );
  od;
  if IsOddInt( N ) then return S[ N + 1 ] / 2; fi;
  D := ListWithIdenticalEntries( N + 1, 0 ); D[ 1 ] := 1;
  for l in [ 1 .. N ] do
    D := WALL_SeriesMul( D, WALL_SeriesBinom( -1, 4 * l - 2, N ), N );
    D := WALL_SeriesMul( D, WALL_SeriesGeom( q, 4 * l, N ), N );
  od;
  return ( S[ N + 1 ] + f.sign * D[ N + 1 ] ) / 2;
end );

#############################################################################
##  enumeration of irreducible polynomials, grouped into
##     self-dual polynomials and pairs {phi, dual(phi)}
##  (t-1, t+1 for Sp/O are treated separately)
#############################################################################

# orbits of exponents k (alpha = w^k) under k -> k*Q mod N of size exactly d
BindGlobal( "WALL_OrbitOf", function( k, Q, N )
  local o, j;
  o := [ k ]; j := k * Q mod N;
  while j <> k do Add( o, j ); j := j * Q mod N; od;
  return o;
end );

BindGlobal( "WALL_Atoms", function( f )
  local K, Q, n, atoms, d, L, w, N, seen, k, o, dk, c, cd, T, j, step, r;
  K := f.field; Q := f.q; n := f.n;
  atoms := [];        # rec( pols := [c] or [c, cd], weight := ...)
  # self-dual ones
  for d in [ 1 .. n ] do
    if f.type = "U" then
      if IsEvenInt( d ) then continue; fi;
      T := f.r^d;                       # tau = (r^d)-Frobenius
    else
      if IsOddInt( d ) then continue; fi;
      T := Q^( d / 2 );
    fi;
    L := WALL_ExtField( Q, d ); w := PrimitiveRoot( L ); N := Q^d - 1;
    step := T - 1;                       # alpha^(T+1) = 1  <=> step | k
    seen := [];
    for j in [ 0 .. T ] do
      k := j * step mod N;
      if k in seen then continue; fi;
      o := WALL_OrbitOf( k, Q, N );
      UniteSet( seen, o );
      if Length( o ) <> d then continue; fi;
      c := List( CoefficientsOfUnivariatePolynomial( MinimalPolynomial( K, w^k ) ), WALL_K );
      Add( atoms, rec( pols := [ c ], weight := d, selfdual := true ) );
    od;
  od;
  # pairs
  for d in [ 1 .. QuoInt( n, 2 ) ] do
    L := WALL_ExtField( Q, d ); w := PrimitiveRoot( L ); N := Q^d - 1;
    seen := BlistList( [ 1 .. N ], [] );   # seen[k+1]
    for k in [ 0 .. N - 1 ] do
      if seen[ k + 1 ] then continue; fi;
      o := WALL_OrbitOf( k, Q, N );
      for j in o do seen[ j + 1 ] := true; od;
      if Length( o ) <> d then continue; fi;
      if f.type = "U" then dk := ( -f.r * k ) mod N; else dk := ( -k ) mod N; fi;
      if dk in o then continue; fi;        # self-dual (or +-1)
      for j in WALL_OrbitOf( dk, Q, N ) do seen[ j + 1 ] := true; od;
      c := List( CoefficientsOfUnivariatePolynomial( MinimalPolynomial( K, w^k ) ), WALL_K );
      cd := WALL_DualCoeffs( f, c );
      Add( atoms, rec( pols := [ c, cd ], weight := 2 * d, selfdual := false ) );
    od;
  od;
  SortBy( atoms, a -> a.weight );
  return atoms;
end );

# options for the (t-a)-part, a = +-1, of total size s (Sp/O)
BindGlobal( "WALL_PlusMinusOptions", function( f, a, s )
  local res, lam, good, symparts, choices, ch;
  res := [];
  for lam in Partitions( s ) do
    if f.type = "Sp" then
      good := ForAll( Set( Filtered( lam, IsOddInt ) ),
                      m -> IsEvenInt( Number( lam, i -> i = m ) ) );
      symparts := Set( Filtered( lam, IsEvenInt ) );
    else
      good := ForAll( Set( Filtered( lam, IsEvenInt ) ),
                      m -> IsEvenInt( Number( lam, i -> i = m ) ) );
      symparts := Set( Filtered( lam, IsOddInt ) );
    fi;
    if not good then continue; fi;
    choices := Tuples( [ 1, -1 ], Length( symparts ) );
    for ch in choices do
      Add( res, rec( pol := [ -a, f.one ], part := lam,
                     signs := List( [ 1 .. Length( symparts ) ],
                                    i -> [ a, symparts[ i ], ch[ i ] ] ) ) );
    od;
  od;
  return res;
end );

# determinant class (Legendre symbol) of the form determined by an
# invariant (orthogonal case); see the LaTeX notes, Lemma "det".
BindGlobal( "WALL_DetClassOfInvariant", function( f, inv )
  local q, lm1, res, p, c, d, dual, s;
  q := f.q; lm1 := WALL_Leg( -f.one, q );
  res := 1;
  for p in inv.polys do
    c := p[ 1 ]; d := Length( c ) - 1; dual := WALL_DualCoeffs( f, c );
    if d = 1 and dual = c then continue; fi;
    if dual = c then
      res := res * ( - lm1^( d / 2 ) )^Sum( p[ 2 ] );
    elif c < dual then
      res := res * lm1^( d * Sum( p[ 2 ] ) );
    fi;
  od;
  for s in inv.signs do
    if IsOddInt( s[ 2 ] ) then res := res * s[ 3 ]; fi;
  od;
  return res;
end );

##
##  <#GAPDoc Label="WallClassInvariants">
##  <ManSection>
##  <Func Name="WallClassInvariants" Arg="f"/>
##  <Returns>a list of records</Returns>
##  <Description>
##  returns the list of the invariants of all conjugacy classes of
##  <M>G(F)</M>, one for each class (see the introduction for their format).
##  No matrices are constructed, so this also works for large groups.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallClassInvariants", function( f )
  local n, atoms, result, pm, s, rec1, recurse, base, s1, s2, o1, o2;
  if IsBound( f.oddChar2 ) then return WallClassInvariants( f.sp ); fi;
  if IsBound( f.twist ) then return WALL3_ClassInvariants( f ); fi;
  if IsBound( f.char2 ) then return WALL2_ClassInvariants( f ); fi;
  n := f.n;
  atoms := WALL_Atoms( f );
  result := [];
  recurse := function( start, remaining, polys, signs )
    local i, a, k, lam, newpolys, inv;
    if remaining = 0 then
      inv := WALL_MakeInvariant( f, polys, signs );
      if f.type <> "O" or WALL_DetClassOfInvariant( f, inv ) = f.det then
        Add( result, inv );
      fi;
      return;
    fi;
    for i in [ start .. Length( atoms ) ] do
      a := atoms[ i ];
      if a.weight > remaining then break; fi;
      for k in [ 1 .. QuoInt( remaining, a.weight ) ] do
        for lam in Partitions( k ) do
          newpolys := Concatenation( polys,
                        List( a.pols, c -> [ c, lam ] ) );
          recurse( i + 1, remaining - k * a.weight, newpolys, signs );
        od;
      od;
    od;
  end;
  if f.type = "U" then
    recurse( 1, n, [], [] );
  else
    for s1 in [ 0 .. n ] do
      for s2 in [ 0 .. n - s1 ] do
        if s1 = 0 then o1 := [ rec( pol := 0, part := [], signs := [] ) ];
        else o1 := WALL_PlusMinusOptions( f, f.one, s1 ); fi;
        if s2 = 0 then o2 := [ rec( pol := 0, part := [], signs := [] ) ];
        else o2 := WALL_PlusMinusOptions( f, -f.one, s2 ); fi;
        for rec1 in Cartesian( o1, o2 ) do
          base := Filtered( List( rec1, r -> [ r.pol, r.part ] ),
                            x -> x[ 1 ] <> 0 );
          recurse( 1, n - s1 - s2, base,
                   Concatenation( rec1[ 1 ].signs, rec1[ 2 ].signs ) );
        od;
      od;
    od;
  fi;
  return result;
end );

#############################################################################
##  construction of representatives and of centralizers
##
##  The model is an orthogonal sum of "components", one for each self-dual
##  phi and one for each pair {phi, dual(phi)}.  A component is described
##  over Lambda = K[t]/(phi) (Lambda = K for t-+1):
##
##    M = (+)_mu  W_mu (x) Lambda[Y]/(Y^mu),   W_mu = Lambda^(m_mu),
##    x = 1 (x) x_mu,
##    self-dual:  H = (+)_mu h_mu (x) beta_mu,  F = Tr_{Lambda/K} o H,
##    pair:       M (+) M^dual with the hyperbolic form.
#############################################################################

# data of the field Lambda = K(alpha) for the irreducible polynomial c
BindGlobal( "WALL_LambdaData", function( f, c, selfdual )
  local K, Q, d, LD, V;
  K := f.field; Q := f.q; d := Length( c ) - 1;
  LD := rec( d := d );
  if d = 1 then
    LD.L := K; LD.alpha := -c[ 1 ];
  else
    LD.L := WALL_ExtField( Q, d );
    LD.alpha := RootsOfUPol( LD.L, UnivariatePolynomial( K, c ) )[ 1 ];
    V := AsVectorSpace( K, LD.L );
    LD.basis := Basis( V, List( [ 0 .. d - 1 ], i -> LD.alpha^i ) );
  fi;
  if selfdual then
    if f.type = "U" then LD.T := f.r^d;
    elif d = 1 then LD.T := 1;             # t -+ 1: trivial involution
    else LD.T := Q^( d / 2 ); fi;
  else
    LD.T := fail;
  fi;
  LD.w := PrimitiveRoot( LD.L );
  return LD;
end );

# K-matrix of a Lambda-matrix (basis alpha^0..alpha^(d-1) in each coordinate)
BindGlobal( "WALL_Realize", function( f, LD, A )
  local d, N, R, i, j, al, Mz;
  d := LD.d;
  if d = 1 then return A; fi;
  N := Length( A );
  R := NullMat( N * d, N * d, f.field );
  al := List( [ 0 .. d - 1 ], i -> LD.alpha^i );
  Mz := z -> List( al, a -> Coefficients( LD.basis, a * z ) );
  for i in [ 1 .. N ] do
    for j in [ 1 .. N ] do
      if not IsZero( A[ i ][ j ] ) then
        R{ [ ( i - 1 ) * d + 1 .. i * d ] }{ [ ( j - 1 ) * d + 1 .. j * d ] }
          := Mz( A[ i ][ j ] );
      fi;
    od;
  od;
  return WALL_KMat( R );
end );

# K-Gram matrix of Tr_{Lambda/K} o H
BindGlobal( "WALL_RealizeForm", function( f, LD, H )
  local d, N, R, i, j, s, t, Q, Tr, tau;
  d := LD.d;
  if d = 1 then return H; fi;
  Q := f.q; N := Length( H );
  Tr := z -> Sum( [ 0 .. d - 1 ], i -> z^( Q^i ) );
  tau := z -> z^LD.T;
  R := NullMat( N * d, N * d, f.field );
  for i in [ 1 .. N ] do
    for j in [ 1 .. N ] do
      if not IsZero( H[ i ][ j ] ) then
        for s in [ 0 .. d - 1 ] do
          for t in [ 0 .. d - 1 ] do
            R[ ( i - 1 ) * d + s + 1 ][ ( j - 1 ) * d + t + 1 ] :=
              WALL_K( Tr( LD.alpha^s * H[ i ][ j ] * tau( LD.alpha^t ) ) );
          od;
        od;
      fi;
    od;
  od;
  return R;
end );

BindGlobal( "WALL_Shift", function( mu, L )
  local Y, i;
  Y := NullMat( mu, mu, L );
  for i in [ 1 .. mu - 1 ] do Y[ i ][ i + 1 ] := One( L ); od;
  return Y;
end );

# the scalar delta of the generalized Cayley transform
BindGlobal( "WALL_Delta", function( f, LD )
  if IsOddInt( f.p ) then return One( LD.L ); fi;
  return LD.w;                    # only GU in characteristic 2
end );

# generalized Cayley transform (delta+A)(tau(delta)-A)^-1 tau(delta)/delta
BindGlobal( "WALL_Cayley", function( f, LD, A )
  local I, de, tde;
  I := IdentityMat( Length( A ), LD.L );
  de := WALL_Delta( f, LD ); tde := de^LD.T;
  return ( de * I + A ) * ( tde * I - A )^-1 * ( tde / de );
end );

BindGlobal( "WALL_SelfDualComponent", function( f, c, part, signs )
  local K, LD, L, ml, comp, mm, mu, m, need, a, s, cval, h, kind, cc, beta,
        i, xmu, xs, Hs, k;
  K := f.field;
  LD := WALL_LambdaData( f, c, true );
  L := LD.L;
  ml := WALL_Mults( part );
  comp := rec( kind := "self", LD := LD, c := c, parts := [] );
  xs := []; Hs := [];
  for mm in ml do
    mu := mm[ 1 ]; m := mm[ 2 ];
    need := f.eps * (-1)^( mu - 1 );
    if LD.T = 1 then                                  # t - a, a = +-1
      a := LD.alpha;
      if need = 1 then
        s := First( signs, x -> x[ 1 ] = a and x[ 2 ] = mu )[ 3 ];
        if WALL_Leg( a^( m * ( mu - 1 ) ), f.q ) = s then cval := One( K );
        else cval := PrimitiveRoot( K ); fi;
        h := List( IdentityMat( m, K ), ShallowCopy );
        h[ m ][ m ] := cval;
        kind := "O";
      else
        h := NullMat( m, m, K );
        for i in [ 1 .. m / 2 ] do
          h[ i ][ m / 2 + i ] := One( K ); h[ m / 2 + i ][ i ] := -One( K );
        od;
        kind := "Sp";
      fi;
    else
      if need = 1 or f.p = 2 then cc := One( L );
      else cc := LD.w^( ( LD.T + 1 ) / 2 ); fi;
      h := cc * IdentityMat( m, L );
      kind := "U";
    fi;
    beta := NullMat( mu, mu, L );
    for i in [ 0 .. mu - 1 ] do beta[ i + 1 ][ mu - i ] := (-1)^i * One( L ); od;
    xmu := LD.alpha * WALL_Cayley( f, LD, WALL_Shift( mu, L ) );
    Add( xs, KroneckerProduct( IdentityMat( m, L ), xmu ) );
    Add( Hs, KroneckerProduct( h, beta ) );
    Add( comp.parts, rec( mu := mu, m := m, h := h, kind := kind ) );
  od;
  comp.xL := WALL_BlockDiag( L, xs );
  comp.HL := WALL_BlockDiag( L, Hs );
  comp.x := WALL_Realize( f, LD, comp.xL );
  comp.F := WALL_RealizeForm( f, LD, comp.HL );
  return comp;
end );

BindGlobal( "WALL_PairComponent", function( f, c, part )
  local K, LD, L, ml, comp, mm, xs, xW, N, i;
  K := f.field;
  LD := WALL_LambdaData( f, c, false );
  L := LD.L;
  ml := WALL_Mults( part );
  comp := rec( kind := "pair", LD := LD, c := c, parts := [] );
  xs := [];
  for mm in ml do
    Add( xs, KroneckerProduct( IdentityMat( mm[ 2 ], L ),
         LD.alpha * ( IdentityMat( mm[ 1 ], L ) + WALL_Shift( mm[ 1 ], L ) ) ) );
    Add( comp.parts, rec( mu := mm[ 1 ], m := mm[ 2 ], kind := "GL" ) );
  od;
  comp.xL := WALL_BlockDiag( L, xs );
  xW := WALL_Realize( f, LD, comp.xL );
  N := Length( xW );
  if IsBound( f.twist ) then
    comp.x := WALL_BlockDiag( K, [ xW, f.twist * WALL_Star( f, xW^-1 ) ] );
  else
    comp.x := WALL_BlockDiag( K, [ xW, WALL_Star( f, xW^-1 ) ] );
  fi;
  comp.F := NullMat( 2 * N, 2 * N, K );
  for i in [ 1 .. N ] do
    comp.F[ i ][ N + i ] := One( K ); comp.F[ N + i ][ i ] := f.eps * One( K );
  od;
  return comp;
end );

##
##  <#GAPDoc Label="WallModel">
##  <ManSection>
##  <Func Name="WallModel" Arg="f, inv"/>
##  <Returns>a record</Returns>
##  <Description>
##  (odd <M>q</M>) returns the model of the class with invariant
##  <A>inv</A>: a record with components <C>x</C> (the model element),
##  <C>F</C> (the model Gram matrix) and <C>comps</C> (data of the components
##  of the block diagonal decomposition). <Ref Func="WallRepresentative"/>
##  transports <C>x</C> to the form of <A>f</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# the model:  rec( x, F, comps )   with  x * F * x^* = F
BindGlobal( "WallModel", function( f, inv )
  local comps, p, c, dual;
  if IsBound( f.char2 ) then Error( "WallModel: not yet available in characteristic 2" ); fi;
  comps := [];
  for p in inv.polys do
    c := p[ 1 ]; dual := WALL_DualCoeffs( f, c );
    if dual = c then
      Add( comps, WALL_SelfDualComponent( f, c, p[ 2 ], inv.signs ) );
    elif c < dual then
      Add( comps, WALL_PairComponent( f, c, p[ 2 ] ) );
    fi;
  od;
  return rec( comps := comps,
              x := WALL_BlockDiag( f.field, List( comps, x -> x.x ) ),
              F := WALL_BlockDiag( f.field, List( comps, x -> x.F ) ) );
end );

##
##  <#GAPDoc Label="WallFormIsometry">
##  <ManSection>
##  <Func Name="WallFormIsometry" Arg="f, F0, F"/>
##  <Returns>a matrix</Returns>
##  <Description>
##  returns a matrix <M>S</M> with <M>S F0 \bar{S}^{tr} = F</M>, for two
##  equivalent Gram matrices <A>F0</A>, <A>F</A> of the kind given by <A>f</A>
##  (not for quadratic forms in characteristic <M>2</M>). An error is raised if
##  the forms are not equivalent.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# matrix S with S * F0 * S^* = F
BindGlobal( "WallFormIsometry", function( f, F0, F )
  local c0, c1;
  c0 := WALL_CanonicalBaseChange( f, F0 );
  c1 := WALL_CanonicalBaseChange( f, F );
  if c0.C <> c1.C then Error( "WallFormIsometry: forms not equivalent" ); fi;
  return c1.P^-1 * c0.P;
end );

#############################################################################
##  centralizers
#############################################################################

# generators of the isometry group of the (Lambda-)form h of a part
BindGlobal( "WALL_LeviPartGens", function( f, LD, part )
  local L, m, h, G, Fg, fh, fg, S, nu;
  L := LD.L; m := part.m;
  if IsBound( part.h ) then h := part.h; fi;
  if part.kind = "GL" then
    return GeneratorsOfGroup( GL( m, L ) );
  elif part.kind = "U" then
    # h = c * I, isometries of h = isometries of the hermitian form I
    G := GU( m, LD.T );
    Fg := InvariantSesquilinearForm( G ).matrix;
    fh := WallClassicalForm( "U", IdentityMat( m, L ), L );
    S := WallFormIsometry( fh, Fg, IdentityMat( m, L ) );
  elif part.kind = "Sp" then
    G := Sp( m, Size( L ) );
    Fg := InvariantBilinearForm( G ).matrix;
    fh := WallClassicalForm( "Sp", h, L );
    S := WallFormIsometry( fh, Fg, h );
  else
    if m = 1 then return [ [ [ -One( L ) ] ] ]; fi;
    fh := WallClassicalForm( "O", h, L );
    if IsOddInt( m ) then G := GO( m, Size( L ) );
    else G := GO( fh.sign, m, Size( L ) ); fi;
    Fg := InvariantBilinearForm( G ).matrix;
    if WALL_Leg( DeterminantMat( Fg ), Size( L ) ) <> fh.det then
      Fg := PrimitiveRoot( L ) * Fg;
    fi;
    S := WallFormIsometry( fh, Fg, h );
  fi;
  return List( GeneratorsOfGroup( G ), g -> S * g * S^-1 );
end );

# Lambda-basis of the radical of End_{Lambda[Y]}(M), graded by weight
# 2s + mu - nu  (map of a mu-block to a nu-block, e_i -> e_{i+s})
BindGlobal( "WALL_RadicalBasis", function( comp )
  local L, blocks, off, p, k, N, res, b1, b2, s, E, i, w;
  L := comp.LD.L;
  blocks := []; off := 0;
  for p in comp.parts do
    for k in [ 1 .. p.m ] do Add( blocks, [ off, p.mu ] ); off := off + p.mu; od;
  od;
  N := off;
  res := [];
  for b1 in blocks do
    for b2 in blocks do
      for s in [ Maximum( 0, b2[ 2 ] - b1[ 2 ] ) .. b2[ 2 ] - 1 ] do
        w := 2 * s + b1[ 2 ] - b2[ 2 ];
        if w = 0 then continue; fi;
        E := NullMat( N, N, L );
        for i in [ 0 .. b1[ 2 ] - 1 ] do
          if i + s < b2[ 2 ] then E[ b1[ 1 ] + i + 1 ][ b2[ 1 ] + i + s + 1 ] := One( L ); fi;
        od;
        if not IsBound( res[ w ] ) then res[ w ] := []; fi;
        Add( res[ w ], E );
      od;
    od;
  od;
  return res;
end );

# F_p-basis of a prime field subfield given by a primitive element
BindGlobal( "WALL_PrimeBasis", function( z )
  local d;
  d := DegreeFFE( z );
  return List( [ 0 .. d - 1 ], i -> z^i );
end );

# coordinates of a Lambda-matrix over the fixed field of tau
BindGlobal( "WALL_FixedFieldCoords", function( LD, A, theta )
  local v, z, x, y;
  v := [];
  for z in Concatenation( A ) do
    if theta = fail then Add( v, z );
    else
      y := ( z - z^LD.T ) / ( theta - theta^LD.T );
      x := z - y * theta;
      Add( v, x ); Add( v, y );
    fi;
  od;
  return v;
end );

BindGlobal( "WALL_FromFixedFieldCoords", function( LD, v, N, theta )
  local zs, i;
  if theta = fail then zs := v;
  else zs := List( [ 1 .. Length( v ) / 2 ], i -> v[ 2 * i - 1 ] + v[ 2 * i ] * theta ); fi;
  return List( [ 1 .. N ], i -> zs{ [ ( i - 1 ) * N + 1 .. i * N ] } );
end );

# generators (as Lambda-matrices) of the unipotent radical of a component
BindGlobal( "WALL_UnipotentGensL", function( f, comp )
  local LD, L, rad, N, gens, w, H, Hi, sharp, theta, cand, vecs, A, kap, B,
        z0, fp, bas, b, lam, E;
  LD := comp.LD; L := LD.L;
  rad := WALL_RadicalBasis( comp );
  N := Length( comp.xL );
  gens := [];
  if comp.kind = "pair" then
    fp := WALL_PrimeBasis( LD.w );
    for w in [ 1 .. Length( rad ) ] do
      if not IsBound( rad[ w ] ) then continue; fi;
      for E in rad[ w ] do
        for lam in fp do
          Add( gens, IdentityMat( N, L ) + lam * E );
        od;
      od;
    od;
    return gens;
  fi;
  H := comp.HL; Hi := H^-1;
  sharp := A -> TransposedMat( WALL_Frob( Hi * A * H, LD.T ) );
  if LD.T = 1 then theta := fail; z0 := LD.w;
  else theta := LD.w; z0 := LD.w^( LD.T + 1 ); fi;
  fp := WALL_PrimeBasis( z0 );               # F_p-basis of the fixed field
  for w in [ 1 .. Length( rad ) ] do
    if not IsBound( rad[ w ] ) then continue; fi;
    cand := [];
    for E in rad[ w ] do
      for kap in Concatenation( [ One( L ) ],
                                 Filtered( [ theta ], t -> t <> fail ) ) do
        A := kap * E;
        Add( cand, A - sharp( A ) );
      od;
    od;
    vecs := List( cand, A -> WALL_FixedFieldCoords( LD, A, theta ) );
    vecs := Filtered( vecs, v -> not IsZero( v ) );
    if Length( vecs ) = 0 then continue; fi;
    bas := BaseMat( vecs );
    for b in bas do
      B := WALL_FromFixedFieldCoords( LD, b, N, theta );
      for lam in fp do
        Add( gens, WALL_Cayley( f, LD, lam * B ) );
      od;
    od;
  od;
  return gens;
end );

# generators of the Levi part of a component (as Lambda-matrices)
BindGlobal( "WALL_LeviGensL", function( f, comp )
  local L, gens, off, sizes, p, i, g, blocks, j;
  L := comp.LD.L;
  sizes := List( comp.parts, p -> p.m * p.mu );
  gens := [];
  for i in [ 1 .. Length( comp.parts ) ] do
    p := comp.parts[ i ];
    for g in WALL_LeviPartGens( f, comp.LD, p ) do
      blocks := List( [ 1 .. Length( comp.parts ) ],
                  j -> IdentityMat( sizes[ j ], L ) );
      blocks[ i ] := KroneckerProduct( g, IdentityMat( p.mu, L ) );
      Add( gens, WALL_BlockDiag( L, blocks ) );
    od;
  od;
  return gens;
end );

# realize a Lambda-matrix commuting with comp.xL as an element of the
# centralizer of comp.x
BindGlobal( "WALL_RealizeCentralizing", function( f, comp, g )
  local G;
  G := WALL_Realize( f, comp.LD, g );
  if comp.kind = "pair" then
    return WALL_BlockDiag( f.field, [ G, WALL_Star( f, G^-1 ) ] );
  fi;
  return G;
end );

# embed component matrices into the full model
BindGlobal( "WALL_Embed", function( f, model, i, g )
  local blocks;
  blocks := List( model.comps, c -> IdentityMat( Length( c.x ), f.field ) );
  blocks[ i ] := g;
  return WALL_BlockDiag( f.field, blocks );
end );

BindGlobal( "WALL_PartName", function( f, LD, p )
  local Q;
  Q := Size( LD.L );
  if p.kind = "GL" then return Concatenation( "GL(", String( p.m ), ",", String( Q ), ")" );
  elif p.kind = "U" then return Concatenation( "GU(", String( p.m ), ",", String( LD.T ), ")" );
  elif p.kind = "Sp" then return Concatenation( "Sp(", String( p.m ), ",", String( Q ), ")" );
  elif p.m mod 2 = 1 then return Concatenation( "GO(", String( p.m ), ",", String( Q ), ")" );
  else
    if WallClassicalForm( "O", p.h, LD.L ).sign = 1 then
      return Concatenation( "GO+(", String( p.m ), ",", String( Q ), ")" );
    fi;
    return Concatenation( "GO-(", String( p.m ), ",", String( Q ), ")" );
  fi;
end );

##
##  <#GAPDoc Label="WallRepresentativeWithCentralizer">
##  <ManSection>
##  <Func Name="WallRepresentativeWithCentralizer" Arg="f, inv"/>
##  <Returns>a record</Returns>
##  <Description>
##  returns a record with components <C>representative</C> (as
##  <Ref Func="WallRepresentative"/>), <C>generators</C> (generators of its
##  centralizer in <M>G(F)</M>) and <C>centralizerOrder</C>. For odd <M>q</M>
##  there are further components <C>levi</C>, <C>unipotent</C> (generators of a
##  Levi complement and of the unipotent radical) and <C>leviType</C>. For even
##  <M>q</M> the generators are pseudo-random elements of the centralizer
##  (Las Vegas method; the order of the generated group is checked).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# representative and generators of its centralizer:
#   rec( representative, levi, unipotent, generators, leviType,
#        unipotentOrder, centralizerOrder )
BindGlobal( "WallRepresentativeWithCentralizer", function( f, inv )
  if IsBound( f.oddChar2 ) then return WALL2_OddRepresentativeWithCentralizer( f, inv ); fi;
  if IsBound( f.char2 ) then return WALL2_RepresentativeWithCentralizer( f, inv ); fi;
  if IsBound( f.twist ) then
    return WALL_RepWithCentFromModel( f, WALL3_Model( f, inv ), WallCentralizerOrder( f, inv ) );
  fi;
  return WALL_RepWithCentFromModel( f, WallModel( f, inv ), WallCentralizerOrder( f, inv ) );
end );

BindGlobal( "WALL_RepWithCentFromModel", function( f, model, ord )
  local S, Si, conj, levi, unip, i, comp, g, types, uord, res;
  S := WallFormIsometry( f, model.F, f.gram );
  Si := S^-1;
  conj := g -> S * g * Si;
  levi := []; unip := []; types := [];
  for i in [ 1 .. Length( model.comps ) ] do
    comp := model.comps[ i ];
    for g in WALL_LeviGensL( f, comp ) do
      Add( levi, conj( WALL_Embed( f, model, i,
                         WALL_RealizeCentralizing( f, comp, g ) ) ) );
    od;
    for g in WALL_UnipotentGensL( f, comp ) do
      Add( unip, conj( WALL_Embed( f, model, i,
                         WALL_RealizeCentralizing( f, comp, g ) ) ) );
    od;
    Append( types, List( comp.parts, p -> WALL_PartName( f, comp.LD, p ) ) );
  od;
  res := rec( representative := conj( model.x ),
              levi := levi, unipotent := unip,
              generators := Concatenation( levi, unip ),
              leviType := types,
              centralizerOrder := ord );
  return res;
end );

##
##  <#GAPDoc Label="WallRepresentative">
##  <ManSection>
##  <Func Name="WallRepresentative" Arg="f, inv"/>
##  <Returns>a matrix</Returns>
##  <Description>
##  returns a representative in <M>G(F)</M> of the class with invariant
##  <A>inv</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallRepresentative", function( f, inv )
  local model, S;
  if IsBound( f.oddChar2 ) then return WALL2_OddPreImage( f, WallRepresentative( f.sp, inv ) ); fi;
  if IsBound( f.twist ) then return WALL3_Representative( f, inv ); fi;
  if IsBound( f.char2 ) then return WALL2_Representative( f, inv ); fi;
  model := WallModel( f, inv );
  if model.x * model.F * WALL_Star( f, model.x ) <> model.F then
    Error( "WallRepresentative: model is not an isometry" );
  fi;
  S := WallFormIsometry( f, model.F, f.gram );
  return S * model.x * S^-1;
end );

##
##  <#GAPDoc Label="WallCentralizerGenerators">
##  <ManSection>
##  <Func Name="WallCentralizerGenerators" Arg="f, inv"/>
##  <Returns>a list of matrices</Returns>
##  <Description>
##  returns the component <C>generators</C> of
##  <Ref Func="WallRepresentativeWithCentralizer"/>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallCentralizerGenerators", function( f, inv )
  return WallRepresentativeWithCentralizer( f, inv ).generators;
end );

#############################################################################
##  conjugating elements
##
##  For x in G(F) we construct a basis P (rows) of V in which x acts as the
##  model x0 and the form has the model Gram matrix F0:
##      P * x * P^-1 = x0,   P * F * P^* = F0.
##  Then y = S * P (S * F0 * S^* = F) is in G(F) and y * x * y^-1 is the
##  representative WallRepresentative( f, WallInvariant( f, x ) ).
#############################################################################

# matrix of the action of lambda in Lambda on V_phi (lambda -> poly in s)
BindGlobal( "WALL_LambdaAct", function( f, LD, lam, spow )
  local co;
  if LD.d = 1 then return lam * spow[ 1 ]; fi;
  co := List( Coefficients( LD.basis, lam ), WALL_K );
  return Sum( [ 1 .. LD.d ], r -> co[ r ] * spow[ r ] );
end );

# Lambda-structure on the generalized eigenspace V_phi of x:
#   rec( B (K-basis of V_phi, global coords), xs (x on V_phi),
#        b (Lambda-basis, V_phi coords), bs[j][r] = b_j s^(r-1),
#        Y (Lambda-matrix), toL (K-vector -> Lambda-coords),
#        fromL (Lambda-coordinate row -> list of K-vectors for alpha^t) )
BindGlobal( "WALL_LambdaStructure", function( f, LD, x, c, selfdual )
  local K, d, pol, B, xs, n, J, s, spow, b, span, v, r, bs, Bfull, toL, u, I,
        Y, de, tde, cc, YL, res;
  K := f.field; d := LD.d;
  pol := UnivariatePolynomial( K, c );
  B := NullspaceMat( Value( pol, x )^Length( x ) );
  xs := List( B, row -> SolutionMat( B, row * x ) );
  n := Length( xs );
  I := IdentityMat( n, K );
  # semisimple part of xs
  if d = 1 then s := LD.alpha * I;
  else s := JordanDecomposition( xs )[ 1 ]; fi;
  spow := List( [ 0 .. d - 1 ], r -> s^r );
  # greedy Lambda-basis
  b := []; span := [];
  for v in I do
    if span = [] or RankMat( Concatenation( span, [ v ] ) ) > Length( span ) then
      Add( b, v );
      Append( span, List( spow, p -> v * p ) );
    fi;
    if Length( span ) = n then break; fi;
  od;
  bs := List( b, v -> List( spow, p -> v * p ) );
  Bfull := Concatenation( bs );           # order (j, r)
  toL := function( w )
    local co;
    co := SolutionMat( Bfull, w );
    return List( [ 1 .. Length( b ) ],
                 j -> Sum( [ 1 .. d ], r -> co[ ( j - 1 ) * d + r ] * LD.alpha^( r - 1 ) ) );
  end;
  # nilpotent Y with x = alpha * Gamma(Y)  (self-dual)  or alpha * (1+Y) (pair)
  u := s^-1 * xs;
  if not selfdual then
    Y := u - I;
  else
    de := WALL_Delta( f, LD ); tde := de^LD.T; cc := tde / de;
    Y := WALL_LambdaAct( f, LD, tde, spow ) * ( u - I )
         * ( u + WALL_LambdaAct( f, LD, cc, spow ) )^-1;
  fi;
  YL := List( b, v -> toL( v * Y ) );
  res := rec( B := B, xs := xs, b := b, bs := bs, spow := spow, YL := YL,
              toL := toL );
  # Lambda-row  ->  K-rows (alpha^t * row, t = 0..d-1) in global coordinates
  res.fromL := function( z )
    return WALL_KMat( List( [ 0 .. d - 1 ], t ->
      Sum( [ 1 .. Length( b ) ], j ->
        b[ j ] * WALL_LambdaAct( f, LD, LD.alpha^t * z[ j ], spow ) ) * B ) );
  end;
  return res;
end );

# Lambda-sesquilinear H with F = Tr o H on V_phi (self-dual case)
BindGlobal( "WALL_HFromF", function( f, LD, str, F )
  local d, Q, FB, Tr, TM, TMi, N, H, i, j, rhs, h, Bst;
  d := LD.d; Q := f.q;
  FB := str.B * F * WALL_Star( f, str.B );
  N := Length( str.b );
  Tr := z -> Sum( [ 0 .. d - 1 ], i -> z^( Q^i ) );
  TM := List( [ 0 .. d - 1 ], r -> List( [ 0 .. d - 1 ], r2 -> Tr( LD.alpha^( r + r2 ) ) ) );
  TMi := TM^-1;
  H := NullMat( N, N, LD.L );
  for i in [ 1 .. N ] do
    for j in [ 1 .. N ] do
      # rhs_r = F( b_i s^r, b_j )
      rhs := List( [ 1 .. d ], r -> ( [ str.bs[ i ][ r ] ] * FB
                                      * WALL_Star( f, [ str.b[ j ] ] ) )[ 1 ][ 1 ] );
      h := TMi * rhs;
      H[ i ][ j ] := Sum( [ 1 .. d ], r -> h[ r ] * LD.alpha^( r - 1 ) );
    od;
  od;
  return H;
end );

# Lambda-star
BindGlobal( "WALL_StarL", function( LD, M )
  if LD.T = 1 or LD.T = fail then return TransposedMat( M ); fi;
  return TransposedMat( WALL_Frob( M, LD.T ) );
end );

# tops: complement of ker Y^(mu-1) + (ker Y^(mu+1)) Y in ker Y^mu
BindGlobal( "WALL_Tops", function( Y, mu )
  local Km, Km1, Kp, S;
  Km  := NullspaceMat( Y^mu );
  Km1 := NullspaceMat( Y^( mu - 1 ) );
  Kp  := NullspaceMat( Y^( mu + 1 ) ) * Y;
  S := Filtered( Concatenation( Km1, Kp ), v -> not IsZero( v ) );
  if Length( S ) = 0 then return Km; fi;
  S := BaseMat( S );
  if Length( S ) = Length( Km ) then return []; fi;
  return BaseSteinitzVectors( Km, S ).factorspace;
end );

# form-type record for a part (to compute WallFormIsometry over Lambda)
BindGlobal( "WALL_PartFormRecord", function( f, LD, p, h )
  if p.kind = "U" then
    return WallClassicalForm( "U", h / p.h[ 1 ][ 1 ], LD.L );
  elif p.kind = "Sp" then return WallClassicalForm( "Sp", h, LD.L );
  else return WallClassicalForm( "O", h, LD.L ); fi;
end );

# adapted Lambda-basis for a self-dual component: rows of the result are in
# the Lambda-coordinates of str, ordered as in the model
BindGlobal( "WALL_AdaptedSelfDual", function( f, comp, str, H )
  local LD, L, zeta, de, Bsub, blocks, Ysub, Hsub, mu, Yp, tops, h1, p, S,
        fr, us, j, t, G, A, Ub, cmp, k, i, Z;
  LD := comp.LD; L := LD.L;
  if IsOddInt( f.p ) then zeta := One( L ) / 2;
  else de := WALL_Delta( f, LD ); zeta := de / ( de + de^LD.T ); fi;
  Bsub := IdentityMat( Length( H ), L );
  blocks := [];                     # blocks[mu] = list of rows u_k Y^i
  while Length( Bsub ) > 0 do
    Ysub := List( Bsub, v -> SolutionMat( Bsub, v * str.Yfull ) );
    Hsub := Bsub * H * WALL_StarL( LD, Bsub );
    mu := 1; Yp := Ysub;
    while not IsZero( Yp ) do Yp := Yp * Ysub; mu := mu + 1; od;
    tops := WALL_Tops( Ysub, mu );
    p := First( comp.parts, x -> x.mu = mu );
    h1 := tops * Hsub * WALL_StarL( LD, tops * Ysub^( mu - 1 ) );
    fr := WALL_PartFormRecord( f, LD, p, h1 );
    if p.kind = "U" then
      S := WallFormIsometry( fr, h1 / p.h[ 1 ][ 1 ], IdentityMat( p.m, L ) );
    else
      S := WallFormIsometry( fr, h1, p.h );
    fi;
    us := S * tops;
    for j in Reversed( [ 0 .. mu - 2 ] ) do
      t := mu - 1 - j;
      G := us * Hsub * WALL_StarL( LD, us * Ysub^j );
      A := -zeta * (-1)^t * G * p.h^-1;
      us := us + A * ( us * Ysub^t );
    od;
    Ub := Concatenation( List( us, u -> List( [ 0 .. mu - 1 ], i -> u * Ysub^i ) ) );
    blocks[ mu ] := Ub * Bsub;
    cmp := NullspaceMat( Hsub * WALL_StarL( LD, Ub ) );
    if Length( cmp ) = 0 then Bsub := [];
    else Bsub := cmp * Bsub; fi;
  od;
  Z := Concatenation( List( comp.parts, p -> blocks[ p.mu ] ) );
  return Z;
end );

BindGlobal( "WALL_AdaptedPair", function( f, comp, str )
  local blocks, p, tops, Y;
  Y := str.Yfull;
  return Concatenation( List( comp.parts, p ->
           Concatenation( List( WALL_Tops( Y, p.mu ),
             u -> List( [ 0 .. p.mu - 1 ], i -> u * Y^i ) ) ) ) );
end );

# adapted rows for a component (other than the unipotent one in char 2)
BindGlobal( "WALL_ComponentRows", function( f, x, comp )
  local LD, str, H, Z, PW, cd, Q, G, C;
  LD := comp.LD;
  str := WALL_LambdaStructure( f, LD, x, comp.c, comp.kind = "self" );
  str.Yfull := str.YL;
  if comp.kind = "self" then
    H := WALL_HFromF( f, LD, str, f.gram );
    Z := WALL_AdaptedSelfDual( f, comp, str, H );
    return Concatenation( List( Z, str.fromL ) );
  fi;
  Z := WALL_AdaptedPair( f, comp, str );
  PW := Concatenation( List( Z, str.fromL ) );
  cd := WALL_DualCoeffs( f, comp.c );
  Q := NullspaceMat( Value( UnivariatePolynomial( f.field, cd ), x )^f.n );
  G := PW * f.gram * WALL_Star( f, Q );
  C := WALL_Star( f, G^-1 ) * Q;
  return Concatenation( PW, C );
end );

##
##  <#GAPDoc Label="WallConjugatingElement">
##  <ManSection>
##  <Func Name="WallConjugatingElement" Arg="f, x"/>
##  <Returns>a record</Returns>
##  <Description>
##  For <A>x</A> <M>\in G(F)</M>, returns a record with components
##  <C>invariant</C> (the invariant of <A>x</A>), <C>representative</C> (the
##  class representative <M>r</M>, as <Ref Func="WallRepresentative"/>) and
##  <C>conjugator</C>, an element <M>y \in G(F)</M> with
##  <M>y x y^{-1} = r</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConjugatingElement", function( f, x )
  local inv, model, rows, comp, LD, str, H, Z, PW, cd, Q, G, C, P, S, y, rep;
  if IsBound( f.oddChar2 ) then return WALL2_OddConjugatingElement( f, x ); fi;
  if IsBound( f.twist ) then return WALL3_ConjugatingElement( f, x ); fi;
  if IsBound( f.char2 ) then return WALL2_ConjugatingElement( f, x ); fi;
  inv := WallInvariant( f, x );
  model := WallModel( f, inv );
  rows := [];
  for comp in model.comps do
    Append( rows, WALL_ComponentRows( f, x, comp ) );
  od;
  P := rows;
  if P * x <> model.x * P or P * f.gram * WALL_Star( f, P ) <> model.F then
    Error( "WallConjugatingElement: adapted basis failed" );
  fi;
  S := WallFormIsometry( f, model.F, f.gram );
  y := S * P;
  rep := S * model.x * S^-1;
  return rec( invariant := inv, representative := rep, conjugator := y );
end );

##
##  <#GAPDoc Label="WallIsConjugate">
##  <ManSection>
##  <Func Name="WallIsConjugate" Arg="f, x, z"/>
##  <Returns>a matrix or <K>fail</K></Returns>
##  <Description>
##  returns <M>g \in G(F)</M> with <M>g x g^{-1} = z</M> if <A>x</A> and
##  <A>z</A> are conjugate in <M>G(F)</M>, and <K>fail</K> otherwise. (Note that
##  &GAP;'s <Ref Func="RepresentativeAction" BookName="ref"/> uses the
##  convention <M>g^{-1} x g = z</M>.)
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# g in G(F) with g * x * g^-1 = z, or fail if not conjugate
BindGlobal( "WallIsConjugate", function( f, x, z )
  local a, b;
  if WallInvariant( f, x ) <> WallInvariant( f, z ) then return fail; fi;
  a := WallConjugatingElement( f, x );
  b := WallConjugatingElement( f, z );
  return b.conjugator^-1 * a.conjugator;
end );

##
##  <#GAPDoc Label="WallCentralizer">
##  <ManSection>
##  <Func Name="WallCentralizer" Arg="f, x"/>
##  <Returns>a list of matrices</Returns>
##  <Description>
##  returns generators of the centralizer of <A>x</A> in <M>G(F)</M>, for an
##  arbitrary element <A>x</A> <M>\in G(F)</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# generators of the centralizer of an arbitrary x in G(F)
BindGlobal( "WallCentralizer", function( f, x )
  local a, r, yi;
  a := WallConjugatingElement( f, x );
  r := WallRepresentativeWithCentralizer( f, a.invariant );
  yi := a.conjugator^-1;
  return List( r.generators, g -> yi * g * a.conjugator );
end );

#############################################################################
##  SO and Omega  (orthogonal groups, q odd)
##
##  pi(x) = [ det x, theta(x) ] in {+-1}^2, theta = spinor norm (Zassenhaus:
##  discriminant of Wall's form F_X on V(1-x)).  Omega = kernel of pi,
##  SO = kernel of det.  A GO-class with representative x0 splits into the
##  S-classes labelled by (target group of pi_S) / pi_S( C_GO(x0) ).
##  The S-class of x is labelled by pi_S(y) mod pi_S(C_GO(x0)), where y is
##  the GO-conjugator with y x y^-1 = x0.
##
##  An S-class invariant is  rec( inv := <GO-invariant>, label := [..] ).
#############################################################################

##
##  <#GAPDoc Label="WallSpinorNorm">
##  <ManSection>
##  <Func Name="WallSpinorNorm" Arg="f, x"/>
##  <Returns><M>1</M> or <M>-1</M></Returns>
##  <Description>
##  (orthogonal form, odd <M>q</M>) returns the spinor norm of <A>x</A>
##  <M>\in GO(F)</M> as a quadratic character value (<M>1</M> if it is a square).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# spinor norm (Legendre symbol) after Zassenhaus
BindGlobal( "WallSpinorNorm", function( f, x )
  local T, M, U, G;
  if IsBound( f.char2 ) then Error( "WallSpinorNorm: not yet available in characteristic 2" ); fi;
  T := IdentityMat( f.n, f.field ) - x;
  M := BaseMat( T );
  if Length( M ) = 0 then return 1; fi;
  U := List( M, m -> SolutionMat( T, m ) );       # u T = m
  G := U * f.gram * TransposedMat( M );            # (uT, vT) = B(u, vT)
  return WALL_Leg( DeterminantMat( G ), f.q );
end );

BindGlobal( "WALL_PiS", function( f, S, x )
  local d;
  if IsBound( f.char2 ) then
    # Dickson invariant: rank(1+x) mod 2
    if IsEvenInt( RankMat( x + IdentityMat( f.n, f.field ) ) ) then return [ 1 ]; fi;
    return [ -1 ];
  fi;
  if IsOne( DeterminantMat( x ) ) then d := 1; else d := -1; fi;
  if S = "SO" then return [ d ]; fi;
  return [ d, WallSpinorNorm( f, x ) ];
end );

BindGlobal( "WALL_PiMul", function( a, b ) return List( [ 1 .. Length( a ) ], i -> a[ i ] * b[ i ] ); end );

BindGlobal( "WALL_PiClosure", function( gens, len )
  local H, a, b, c;
  H := [ ListWithIdenticalEntries( len, 1 ) ];
  repeat
    c := Length( H );
    for a in ShallowCopy( H ) do
      for b in gens do
        if not WALL_PiMul( a, b ) in H then Add( H, WALL_PiMul( a, b ) ); fi;
      od;
    od;
  until Length( H ) = c;
  return Set( H );
end );

BindGlobal( "WALL_CheckS", function( f, S )
  if f.type = "U" then
    if S <> "SU" then Error( "for unitary forms S must be \"SU\"" ); fi;
    return;
  fi;
  if S = "SU" then Error( "SU only for unitary forms" ); fi;
  if f.type <> "O" then Error( "SO/Omega only for orthogonal forms" ); fi;
  if IsBound( f.oddChar2 ) then
    Error( "SO/Omega are not covered for odd dimension and even q" );
  fi;
  if IsBound( f.char2 ) and S = "SO" then
    Error( "in characteristic 2, SO = GO; use the functions for GO" );
  fi;
  if not S in [ "SO", "Omega" ] then Error( "S must be \"SO\" or \"Omega\"" ); fi;
end );

##
##  <#GAPDoc Label="WallDeterminantOfInvariant">
##  <ManSection>
##  <Func Name="WallDeterminantOfInvariant" Arg="f, inv"/>
##  <Returns><M>1</M> or <M>-1</M></Returns>
##  <Description>
##  (orthogonal form) returns the determinant of the elements with invariant
##  <A>inv</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# det and spinor norm read off from a GO-invariant
BindGlobal( "WallDeterminantOfInvariant", function( f, inv )
  local p;
  p := First( inv.polys, p -> p[ 1 ] = [ f.one, f.one ] );   # t + 1
  if p = fail or IsEvenInt( Sum( p[ 2 ] ) ) then return 1; fi;
  return -1;
end );

##
##  <#GAPDoc Label="WallDicksonInvariantOfInvariant">
##  <ManSection>
##  <Func Name="WallDicksonInvariantOfInvariant" Arg="f, inv"/>
##  <Returns><M>1</M> or <M>-1</M></Returns>
##  <Description>
##  (orthogonal form, even <M>q</M>) returns the value of
##  <Ref Func="WallDicksonInvariant"/> for the elements with invariant
##  <A>inv</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# Dickson invariant (as +-1) read off from the invariant (characteristic 2):
# rank(1+x) = n - (number of Jordan blocks for the eigenvalue 1)
BindGlobal( "WallDicksonInvariantOfInvariant", function( f, inv )
  local p;
  p := First( inv.polys, p -> p[ 1 ] = [ f.one, f.one ] );
  if p = fail or IsEvenInt( Length( p[ 2 ] ) ) then return 1; fi;
  return -1;
end );

##
##  <#GAPDoc Label="WallDicksonInvariant">
##  <ManSection>
##  <Func Name="WallDicksonInvariant" Arg="f, x"/>
##  <Returns><M>1</M> or <M>-1</M></Returns>
##  <Description>
##  (orthogonal form, even <M>q</M>) returns <M>(-1)^{D(x)}</M>, where
##  <M>D(x)</M> is the rank of <M>1+x</M> modulo <M>2</M> (the Dickson invariant);
##  <M>\Omega</M> is its kernel.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallDicksonInvariant", function( f, x )
  return WALL_PiS( f, "Omega", x )[ 1 ];
end );

##
##  <#GAPDoc Label="WallSpinorNormOfInvariant">
##  <ManSection>
##  <Func Name="WallSpinorNormOfInvariant" Arg="f, inv"/>
##  <Returns><M>1</M> or <M>-1</M></Returns>
##  <Description>
##  (orthogonal form, odd <M>q</M>) returns the spinor norm, as in
##  <Ref Func="WallSpinorNorm"/>, of the elements with invariant <A>inv</A> and
##  determinant <M>1</M>, read off from the invariant.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSpinorNormOfInvariant", function( f, inv )
  local q, lm1, res, p, c, d, dual, s;
  q := f.q; lm1 := WALL_Leg( -f.one, q ); res := 1;
  for p in inv.polys do
    c := p[ 1 ]; d := Length( c ) - 1; dual := WALL_DualCoeffs( f, c );
    if d = 1 and dual = c then continue; fi;
    if dual = c then
      res := res * ( - lm1^( d / 2 ) * WALL_Leg( Sum( c ), q ) )^Sum( p[ 2 ] );
    elif c < dual then
      res := res * ( lm1^d * WALL_Leg( c[ 1 ], q ) )^Sum( p[ 2 ] );
    fi;
  od;
  for s in inv.signs do
    if s[ 1 ] = -f.one and IsOddInt( s[ 2 ] ) then res := res * s[ 3 ]; fi;
  od;
  return res;
end );

##
##  <#GAPDoc Label="WallPiImageOfCentralizer">
##  <ManSection>
##  <Func Name="WallPiImageOfCentralizer" Arg="f, inv"/>
##  <Returns>a list</Returns>
##  <Description>
##  (orthogonal form) returns the image of the centralizer in <M>GO(F)</M> of
##  an element with invariant <A>inv</A> under <M>\pi = </M> (determinant, spinor
##  norm), as a list of pairs in <M>\{\pm 1\}^2</M> (odd <M>q</M>), resp. under the
##  Dickson invariant, as a list of lists <M>[\pm 1]</M> (even <M>q</M>).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# pi( C_GO(x) ) in {+-1}^2, read off from the invariant
BindGlobal( "WallPiImageOfCentralizer", function( f, inv )
  local gens, l2, p, c, d, dual, mm, s, a;
  if IsBound( f.char2 ) then
    # Dickson image of C(x): non-trivial iff the eigenvalue 1 has an odd part
    # or an even part with s = 1
    p := First( inv.polys, p -> p[ 1 ] = [ f.one, f.one ] );
    if p <> fail and ( ForAny( p[ 2 ], IsOddInt ) or ForAny( inv.s, a -> a[ 2 ] = 1 ) ) then
      return [ [ -1 ], [ 1 ] ];
    fi;
    return [ [ 1 ] ];
  fi;
  gens := [];
  l2 := WALL_Leg( 2 * f.one, f.q );
  for p in inv.polys do
    c := p[ 1 ]; d := Length( c ) - 1; dual := WALL_DualCoeffs( f, c );
    if d = 1 and dual = c then                       # t -+ 1
      a := -c[ 1 ];
      for mm in WALL_Mults( p[ 2 ] ) do
        if IsOddInt( mm[ 1 ] ) then
          if mm[ 2 ] >= 2 then
            Append( gens, [ [ -1, 1 ], [ -1, -1 ] ] );
          else
            s := First( inv.signs, x -> x[ 1 ] = a and x[ 2 ] = mm[ 1 ] )[ 3 ];
            Add( gens, [ -1, l2 * s ] );
          fi;
        fi;
      od;
    elif dual = c or c < dual then
      if ForAny( p[ 2 ], IsOddInt ) then Add( gens, [ 1, -1 ] ); fi;
    fi;
  od;
  return WALL_PiClosure( gens, 2 );
end );

BindGlobal( "WALL_ProjS", function( S, H )
  if Length( H[ 1 ] ) = 1 then return H; fi;          # characteristic 2
  if S = "SO" then return Set( H, h -> [ h[ 1 ] ] ); fi;
  return H;
end );

# canonical labels = minimal elements of the cosets of H in {+-1}^k
BindGlobal( "WALL_Labels", function( k, H )
  local all;
  all := Set( Tuples( [ -1, 1 ], k ) );
  return Set( all, a -> Minimum( List( H, h -> WALL_PiMul( a, h ) ) ) );
end );
BindGlobal( "WALL_LabelOf", function( a, H )
  return Minimum( List( H, h -> WALL_PiMul( a, h ) ) );
end );

##
##  <#GAPDoc Label="WallIsInSubgroup">
##  <ManSection>
##  <Func Name="WallIsInSubgroup" Arg="f, S, x"/>
##  <Returns><K>true</K> or <K>false</K></Returns>
##  <Description>
##  tests whether <A>x</A> lies in the subgroup <A>S</A> of <M>G(F)</M>.
##  Here <A>S</A> is <C>"SO"</C> or <C>"Omega"</C> for orthogonal forms (for even
##  <M>q</M> only <C>"Omega"</C>, since <M>SO = GO</M>), and <C>"SU"</C> for
##  unitary forms; the same values of <A>S</A> are used in all functions of this
##  section.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallIsInSubgroup", function( f, S, x )
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SUIsInSubgroup( f, x ); fi;
  if not WallIsInGroup( f, x ) then return false; fi;
  return ForAll( WALL_PiS( f, S, x ), IsOne );
end );

##
##  <#GAPDoc Label="WallSubgroupOrder">
##  <ManSection>
##  <Func Name="WallSubgroupOrder" Arg="f, S"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  returns the order of the subgroup <A>S</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSubgroupOrder", function( f, S )
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SUOrder( f ); fi;
  if S = "SO" or IsBound( f.char2 ) then return WallGroupOrder( f ) / 2; fi;
  return WallGroupOrder( f ) / 4;
end );

##
##  <#GAPDoc Label="WallSubgroupClassInvariants">
##  <ManSection>
##  <Func Name="WallSubgroupClassInvariants" Arg="f, S"/>
##  <Returns>a list of records</Returns>
##  <Description>
##  returns the invariants of all conjugacy classes of the subgroup
##  <A>S</A>: records <C>rec( inv, label )</C>, where <C>inv</C> is the invariant
##  of the class of <M>G(F)</M> containing the class, and <C>label</C> numbers the
##  classes of <A>S</A> into which it splits (for <C>"SO"</C>, <C>"Omega"</C> a list
##  of signs, for <C>"SU"</C> an integer <M>e</M>, the class of
##  <M>r_e^{-1} x_0 r_e</M> with <M>\det(r_e) = \omega^e</M>,
##  <M>\omega = Z(r^2)^{r-1}</M>).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSubgroupClassInvariants", function( f, S )
  local res, inv, H, k, l;
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SUClassInvariants( f ); fi;
  if S = "SO" or IsBound( f.char2 ) then k := 1; else k := 2; fi;
  res := [];
  for inv in WallClassInvariants( f ) do
    if IsBound( f.char2 ) then
      if WallDicksonInvariantOfInvariant( f, inv ) <> 1 then continue; fi;
    else
      if WallDeterminantOfInvariant( f, inv ) <> 1 then continue; fi;
      if S = "Omega" and WallSpinorNormOfInvariant( f, inv ) <> 1 then continue; fi;
    fi;
    H := WALL_ProjS( S, WallPiImageOfCentralizer( f, inv ) );
    for l in WALL_Labels( k, H ) do
      Add( res, rec( inv := inv, label := l ) );
    od;
  od;
  return res;
end );

##
##  <#GAPDoc Label="WallSubgroupNrClasses">
##  <ManSection>
##  <Func Name="WallSubgroupNrClasses" Arg="f, S"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  returns the number of conjugacy classes of the subgroup <A>S</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSubgroupNrClasses", function( f, S )
  return Length( WallSubgroupClassInvariants( f, S ) );
end );

##
##  <#GAPDoc Label="WallSubgroupCentralizerOrder">
##  <ManSection>
##  <Func Name="WallSubgroupCentralizerOrder" Arg="f, S, sinv"/>
##  <Func Name="WallSubgroupClassSize" Arg="f, S, sinv"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  return the centralizer order in <A>S</A> and the size of the class of
##  <A>S</A> with invariant <A>sinv</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSubgroupCentralizerOrder", function( f, S, sinv )
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SUCentralizerOrder( f, sinv ); fi;
  return WallCentralizerOrder( f, sinv.inv ) /
         Length( WALL_ProjS( S, WallPiImageOfCentralizer( f, sinv.inv ) ) );
end );

BindGlobal( "WallSubgroupClassSize", function( f, S, sinv )
  return WallSubgroupOrder( f, S ) / WallSubgroupCentralizerOrder( f, S, sinv );
end );

# elements of GO with prescribed pi = [det, theta]  (cached in f)
BindGlobal( "WALL_PiElements", function( f )
  local K, P, n, refl, cand, v, w, x, r, pi, res, a, b;
  if IsBound( f.piElements ) then return f.piElements; fi;
  K := f.field; n := f.n;
  if IsBound( f.char2 ) then
    # orthogonal transvection (reflection) u -> u + B(u,v)/Q(v) v
    v := First( IdentityMat( n, K ), e -> not IsZero( e * f.quad * e ) );
    if v = fail then
      v := First( Combinations( IdentityMat( n, K ), 2 ), c -> not IsZero( Sum( c ) * f.quad * Sum( c ) ) );
      v := Sum( v );
    fi;
    r := IdentityMat( n, K ) + ( 1 / ( v * f.quad * v ) ) * TransposedMat( [ v * f.gram ] ) * [ v ];
    f.piElements := [ [ [ 1 ], IdentityMat( n, K ) ], [ [ -1 ], r ] ];
    return f.piElements;
  fi;
  refl := function( v )
    local Q;
    Q := v * f.gram * v;
    return IdentityMat( n, K ) - ( 2 / Q ) * TransposedMat( [ v * f.gram ] ) * [ v ];
  end;
  P := WALL_CanonicalBaseChange( f, f.gram ).P;     # orthogonal basis
  cand := ShallowCopy( P );
  if n >= 2 then
    for x in List( [ 1 .. Size( K ) - 1 ], i -> PrimitiveRoot( K )^i ) do
      Add( cand, P[ 1 ] + x * P[ 2 ] );
    od;
  fi;
  res := [ [ [ 1, 1 ], IdentityMat( n, K ) ] ];
  for v in cand do
    if IsZero( v * f.gram * v ) then continue; fi;
    r := refl( v );
    pi := WALL_PiS( f, "Omega", r );
    if not pi in List( res, a -> a[ 1 ] ) then Add( res, [ pi, r ] ); fi;
  od;
  # products of two reflections
  for a in ShallowCopy( res ) do
    for b in ShallowCopy( res ) do
      pi := WALL_PiMul( a[ 1 ], b[ 1 ] );
      if not pi in List( res, c -> c[ 1 ] ) then Add( res, [ pi, a[ 2 ] * b[ 2 ] ] ); fi;
    od;
  od;
  if Length( res ) < 4 then Error( "WALL_PiElements: pi not surjective" ); fi;
  f.piElements := res;
  return res;
end );

BindGlobal( "WALL_ElementWithPi", function( f, S, t )
  return First( WALL_PiElements( f ), a -> a[ 1 ]{ [ 1 .. Length( t ) ] } = t )[ 2 ];
end );

# transversal of ker(pi_S) in <gens> and Schreier generators of the kernel
BindGlobal( "WALL_KernelGens", function( f, S, gens )
  local one, T, imgs, i, g, s, im, kgens, pis, pg;
  one := IdentityMat( f.n, f.field );
  pis := List( gens, g -> WALL_PiS( f, S, g ) );
  T := [ one ]; imgs := [ WALL_PiS( f, S, one ) ];
  i := 1;
  while i <= Length( T ) do
    for g in [ 1 .. Length( gens ) ] do
      im := WALL_PiMul( imgs[ i ], pis[ g ] );
      if not im in imgs then Add( T, T[ i ] * gens[ g ] ); Add( imgs, im ); fi;
    od;
    i := i + 1;
  od;
  kgens := [];
  for i in [ 1 .. Length( T ) ] do
    for g in [ 1 .. Length( gens ) ] do
      s := T[ i ] * gens[ g ];
      im := WALL_PiMul( imgs[ i ], pis[ g ] );
      s := s * T[ Position( imgs, im ) ]^-1;
      if s <> one then AddSet( kgens, s ); fi;
    od;
  od;
  return rec( transversal := T, images := imgs, kernel := kgens );
end );

##
##  <#GAPDoc Label="WallSubgroupRepresentativeWithCentralizer">
##  <ManSection>
##  <Func Name="WallSubgroupRepresentativeWithCentralizer" Arg="f, S, sinv"/>
##  <Returns>a record</Returns>
##  <Description>
##  returns a record with components <C>representative</C>,
##  <C>generators</C> (of its centralizer in <A>S</A>) and
##  <C>centralizerOrder</C>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# representative of an S-class and generators of its centralizer in S
BindGlobal( "WallSubgroupRepresentativeWithCentralizer", function( f, S, sinv )
  local r, x0, rt, rti, K;
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SURepresentativeWithCentralizer( f, sinv ); fi;
  r := WallRepresentativeWithCentralizer( f, sinv.inv );
  x0 := r.representative;
  rt := WALL_ElementWithPi( f, S, sinv.label );
  rti := rt^-1;
  K := WALL_KernelGens( f, S, r.generators );
  return rec( representative := rti * x0 * rt,
              generators := List( K.kernel, g -> rti * g * rt ),
              centralizerOrder := WallSubgroupCentralizerOrder( f, S, sinv ) );
end );

##
##  <#GAPDoc Label="WallSubgroupRepresentative">
##  <ManSection>
##  <Func Name="WallSubgroupRepresentative" Arg="f, S, sinv"/>
##  <Returns>a matrix</Returns>
##  <Description>
##  returns a representative of the class of the subgroup <A>S</A> with
##  invariant <A>sinv</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSubgroupRepresentative", function( f, S, sinv )
  local x0, rt;
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SURepresentative( f, sinv ); fi;
  x0 := WallRepresentative( f, sinv.inv );
  rt := WALL_ElementWithPi( f, S, sinv.label );
  return rt^-1 * x0 * rt;
end );

##
##  <#GAPDoc Label="WallSubgroupConjugatingElement">
##  <ManSection>
##  <Func Name="WallSubgroupConjugatingElement" Arg="f, S, x"/>
##  <Returns>a record</Returns>
##  <Description>
##  For <A>x</A> in the subgroup <A>S</A>, returns a record with components
##  <C>invariant</C>, <C>representative</C> <M>r</M> and <C>conjugator</C>
##  <M>y \in S</M> with <M>y x y^{-1} = r</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
# S-class invariant of x in S, a conjugator y in S with y x y^-1 the
# representative, and the GO-data
BindGlobal( "WallSubgroupConjugatingElement", function( f, S, x )
  local a, H, t, rt, r, K, need, c, y;
  WALL_CheckS( f, S );
  if S = "SU" then return WALL_SUConjugatingElement( f, x ); fi;
  if not WallIsInSubgroup( f, S, x ) then Error( "x is not in ", S ); fi;
  a := WallConjugatingElement( f, x );                  # y0 x y0^-1 = x0
  H := WALL_ProjS( S, WallPiImageOfCentralizer( f, a.invariant ) );
  t := WALL_LabelOf( WALL_PiS( f, S, a.conjugator ), H );
  rt := WALL_ElementWithPi( f, S, t );
  # need c in C(x0) with pi(c) = pi(rt) * pi(y0)  (then y = rt^-1 c y0 in S)
  need := WALL_PiMul( WALL_PiS( f, S, rt ), WALL_PiS( f, S, a.conjugator ) );
  r := WallRepresentativeWithCentralizer( f, a.invariant );
  K := WALL_KernelGens( f, S, r.generators );
  c := K.transversal[ Position( K.images, need ) ];
  y := rt^-1 * c * a.conjugator;
  return rec( invariant := rec( inv := a.invariant, label := t ),
              representative := rt^-1 * a.representative * rt,
              conjugator := y );
end );

##
##  <#GAPDoc Label="WallSubgroupInvariant">
##  <ManSection>
##  <Func Name="WallSubgroupInvariant" Arg="f, S, x"/>
##  <Returns>a record</Returns>
##  <Description>
##  returns the class invariant <C>rec( inv, label )</C> of <A>x</A> in the
##  subgroup <A>S</A>; two elements of <A>S</A> are conjugate in <A>S</A> if and
##  only if their invariants are equal.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallSubgroupInvariant", function( f, S, x )
  return WallSubgroupConjugatingElement( f, S, x ).invariant;
end );

#############################################################################
##  SU  (unitary groups, all q; GU(n,r) over GF(r^2))
##
##  det : GU -> mu_{r+1} = < omega >, omega = Z^(r-1), SU = kernel.  We use
##  exponents e mod r+1 (det = omega^e).  det( C_GU(x) ) = < omega^g >,
##  g = gcd( r+1, all parts of all partitions lambda_phi ), so the GU-class
##  of x0 in SU splits into g SU-classes, labelled by e mod g; the label of
##  x = y^-1 x0 y is det(y) mod < omega^g >.
##  An SU-class invariant is  rec( inv := <GU-invariant>, label := e ),
##  0 <= e < g.
#############################################################################

BindGlobal( "WALL_SUOmega", function( f )
  return PrimitiveRoot( f.field )^( f.r - 1 );
end );

BindGlobal( "WALL_SUDetExp", function( f, x )
  return LogFFE( DeterminantMat( x ), WALL_SUOmega( f ) );
end );

# exponent of det for an element with GU-invariant inv
BindGlobal( "WALL_SUDetExpOfInvariant", function( f, inv )
  local d, p, c;
  d := f.one;
  for p in inv.polys do
    c := p[ 1 ];
    d := d * ( ( -f.one )^( Length( c ) - 1 ) * c[ 1 ] )^Sum( p[ 2 ] );
  od;
  return LogFFE( d, WALL_SUOmega( f ) );
end );

# g with det( C_GU(x) ) = < omega^g >
BindGlobal( "WALL_SUGcd", function( f, inv )
  return Gcd( Concatenation( [ f.r + 1 ], Concatenation( List( inv.polys, p -> p[ 2 ] ) ) ) );
end );

BindGlobal( "WALL_SUIsInSubgroup", function( f, x )
  return WallIsInGroup( f, x ) and IsOne( DeterminantMat( x ) );
end );

BindGlobal( "WALL_SUOrder", function( f )
  return WallGroupOrder( f ) / ( f.r + 1 );
end );

BindGlobal( "WALL_SUClassInvariants", function( f )
  local res, inv;
  res := [];
  for inv in WallClassInvariants( f ) do
    if WALL_SUDetExpOfInvariant( f, inv ) = 0 then
      Append( res, List( [ 0 .. WALL_SUGcd( f, inv ) - 1 ], e -> rec( inv := inv, label := e ) ) );
    fi;
  od;
  return res;
end );

BindGlobal( "WALL_SUCentralizerOrder", function( f, sinv )
  return WallCentralizerOrder( f, sinv.inv ) * WALL_SUGcd( f, sinv.inv ) / ( f.r + 1 );
end );

# element of GU with det omega^e: u -> u + (omega^e - 1) B(u,v)/B(v,v) v,
# v anisotropic
BindGlobal( "WALL_SUElementWithDet", function( f, e )
  local v, col;
  if not IsBound( f.suVector ) then
    f.suVector := WALL_CanonicalBaseChange( f, f.gram ).P[ 1 ];
  fi;
  v := f.suVector;
  col := f.gram * List( v, z -> z^f.r );                  # B(u,v) = u * col
  return IdentityMat( f.n, f.field ) +
         ( ( WALL_SUOmega( f )^e - f.one ) / ( v * col ) ) * TransposedMat( [ col ] ) * [ v ];
end );

# transversal of ker(det) in <gens> (indexed by det exponents) and Schreier
# generators of the kernel
BindGlobal( "WALL_SUKernelGens", function( f, gens )
  local N, one, T, imgs, es, i, g, s, im, kgens;
  N := f.r + 1;
  one := IdentityMat( f.n, f.field );
  es := List( gens, g -> WALL_SUDetExp( f, g ) );
  T := [ one ]; imgs := [ 0 ];
  i := 1;
  while i <= Length( T ) do
    for g in [ 1 .. Length( gens ) ] do
      im := ( imgs[ i ] + es[ g ] ) mod N;
      if not im in imgs then Add( T, T[ i ] * gens[ g ] ); Add( imgs, im ); fi;
    od;
    i := i + 1;
  od;
  kgens := [];
  for i in [ 1 .. Length( T ) ] do
    for g in [ 1 .. Length( gens ) ] do
      im := ( imgs[ i ] + es[ g ] ) mod N;
      s := T[ i ] * gens[ g ] * T[ Position( imgs, im ) ]^-1;
      if s <> one then AddSet( kgens, s ); fi;
    od;
  od;
  return rec( transversal := T, images := imgs, kernel := kgens );
end );

BindGlobal( "WALL_SURepresentativeWithCentralizer", function( f, sinv )
  local r, rt, rti, K;
  r := WallRepresentativeWithCentralizer( f, sinv.inv );
  rt := WALL_SUElementWithDet( f, sinv.label );
  rti := rt^-1;
  K := WALL_SUKernelGens( f, r.generators );
  if Length( K.images ) * WALL_SUGcd( f, sinv.inv ) <> f.r + 1 then
    Error( "WALL_SURepresentativeWithCentralizer: det(C) has wrong order" );
  fi;
  return rec( representative := rti * r.representative * rt,
              generators := List( K.kernel, g -> rti * g * rt ),
              centralizerOrder := WALL_SUCentralizerOrder( f, sinv ) );
end );

BindGlobal( "WALL_SURepresentative", function( f, sinv )
  local rt;
  rt := WALL_SUElementWithDet( f, sinv.label );
  return rt^-1 * WallRepresentative( f, sinv.inv ) * rt;
end );

BindGlobal( "WALL_SUConjugatingElement", function( f, x )
  local a, N, e0, t, rt, r, K, need, pos, c;
  if not WALL_SUIsInSubgroup( f, x ) then Error( "x is not in SU" ); fi;
  a := WallConjugatingElement( f, x );                  # y0 x y0^-1 = x0
  N := f.r + 1;
  e0 := WALL_SUDetExp( f, a.conjugator );
  t := e0 mod WALL_SUGcd( f, a.invariant );
  rt := WALL_SUElementWithDet( f, t );
  # c in C(x0) with det c = det(rt) / det(y0); then y = rt^-1 c y0 in SU
  need := ( t - e0 ) mod N;
  r := WallRepresentativeWithCentralizer( f, a.invariant );
  K := WALL_SUKernelGens( f, r.generators );
  pos := Position( K.images, need );
  if pos = fail then Error( "WALL_SUConjugatingElement: det(C) too small" ); fi;
  c := K.transversal[ pos ];
  return rec( invariant := rec( inv := a.invariant, label := t ),
              representative := rt^-1 * a.representative * rt,
              conjugator := rt^-1 * c * a.conjugator );
end );

#############################################################################
#############################################################################
##
##  CHARACTERISTIC 2:  Sp(2m,q) and GO+-(2m,q), q even   (Wall, Section 3)
##
##  Orthogonal forms are given by a quadratic form Q(v) = v * Qm * v^T
##  (any matrix Qm; it is normalized to upper triangular form).
##  Away from the eigenvalue 1 everything is as for odd q.  At the
##  eigenvalue 1 the invariant has, besides the partition, the data of
##  Wall 3.7:  bits s for the even parts, component sets and their
##  "partial second discriminants" delta in {0,1} (meaning 0 or delta).
##
#############################################################################
#############################################################################

# trace F_q -> F_2 (Arf invariants live in F_q / {x^2+x} = F_2 via trace)
BindGlobal( "WALL2_Tr2", function( z, q )
  local e;
  e := LogInt( q, 2 );
  return Sum( [ 0 .. e - 1 ], i -> z^( 2^i ) );
end );

BindGlobal( "WALL2_Form", function( type, F, K )
  local f, n, q, Qm, i, j, sp, c, P, k, a;
  n := Length( F ); q := Size( K );
  f := rec( type := type, field := K, n := n, p := 2, one := One( K ),
            q := q, sigma := 1, eps := 1, char2 := true );
  if IsOddInt( n ) then
    if type = "O" then return WALL2_OddForm( F, K ); fi;
    Error( "WallClassicalForm: an alternating form needs even dimension" );
  fi;
  if type = "Sp" then
    if TransposedMat( F ) <> F or ForAny( [ 1 .. n ], i -> not IsZero( F[ i ][ i ] ) ) then
      Error( "WallClassicalForm: not alternating" );
    fi;
    f.gram := Immutable( F );
  else
    Qm := List( F, ShallowCopy );
    for i in [ 1 .. n ] do
      for j in [ 1 .. i - 1 ] do
        Qm[ j ][ i ] := Qm[ j ][ i ] + Qm[ i ][ j ]; Qm[ i ][ j ] := Zero( K );
      od;
    od;
    f.quad := Immutable( Qm );
    f.gram := Immutable( Qm + TransposedMat( Qm ) );
  fi;
  if IsZero( DeterminantMat( f.gram ) ) then
    Error( "WallClassicalForm: degenerate form" );
  fi;
  if type = "O" then
    # Arf invariant via a symplectic basis of the polar form
    sp := WALL_CanonicalBaseChange( rec( type := "Sp", field := K, sigma := 1 ), f.gram );
    P := sp.P; k := n / 2;
    a := Sum( [ 1 .. k ], i -> ( P[ i ] * f.quad * P[ i ] ) *
                               ( P[ k + i ] * f.quad * P[ k + i ] ) );
    f.arf := IntFFE( WALL2_Tr2( a, q ) );
    if f.arf = 0 then f.sign := 1; else f.sign := -1; fi;
  fi;
  return f;
end );

#############################################################################
##  Wall's data at the eigenvalue 1 (Theorem 3.7.2) in terms of x:
##    part   : Jordan partition of x at eigenvalue 1
##             (odd parts have even multiplicity)
##    s      : list of [ m, s_m ] for the even parts m, s_m in {0,1}
##             (s_m = 1 forced if the multiplicity of m is odd);
##             Wall's index lambda = m - 1 (odd), s_lambda = s_m
##    P-indices: e = m - 1 for the parts m >= 2
##    component sets: maximal runs of P-indices without "gap" (Wall 3.5)
##    deltas : list of [ L, d ], L a component set (list of P-indices) whose
##             partial second discriminant is not forced to 0, d in {0,1}
##    delta0 : (orthogonal only, if s_2 = 0 and 1 is a part) in {0,1}: Arf
##             invariant of the core of Q on the fixed space of x
#############################################################################

BindGlobal( "WALL2_SOf", function( slist, m )
  local a;
  a := First( slist, x -> x[ 1 ] = m );
  if a = fail then return 0; fi;
  return a[ 2 ];
end );

BindGlobal( "WALL2_ComponentSets", function( part, slist )
  local idx, sets, cur, i, a, b, gap, k;
  idx := Set( Filtered( part, m -> m >= 2 ), m -> m - 1 );
  sets := [];
  if idx = [] then return sets; fi;
  cur := [ idx[ 1 ] ];
  for i in [ 2 .. Length( idx ) ] do
    a := idx[ i - 1 ]; b := idx[ i ];
    gap := ForAny( [ a + 1 .. b - 1 ], IsOddInt )
           or ( IsOddInt( a ) and WALL2_SOf( slist, a + 1 ) = 0 )
           or ( IsOddInt( b ) and WALL2_SOf( slist, b + 1 ) = 0 );
    if gap then Add( sets, cur ); cur := [ b ];
    else Add( cur, b ); fi;
  od;
  Add( sets, cur );
  return sets;
end );

# is the partial second discriminant of the component set L free?
BindGlobal( "WALL2_DeltaFree", function( type, L, slist )
  if Length( L ) = 1 and IsOddInt( L[ 1 ] ) and WALL2_SOf( slist, L[ 1 ] + 1 ) = 0 then
    return false;
  fi;
  if type = "Sp" and 1 in L and WALL2_SOf( slist, 2 ) = 1 then return false; fi;
  return true;
end );

# all data (part, s, deltas, delta0) for a unipotent part of size n1
BindGlobal( "WALL2_UnipotentOptions", function( type, n1 )
  local res, part, evens, sch, sl, comps, free, dch, d0ch, dl, d0, c;
  res := [];
  for part in Partitions( n1 ) do
    if not ForAll( Set( Filtered( part, IsOddInt ) ),
                   m -> IsEvenInt( Number( part, i -> i = m ) ) ) then continue; fi;
    evens := Set( Filtered( part, IsEvenInt ) );
    sch := Cartesian( List( evens, m -> Filtered( [ 0, 1 ], b ->
             b = 1 or IsEvenInt( Number( part, i -> i = m ) ) ) ) );
    for c in sch do
      sl := List( [ 1 .. Length( evens ) ], i -> [ evens[ i ], c[ i ] ] );
      comps := WALL2_ComponentSets( part, sl );
      free := Filtered( comps, L -> WALL2_DeltaFree( type, L, sl ) );
      if type = "O" and WALL2_SOf( sl, 2 ) = 0 and 1 in part then d0ch := [ 0, 1 ];
      else d0ch := [ fail ]; fi;
      for dl in Tuples( [ 0, 1 ], Length( free ) ) do
        for d0 in d0ch do
          Add( res, rec( part := part, s := sl, comps := comps,
                         deltas := List( [ 1 .. Length( free ) ], i -> [ free[ i ], dl[ i ] ] ),
                         delta0 := d0 ) );
        od;
      od;
    od;
  od;
  return res;
end );

# Arf contribution (sum of the deltas) of an option
BindGlobal( "WALL2_OptionArf", function( o )
  local a;
  a := Sum( o.deltas, d -> d[ 2 ] );
  if o.delta0 <> fail then a := a + o.delta0; fi;
  return a mod 2;
end );

BindGlobal( "WALL2_MakeInvariant", function( f, polys, uni )
  local inv;
  inv := WALL_MakeInvariant( f, polys, [] );
  inv := ShallowCopy( inv );
  if uni = fail then
    inv.s := []; inv.deltas := []; inv.delta0 := fail;
  else
    inv.s := uni.s; inv.deltas := uni.deltas; inv.delta0 := uni.delta0;
  fi;
  return Immutable( inv );
end );

BindGlobal( "WALL2_ClassInvariants", function( f )
  local n, atoms, result, recurse, n1, opts, o, base, one;
  n := f.n; one := f.one;
  atoms := WALL_Atoms( f );
  result := [];
  recurse := function( start, remaining, polys, uni )
    local i, a, k, lam, inv, arf, p;
    if remaining = 0 then
      if f.type = "O" then
        arf := 0;
        if uni <> fail then arf := WALL2_OptionArf( uni ); fi;
        for p in polys do
          if p[ 1 ] <> [ one, one ] and WALL_DualCoeffs( f, p[ 1 ] ) = p[ 1 ] then
            arf := arf + Sum( p[ 2 ] );
          fi;
        od;
        if arf mod 2 <> f.arf then return; fi;
      fi;
      Add( result, WALL2_MakeInvariant( f, polys, uni ) );
      return;
    fi;
    for i in [ start .. Length( atoms ) ] do
      a := atoms[ i ];
      if a.weight > remaining then break; fi;
      for k in [ 1 .. QuoInt( remaining, a.weight ) ] do
        for lam in Partitions( k ) do
          recurse( i + 1, remaining - k * a.weight,
                   Concatenation( polys, List( a.pols, c -> [ c, lam ] ) ), uni );
        od;
      od;
    od;
  end;
  for n1 in [ 0, 2 .. n ] do
    if n1 = 0 then
      recurse( 1, n, [], fail );
    else
      for o in WALL2_UnipotentOptions( f.type, n1 ) do
        recurse( 1, n - n1, [ [ [ one, one ], o.part ] ], o );
      od;
    fi;
  od;
  return result;
end );

# Wall, Theorem 3.7.3 (generating functions)
BindGlobal( "WALL2_NrClasses", function( f )
  local nu, N, chi, cm1, c0, v, c, e, i, q, prodq, S, D, l, res;
  nu := f.n / 2; q := f.q;
  N := nu + 1;                              # series in u = t^2 up to u^nu
  # chi_i as series in the variable t (degree <= nu), recursion of Wall
  chi := function( a, b )
    local cm, c, r, x, sh, mul, add, tv;
    sh := function( s, k ) local r; r := ListWithIdenticalEntries( N, 0 );
            for x in [ 1 .. N - k ] do r[ x + k ] := s[ x ]; od; return r; end;
    add := function( s1, s2 ) return s1 + s2; end;
    cm := ListWithIdenticalEntries( N, 0 ); cm[ 1 ] := a;        # chi_{-1}
    c := ListWithIdenticalEntries( N, 0 ); c[ 1 ] := b;          # chi_0
    for v in [ 0 .. N ] do
      # chi_{2v+1} = chi_{2v} + t^{2v+1} chi_{2v-1}
      r := c + sh( cm, 2 * v + 1 );
      # chi_{2v+2} = chi_{2v+1} + t^{v+1}(1+t^{v+1})(chi_{2v+1} + (1-t^{2v+1}) chi_{2v-1})
      tv := r + cm - sh( cm, 2 * v + 1 );
      tv := sh( tv, v + 1 ) + sh( tv, 2 * v + 2 );
      cm := r; c := r + tv;
    od;
    return c;
  end;
  prodq := ListWithIdenticalEntries( N, 0 ); prodq[ 1 ] := 1;
  for l in [ 1 .. nu ] do
    prodq := WALL_SeriesMul( prodq, WALL_SeriesGeom( q, l, nu ), nu );
  od;
  if f.type = "Sp" then
    return WALL_SeriesMul( chi( 0, 1 ), prodq, nu )[ nu + 1 ];
  fi;
  S := WALL_SeriesMul( chi( 1, 1 ), prodq, nu );
  D := ListWithIdenticalEntries( N, 0 ); D[ 1 ] := 1;     # in u = t^2
  for l in [ 1 .. nu ] do
    D := WALL_SeriesMul( D, WALL_SeriesBinom( -1, 2 * l - 1, nu ), nu );
    D := WALL_SeriesMul( D, WALL_SeriesGeom( q, 2 * l, nu ), nu );
  od;
  return ( S[ nu + 1 ] + f.sign * D[ nu + 1 ] ) / 2;
end );

# Wall, Theorem 3.7.4:  |C(x)| = 2^k prod B(phi)
BindGlobal( "WALL2_UnipotentCentralizerOrder", function( f, part, slist, deltas, delta0 )
  local q, eps, ml, mm, i, m, e2, res, sprev, isolated, dprime, L, k, big, Ls,
        Sp, Ot, l;
  q := f.q;
  if f.type = "Sp" then eps := 1; else eps := -1; fi;
  ml := WALL_Mults( part );
  e2 := WALL_E2( part );            # 2 * (sum_{i<j} i m_i m_j + 1/2 sum (i-1) m_i^2)
  Ls := WALL2_ComponentSets( part, slist );
  Sp := m -> WALL_OrderSp( m, q );
  res := 1;
  for mm in ml do
    i := mm[ 1 ]; m := mm[ 2 ];
    if IsEvenInt( i ) then
      sprev := WALL2_SOf( slist, i );
      if sprev = 0 then
        e2 := e2 + eps * m; res := res * Sp( m );
      elif IsOddInt( m ) then
        e2 := e2 + eps * m; res := res * Sp( m - 1 );
      else
        e2 := e2 + ( 2 + eps ) * m - 2; res := res * Sp( m - 2 );
      fi;
    else
      # odd part i: index mu = i - 1 (even); isolated?
      if i = 1 then
        isolated := f.type = "O" and WALL2_SOf( slist, 2 ) = 0;
        dprime := delta0;
      else
        L := First( Ls, L -> i - 1 in L );
        isolated := Length( L ) = 1;
        dprime := First( deltas, d -> d[ 1 ] = L );
        if dprime <> fail then dprime := dprime[ 2 ]; fi;
      fi;
      if isolated then
        if dprime = fail then dprime := 0; fi;
        e2 := e2 + ( 1 + eps ) * m;
        if dprime = 0 then Ot := 1; else Ot := -1; fi;
        res := res * WALL_OrderO( m, q, Ot );
      else
        e2 := e2 - ( 1 - eps ) * m; res := res * Sp( m );
      fi;
    fi;
  od;
  if IsOddInt( e2 ) then Error( "WALL2: half-integral exponent" ); fi;
  res := res * q^( e2 / 2 );
  # big component sets
  k := Number( Ls, L -> ForAny( L, l -> IsOddInt( l ) and WALL2_SOf( slist, l + 1 ) = 1 )
                       and not ( f.type = "Sp" and 1 in L ) );
  return 2^k * res;
end );

BindGlobal( "WALL2_CentralizerOrder", function( f, inv )
  local res, Q, p, c, d, dual, part, ml, e2, ord;
  res := 1; Q := f.q;
  for p in inv.polys do
    c := p[ 1 ]; part := p[ 2 ]; d := Length( c ) - 1;
    ml := WALL_Mults( part ); e2 := WALL_E2( part );
    dual := WALL_DualCoeffs( f, c );
    if c = [ f.one, f.one ] then
      res := res * WALL2_UnipotentCentralizerOrder( f, part, inv.s, inv.deltas, inv.delta0 );
    elif dual = c then
      ord := Q^( d / 2 );
      res := res * ord^e2 * Product( ml, x -> WALL_OrderGU( x[ 2 ], ord ) );
    elif c < dual then
      res := res * ( Q^d )^e2 * Product( ml, x -> WALL_OrderGL( x[ 2 ], Q^d ) );
    fi;
  od;
  return res;
end );

#############################################################################
##  characteristic 2: computable invariants, pieces and models
#############################################################################








# The blocks of De Franceschi-Liebeck-O'Brien, "Conjugacy in finite classical
# groups" (2025), Sect. 5.1 (following Gonshaw-Liebeck-O'Brien):
#   "V":  V_beta(2k)   (m = 2k),  beta = 0 (p = 0) or alpha (p = 1)
#   "W":  W(m)
#   "Wt": W_beta(2l+1) (m = 2l+1), beta = 0 (p = 0) or alpha (p = 1);
#         for m = 1 (orthogonal only) the hyperbolic resp. anisotropic plane
# alpha is a fixed element of trace 1 (x^2+x+alpha irreducible).
# Returns rec( x, F, Qm, dim ), or fail if the block does not exist.
BindGlobal( "WALL2_Piece", function( f, kind, m, p )
  local K, key, one, al, beta, n, idx, pos, x, F, Qm, i, j, k, l, A, r, res, type;
  K := f.field; type := f.type; one := One( K );
  if not IsBound( f.pieces ) then f.pieces := rec(); fi;
  key := Concatenation( kind, "_", String( m ), "_", String( p ) );
  if IsBound( f.pieces.( key ) ) then return f.pieces.( key ); fi;
  al := WALL2_StdAniso( K, f.q );
  if p = 1 then beta := al; else beta := Zero( K ); fi;
  if kind = "V" then
    k := m / 2;
    if p = 1 and type = "Sp" and k = 1 then f.pieces.( key ) := fail; return fail; fi;
    idx := [ -( 2 * k - 1 ), -( 2 * k - 3 ) .. 2 * k - 1 ];
    pos := i -> Position( idx, i );
    n := 2 * k;
    x := NullMat( n, n, K ); F := NullMat( n, n, K ); Qm := NullMat( n, n, K );
    for i in idx do F[ pos( i ) ][ pos( -i ) ] := one; od;
    if k = 1 then
      x[ 1 ][ 1 ] := one; x[ 1 ][ 2 ] := one; x[ 2 ][ 2 ] := one;
    else
      for i in idx do
        if i <= -3 then
          for j in [ i, i + 2 .. 1 ] do x[ pos( i ) ][ pos( j ) ] := one; od;
          x[ pos( i ) ][ pos( 3 ) ] := x[ pos( i ) ][ pos( 3 ) ] + beta;
        elif i < 2 * k - 1 then
          x[ pos( i ) ][ pos( i ) ] := one; x[ pos( i ) ][ pos( i + 2 ) ] := one;
        else
          x[ pos( i ) ][ pos( i ) ] := one;
        fi;
      od;
    fi;
    for i in [ 1 .. n ] do for j in [ i + 1 .. n ] do Qm[ i ][ j ] := F[ i ][ j ]; od; od;
    Qm[ pos( -1 ) ][ pos( -1 ) ] := beta; Qm[ pos( 1 ) ][ pos( 1 ) ] := one;
  else
    if kind = "W" then beta := Zero( K ); fi;
    if kind = "Wt" and p = 1 and type = "Sp" and m = 1 then f.pieces.( key ) := fail; return fail; fi;
    # basis w_{-(m-1)}, x_{-(m-1)}, ..., w_{m-1}, x_{m-1}
    idx := [ -( m - 1 ), -( m - 3 ) .. m - 1 ];
    n := 2 * m;
    pos := function( c, i ) return 2 * Position( idx, i ) - 1 + c; end;   # c = 0: w, 1: x
    x := NullMat( n, n, K ); F := NullMat( n, n, K ); Qm := NullMat( n, n, K );
    for i in idx do F[ pos( 0, i ) ][ pos( 1, -i ) ] := one; F[ pos( 1, -i ) ][ pos( 0, i ) ] := one; od;
    for i in idx do
      # w_i
      x[ pos( 0, i ) ][ pos( 0, i ) ] := one;
      if i < m - 1 then x[ pos( 0, i ) ][ pos( 0, i + 2 ) ] := one; fi;
      if beta <> Zero( K ) and ( i = -4 or i = -2 ) then
        x[ pos( 0, i ) ][ pos( 1, 2 ) ] := x[ pos( 0, i ) ][ pos( 1, 2 ) ] + beta;
      fi;
      # x_i
      for j in [ i, i + 2 .. m - 1 ] do x[ pos( 1, i ) ][ pos( 1, j ) ] := one; od;
      if beta <> Zero( K ) and i <= -2 then
        x[ pos( 1, i ) ][ pos( 0, 2 ) ] := x[ pos( 1, i ) ][ pos( 0, 2 ) ] + beta;
      fi;
    od;
    for i in [ 1 .. n ] do for j in [ i + 1 .. n ] do Qm[ i ][ j ] := F[ i ][ j ]; od; od;
    if beta <> Zero( K ) then
      if m = 1 then
        Qm[ pos( 0, 0 ) ][ pos( 0, 0 ) ] := beta; Qm[ pos( 1, 0 ) ][ pos( 1, 0 ) ] := one;
      else
        Qm[ pos( 0, -2 ) ][ pos( 0, -2 ) ] := beta;
        Qm[ pos( 0, 0 ) ][ pos( 0, 0 ) ] := beta; Qm[ pos( 1, 0 ) ][ pos( 1, 0 ) ] := beta;
      fi;
    fi;
  fi;
  if x * F * TransposedMat( x ) <> F or
     ( type = "O" and ForAny( [ 1 .. n ], i -> x[ i ] * Qm * x[ i ] <> Qm[ i ][ i ] ) ) then
    Error( "WALL2_Piece: block is not an isometry" );
  fi;
  if type = "Sp" then Qm := fail; fi;
  res := rec( x := x, F := F, Qm := Qm, dim := n );
  f.pieces.( key ) := res;
  return res;
end );

# list of pieces [kind, m, p] for a part m with multiplicity k, bit s, param p
BindGlobal( "WALL2_PartPieces", function( type, m, k, s, p )
  local res;
  res := [];
  if IsOddInt( m ) then
    if type = "Sp" and m = 1 then p := 0; fi;
    Add( res, [ "Wt", m, p ] );
    Append( res, List( [ 1 .. k / 2 - 1 ], i -> [ "W", m, 0 ] ) );
  elif s = 0 then
    Append( res, List( [ 1 .. k / 2 ], i -> [ "W", m, 0 ] ) );
  elif IsOddInt( k ) then
    Add( res, [ "V", m, p ] );
    Append( res, List( [ 1 .. ( k - 1 ) / 2 ], i -> [ "W", m, 0 ] ) );
  else
    Add( res, [ "V", m, p ] ); Add( res, [ "V", m, 0 ] );
    Append( res, List( [ 1 .. k / 2 - 1 ], i -> [ "W", m, 0 ] ) );
  fi;
  return res;
end );

# which part carries the parameter of a free component set / delta0
BindGlobal( "WALL2_HasParam", function( type, m, slist )
  if IsOddInt( m ) then return not ( type = "Sp" and m = 1 ); fi;
  return WALL2_SOf( slist, m ) = 1 and not ( type = "Sp" and m = 2 );
end );
BindGlobal( "WALL2_DesignatedPart", function( type, L, part, slist )
  local ms;
  ms := Filtered( List( L, e -> e + 1 ), m -> WALL2_HasParam( type, m, slist ) );
  if ms = [] then return fail; fi;
  return Maximum( ms );
end );

# parameters p_m for all parts, from Wall's labels (deltas, delta0)
BindGlobal( "WALL2_ParamsFromLabels", function( type, part, slist, deltas, delta0 )
  local ps, d, m;
  ps := List( Set( part ), m -> [ m, 0 ] );
  for d in deltas do
    m := WALL2_DesignatedPart( type, d[ 1 ], part, slist );
    if m = fail then Error( "WALL2: free component set without parameter" ); fi;
    First( ps, a -> a[ 1 ] = m )[ 2 ] := d[ 2 ];
  od;
  if delta0 <> fail and delta0 = 1 then First( ps, a -> a[ 1 ] = 1 )[ 2 ] := 1; fi;
  return ps;
end );

# all pieces of the unipotent model
BindGlobal( "WALL2_UnipotentPieces", function( f, part, slist, ps )
  local res, mm;
  res := [];
  for mm in WALL_Mults( part ) do
    Append( res, WALL2_PartPieces( f.type, mm[ 1 ], mm[ 2 ], WALL2_SOf( slist, mm[ 1 ] ),
                                   First( ps, a -> a[ 1 ] = mm[ 1 ] )[ 2 ] ) );
  od;
  return List( res, a -> WALL2_Piece( f, a[ 1 ], a[ 2 ], a[ 3 ] ) );
end );

BindGlobal( "WALL2_SumPieces", function( f, pcs )
  local K, x, F, Qm;
  K := f.field;
  if ForAny( pcs, p -> p = fail ) then return fail; fi;
  x := WALL_BlockDiag( K, List( pcs, p -> p.x ) );
  F := WALL_BlockDiag( K, List( pcs, p -> p.F ) );
  if f.type = "O" then Qm := WALL_BlockDiag( K, List( pcs, p -> p.Qm ) ); else Qm := fail; fi;
  return rec( x := x, F := F, Qm := Qm );
end );

# s-bits of a unipotent x (polar form F): s_m = 0 iff h_m is alternating
BindGlobal( "WALL2_SBits", function( K, x, F, part )
  local n, N, res, m, Km, Km1, Kp, S, comp;
  n := Length( x ); N := x + IdentityMat( n, K ); res := [];
  for m in Set( Filtered( part, IsEvenInt ) ) do
    comp := WALL_Tops( N, m );
    if ForAny( comp, u -> not IsZero( u * F * ( u * N^( m - 1 ) ) ) ) then
      Add( res, [ m, 1 ] );
    else
      Add( res, [ m, 0 ] );
    fi;
  od;
  return res;
end );



BindGlobal( "WALL2_Invariant", function( f, x )
  local K, chi, facs, polys, pr, c, part, uni, B1, x1, F1, Q1, N;
  if not WallIsInGroup( f, x ) then
    Error( "WallInvariant: x does not preserve the form" );
  fi;
  K := f.field;
  chi := CharacteristicPolynomial( K, K, x );
  facs := Collected( Factors( PolynomialRing( K ), chi ) );
  polys := []; uni := fail;
  for pr in facs do
    c := CoefficientsOfUnivariatePolynomial( pr[ 1 ] );
    c := c / c[ Length( c ) ];
    part := WALL_Partition( f, x, pr[ 1 ], pr[ 2 ] );
    Add( polys, [ c, part ] );
    if c = [ f.one, f.one ] then
      N := x + IdentityMat( f.n, K );
      B1 := NullspaceMat( N^pr[ 2 ] );
      x1 := List( B1, b -> SolutionMat( B1, b * x ) );
      F1 := B1 * f.gram * TransposedMat( B1 );
      if f.type = "O" then Q1 := B1 * f.quad * TransposedMat( B1 ); else Q1 := fail; fi;
      uni := WALL2_UnipotentLabelsDLO( f, x1, F1, Q1 );
    fi;
  od;
  return WALL2_MakeInvariant( f, polys, uni );
end );

#############################################################################
##  canonical bases for quadratic forms in characteristic 2
#############################################################################

BindGlobal( "WALL2_StdAniso", function( K, q )
  local w, z;
  w := PrimitiveRoot( K ); z := One( K );
  while IsZero( WALL2_Tr2( z, q ) ) do z := z * w; od;
  return z;
end );

# P with: rows e_1..e_k, f_1..f_k, B(e_i,f_j) = delta_ij, Q(e_i) = Q(f_i) = 0
# except possibly Q(e_k) = 1, Q(f_k) = std (anisotropic last plane)
BindGlobal( "WALL2_CanonicalQuad", function( K, q, F, Qm )
  local n, Q, B, W, es, fs, rs, v, w, e, ff, c, i, j, a, b, r, aniso, std, sq, x;
  n := Length( F );
  Q := v -> v * Qm * v; B := function( u, v ) return u * F * v; end;
  W := List( IdentityMat( n, K ), ShallowCopy );
  es := []; fs := []; aniso := false;
  rs := RandomSource( IsMersenneTwister, 4711 );
  while Length( W ) > 0 do
    # find a singular nonzero vector in the span of W
    e := fail;
    for v in W do if IsZero( Q( v ) ) then e := v; break; fi; od;
    if e = fail and Length( W ) = 2 then
      a := Q( W[ 1 ] ); b := B( W[ 1 ], W[ 2 ] ); c := Q( W[ 2 ] );
      r := RootsOfUPol( K, UnivariatePolynomial( K, [ c, b, a ] ) );
      if r <> [] then e := r[ 1 ] * W[ 1 ] + W[ 2 ]; fi;
    fi;
    while e = fail and Length( W ) > 2 do
      v := List( W, u -> Random( rs, AsList( K ) ) ) * W;
      if not IsZero( v ) and IsZero( Q( v ) ) then e := v; fi;
    od;
    if e = fail then
      # anisotropic plane
      aniso := true;
      e := W[ 1 ] / ( Q( W[ 1 ] )^( q / 2 ) );          # Q(e) = 1
      ff := W[ 2 ] / B( e, W[ 2 ] );                       # B(e,ff) = 1
      std := WALL2_StdAniso( K, q );
      r := RootsOfUPol( K, UnivariatePolynomial( K, [ Q( ff ) + std, One( K ), One( K ) ] ) );
      ff := ff + r[ 1 ] * e;
      Add( es, e ); Add( fs, ff ); W := [];
    else
      w := First( W, u -> not IsZero( B( e, u ) ) );
      ff := w / B( e, w );
      ff := ff + Q( ff ) * e;
      Add( es, e ); Add( fs, ff );
      W := List( W, u -> u + B( u, ff ) * e + B( u, e ) * ff );
      W := Filtered( W, u -> not IsZero( u ) );
      if Length( W ) > 0 then W := List( BaseMat( W ), ShallowCopy ); fi;
    fi;
  od;
  # put the anisotropic plane last
  return rec( P := Concatenation( es, fs ), aniso := aniso );
end );

# S with  Q(v S^-1) = Q0(v)  i.e.  y = S x0 S^-1 preserves (F, Qm) if x0
# preserves (F0, Q0)
BindGlobal( "WALL2_FormIsometry", function( f, F0, Q0, F, Qm )
  local c0, c1;
  if f.type = "Sp" then return WallFormIsometry( f, F0, F ); fi;
  c0 := WALL2_CanonicalQuad( f.field, f.q, F0, Q0 );
  c1 := WALL2_CanonicalQuad( f.field, f.q, F, Qm );
  if c0.aniso <> c1.aniso then Error( "WALL2_FormIsometry: Arf invariants differ" ); fi;
  return c1.P^-1 * c0.P;
end );

# quadratic form on a component where 1+x is invertible: Q(v(1+x)) = B(v, vx)
BindGlobal( "WALL2_InducedQuad", function( K, x, F )
  local n, T, Ti, M, i, j;
  n := Length( x ); T := x + IdentityMat( n, K ); Ti := T^-1;
  M := List( Ti * F * TransposedMat( x ) * TransposedMat( Ti ), ShallowCopy );
  for i in [ 1 .. n ] do for j in [ 1 .. i - 1 ] do
    M[ j ][ i ] := M[ j ][ i ] + M[ i ][ j ]; M[ i ][ j ] := Zero( K );
  od; od;
  return M;
end );

BindGlobal( "WALL2_Model", function( f, inv )
  local K, comps, p, c, dual, comp, blocks, ps, pcs, md, x, F, Qm;
  K := f.field;
  blocks := [];
  for p in inv.polys do
    c := p[ 1 ]; dual := WALL_DualCoeffs( f, c );
    if c = [ f.one, f.one ] then
      ps := WALL2_ParamsFromLabels( f.type, p[ 2 ], inv.s, inv.deltas, inv.delta0 );
      md := WALL2_SumPieces( f, WALL2_UnipotentPieces( f, p[ 2 ], inv.s, ps ) );
      if md = fail then Error( "WALL2_Model: piece does not exist" ); fi;
      Add( blocks, md );
    elif dual = c or c < dual then
      if dual = c then comp := WALL_SelfDualComponent( f, c, p[ 2 ], [] );
      else comp := WALL_PairComponent( f, c, p[ 2 ] ); fi;
      if f.type = "O" then Qm := WALL2_InducedQuad( K, comp.x, comp.F ); else Qm := fail; fi;
      Add( blocks, rec( x := comp.x, F := comp.F, Qm := Qm ) );
    fi;
  od;
  x := WALL_BlockDiag( K, List( blocks, b -> b.x ) );
  F := WALL_BlockDiag( K, List( blocks, b -> b.F ) );
  if f.type = "O" then Qm := WALL_BlockDiag( K, List( blocks, b -> b.Qm ) ); else Qm := fail; fi;
  return rec( x := x, F := F, Qm := Qm );
end );

BindGlobal( "WALL2_Representative", function( f, inv )
  local md, S, Qt;
  md := WALL2_Model( f, inv );
  if f.type = "O" then Qt := f.quad; else Qt := fail; fi;
  S := WALL2_FormIsometry( f, md.F, md.Qm, f.gram, Qt );
  return S * md.x * S^-1;
end );

#############################################################################
##  characteristic 2: conjugating elements
#############################################################################

BindGlobal( "WALL2_Sqrt", function( K, z )
  return SquareRoots( K, z )[ 1 ];
end );

BindGlobal( "WALL2_Bits", function( K, z ) return Coefficients( Basis( K ), z ); end );

# isometry of a piece U (generators u_k in V-coordinates, x, F, Qm on V)
# onto the model piece pc (generators: tops of pc); returns the matrix whose
# rows are the preimages of the standard basis of the piece
BindGlobal( "WALL2_PieceIsometry", function( f, x, F, Qm, us, m, pc, rs )
  local K, q, r, n, N, NP, es, TB, TQ, quadTop, hu, he, qu, qe, cu, ce, C0, B2,
        abits, vars, nv, vals, gens, evalE, k, l, t, i, d, a, D, eqsDiag, eqsOff,
        cons, rhs, addEqs, solveSet, fixUpTo, ok, tries, MP, MU, Qu, Qe, upper,
        bitIndex, setFromBits, curBits, fixedBits, alleqs, val, target, e, row;
  K := f.field; q := f.q; r := Length( us ); n := Length( x );
  N := x + IdentityMat( n, K );
  NP := pc.x + IdentityMat( Length( pc.x ), K );
  es := WALL_Tops( NP, m );
  if Length( es ) <> r then Error( "WALL2_PieceIsometry: generator count" ); fi;
  TB := List( [ 1 .. r ], k -> List( [ 1 .. r ], l -> List( [ 0 .. m - 1 ],
          t -> us[ k ] * F * ( us[ l ] * N^t ) ) ) );
  if f.type = "O" then
    TQ := List( [ 1 .. r ], k -> List( [ 0 .. m - 1 ], i -> ( us[ k ] * N^i ) * Qm * ( us[ k ] * N^i ) ) );
  fi;
  # ---- top coefficients C0
  quadTop := IsOddInt( m ) and ( f.type = "O" or m >= 3 );
  hu := List( [ 1 .. r ], k -> List( [ 1 .. r ], l -> TB[ k ][ l ][ m ] ) );
  he := List( [ 1 .. r ], k -> List( [ 1 .. r ], l -> es[ k ] * pc.F * ( es[ l ] * NP^( m - 1 ) ) ) );
  if r = 1 then
    C0 := [ [ WALL2_Sqrt( K, hu[ 1 ][ 1 ] / he[ 1 ][ 1 ] ) ] ];
  else
    if quadTop then
      if f.type = "O" then
        qu := List( [ 1 .. r ], k -> TQ[ k ][ ( m + 1 ) / 2 ] );
        qe := List( es, e -> ( e * NP^( ( m - 1 ) / 2 ) ) * pc.Qm * ( e * NP^( ( m - 1 ) / 2 ) ) );
      else
        qu := List( [ 1 .. r ], k -> TB[ k ][ k ][ m - 1 ] );
        qe := List( es, e -> e * pc.F * ( e * NP^( m - 2 ) ) );
      fi;
      upper := function( h, qv ) return [ [ qv[ 1 ], h[ 1 ][ 2 ] ], [ Zero( K ), qv[ 2 ] ] ]; end;
      cu := WALL2_CanonicalQuad( K, q, hu, upper( hu, qu ) );
      ce := WALL2_CanonicalQuad( K, q, he, upper( he, qe ) );
      if cu.aniso <> ce.aniso then Error( "WALL2_PieceIsometry: top forms differ" ); fi;
    else
      cu := WALL_CanonicalBaseChange( rec( type := "Sp", field := K, sigma := 1 ), hu );
      ce := WALL_CanonicalBaseChange( rec( type := "Sp", field := K, sigma := 1 ), he );
    fi;
    C0 := cu.P^-1 * ce.P;
  fi;
  # ---- unknowns c[k][a][d], d = 1..m-1, as F_2-bits
  B2 := Basis( K ); abits := Length( B2 );
  vars := [];
  for d in [ 1 .. m - 1 ] do for k in [ 1 .. r ] do for a in [ 1 .. r ] do
    Add( vars, [ k, a, d ] );
  od; od; od;
  nv := Length( vars );
  setFromBits := function( bits )
    local c, v, z;
    c := List( [ 1 .. r ], k -> List( [ 1 .. r ], a -> List( [ 0 .. m - 1 ], d -> Zero( K ) ) ) );
    for k in [ 1 .. r ] do for a in [ 1 .. r ] do c[ k ][ a ][ 1 ] := C0[ k ][ a ]; od; od;
    for v in [ 1 .. nv ] do
      z := bits{ [ ( v - 1 ) * abits + 1 .. v * abits ] } * B2;
      c[ vars[ v ][ 1 ] ][ vars[ v ][ 2 ] ][ vars[ v ][ 3 ] + 1 ] := z;
    od;
    return c;
  end;
  gens := function( c )
    return List( [ 1 .. r ], k -> Sum( [ 1 .. r ], a -> Sum( [ 0 .. m - 1 ],
                   d -> c[ k ][ a ][ d + 1 ] * ( es[ a ] * NP^d ) ) ) );
  end;
  # equation (kind, k, l, t) -> value  (kind "B": B(g_k, g_l N^t), "Q": Q(g_k N^t))
  evalE := function( g, eq )
    local v;
    if eq[ 1 ] = "B" then return g[ eq[ 2 ] ] * pc.F * ( g[ eq[ 3 ] ] * NP^eq[ 4 ] ); fi;
    v := g[ eq[ 2 ] ] * NP^eq[ 4 ];
    return v * pc.Qm * v;
  end;
  target := function( eq )
    if eq[ 1 ] = "B" then return TB[ eq[ 2 ] ][ eq[ 3 ] ][ eq[ 4 ] + 1 ]; fi;
    return TQ[ eq[ 2 ] ][ eq[ 4 ] + 1 ];
  end;
  alleqs := [];
  for k in [ 1 .. r ] do for l in [ 1 .. r ] do for t in [ 0 .. m - 1 ] do
    Add( alleqs, [ "B", k, l, t ] );
  od; od; od;
  if f.type = "O" then
    for k in [ 1 .. r ] do for i in [ 0 .. m - 1 ] do Add( alleqs, [ "Q", k, k, i ] ); od; od;
  fi;
  for tries in [ 1 .. 30 ] do
    curBits := List( [ 1 .. nv * abits ], i -> Zero( GF(2) ) );
    cons := []; rhs := [];
    # add linearized equations eqs (affine in the non-fixed bits)
    addEqs := function( eqs, fixed )
      local g0, v0, j, b, g1, col, cols, e, i2, row;
      if eqs = [] then return; fi;
      g0 := gens( setFromBits( curBits ) );
      v0 := Concatenation( List( eqs, e -> WALL2_Bits( K, evalE( g0, e ) - target( e ) ) ) );
      cols := [];
      for j in [ 1 .. nv * abits ] do
        if fixed[ j ] then Add( cols, 0 * v0 ); continue; fi;
        b := ShallowCopy( curBits ); b[ j ] := b[ j ] + Z(2)^0;
        g1 := gens( setFromBits( b ) );
        Add( cols, Concatenation( List( eqs, e -> WALL2_Bits( K, evalE( g1, e ) - target( e ) ) ) ) - v0 );
      od;
      # J (y - y0) = - v0   ->  rows: J,  rhs: J y0 + v0
      for i2 in [ 1 .. Length( v0 ) ] do
        row := List( cols, c -> c[ i2 ] );
        Add( cons, row ); Add( rhs, row * curBits + v0[ i2 ] );
      od;
    end;
    solveSet := function()
      local A, sol, ker;
      if cons = [] then return true; fi;
      A := TransposedMat( cons );
      sol := SolutionMat( A, rhs );
      if sol = fail then return false; fi;
      ker := NullspaceMat( A );
      if Length( ker ) > 0 then
        sol := sol + List( ker, v -> Random( rs, [ 0, 1 ] ) * Z(2)^0 ) * ker;
      fi;
      curBits := sol;
      return true;
    end;
    fixedBits := List( [ 1 .. nv * abits ], i -> false );
    fixUpTo := function( dmax )
      local v, j;
      for v in [ 1 .. nv ] do
        if vars[ v ][ 3 ] <= dmax then
          for j in [ ( v - 1 ) * abits + 1 .. v * abits ] do
            if not fixedBits[ j ] then
              fixedBits[ j ] := true;
              row := ListWithIdenticalEntries( nv * abits, Zero( GF(2) ) ); row[ j ] := Z(2)^0;
              Add( cons, row ); Add( rhs, curBits[ j ] );
            fi;
          od;
        fi;
      od;
    end;
    ok := true;
    for D in [ 1 .. m - 1 ] do
      t := m - 1 - D;
      eqsDiag := Filtered( alleqs, e -> ( e[ 1 ] = "B" and e[ 2 ] = e[ 3 ] and e[ 4 ] = t ) or
                   ( e[ 1 ] = "Q" and Maximum( 1, m - 1 - 2 * e[ 4 ] ) = D ) );
      addEqs( eqsDiag, fixedBits );
      if not solveSet() then ok := false; break; fi;
      fixUpTo( QuoInt( D, 2 ) );
      eqsOff := Filtered( alleqs, e -> e[ 1 ] = "B" and e[ 2 ] <> e[ 3 ] and e[ 4 ] = t );
      addEqs( eqsOff, fixedBits );
      if not solveSet() then ok := false; break; fi;
    od;
    if not ok then continue; fi;
    # verify all equations exactly
    e := gens( setFromBits( curBits ) );
    if ForAll( alleqs, eq -> evalE( e, eq ) = target( eq ) ) then
      MP := Concatenation( List( e, g -> List( [ 0 .. m - 1 ], i -> g * NP^i ) ) );
      MU := Concatenation( List( us, u -> List( [ 0 .. m - 1 ], i -> u * N^i ) ) );
      return MP^-1 * MU;
    fi;
  od;
  Error( "WALL2_PieceIsometry: no solution found" );
end );


# conjugating rows for the unipotent part: x, F, Qm on V_1 (coordinates);
# returns rows (V_1 coordinates) of an adapted basis, in model order
BindGlobal( "WALL2_UnipotentAdapted", function( f, x, F, Qm, inv, rs )
  local K, n, N, part, ps, mults, plists, M, done, mm, m, plist, j, kind, p, piece,
        Nsub, Fsub, tops, hm, phi, w0, sq, low, gtop, g, g1, g2, U, Uv, prm, tries,
        cmp, isLastV, ker, ord, rows, pc, res, kk, a, b, c;
  K := f.field; n := Length( x ); N := x + IdentityMat( n, K );
  part := First( inv.polys, p -> p[ 1 ] = [ f.one, f.one ] )[ 2 ];
  ps := WALL2_ParamsFromLabels( f.type, part, inv.s, inv.deltas, inv.delta0 );
  mults := WALL_Mults( part );
  M := IdentityMat( n, K );
  done := rec();
  for mm in Reversed( mults ) do
    m := mm[ 1 ];
    plist := WALL2_PartPieces( f.type, m, mm[ 2 ], WALL2_SOf( inv.s, m ),
                               First( ps, a -> a[ 1 ] = m )[ 2 ] );
    done.( String( m ) ) := [];
    for j in [ 1 .. Length( plist ) ] do
      kind := plist[ j ][ 1 ]; p := plist[ j ][ 3 ];
      isLastV := kind = "V" and ForAll( plist{ [ j + 1 .. Length( plist ) ] }, a -> a[ 1 ] = "W" );
      Nsub := List( M, v -> SolutionMat( M, v * N ) );
      Fsub := M * F * TransposedMat( M );
      tops := WALL_Tops( Nsub, m );
      hm := List( tops, a -> List( tops, b -> a * Fsub * ( b * Nsub^( m - 1 ) ) ) );
      low := Concatenation( NullspaceMat( Nsub^( m - 1 ) ), Nsub );
      low := Filtered( low, v -> not IsZero( v ) );
      if low <> [] then low := BaseMat( low ); fi;
      for tries in [ 1 .. 200 ] do
        # top coefficients (in terms of tops)
        if kind = "V" then
          if isLastV then
            # w0 with h(v,w0) = sqrt(h(v,v)) for all v
            sq := List( [ 1 .. Length( tops ) ], i -> WALL2_Sqrt( K, hm[ i ][ i ] ) );
            c := SolutionMat( TransposedMat( hm ), sq );
          else
            repeat c := List( tops, t -> Random( rs, AsList( K ) ) ); until not IsZero( c * hm * c );
          fi;
          gtop := [ c ];
        else
          # phi(v) = h(v,v) is semilinear: kernel = vectors v with h(v,w0)=0
          sq := List( [ 1 .. Length( tops ) ], i -> WALL2_Sqrt( K, hm[ i ][ i ] ) );
          if IsZero( sq ) then ker := IdentityMat( Length( tops ), K );
          else ker := NullspaceMat( TransposedMat( [ SolutionMat( TransposedMat( hm ), sq ) * hm ] ) ); fi;
          repeat a := List( ker, v -> Random( rs, AsList( K ) ) ) * ker; until not IsZero( a );
          repeat b := List( ker, v -> Random( rs, AsList( K ) ) ) * ker; until not IsZero( a * hm * b );
          b := b / ( a * hm * b );
          gtop := [ a, b ];
        fi;
        g := List( gtop, c -> c * tops );
        if low <> [] then
          g := List( g, v -> v + List( low, w -> Random( rs, AsList( K ) ) ) * low );
        fi;
        U := Concatenation( List( g, v -> List( [ 0 .. m - 1 ], i -> v * Nsub^i ) ) );
        Uv := U * M;
        # accept if U is the block of the model (beta by DLO, Lemmas 5.3.3/5.3.4)
        if not IsZero( DeterminantMat( Uv * F * TransposedMat( Uv ) ) ) and
           ( ( kind = "W" and IsEvenInt( m ) ) or
             ( kind = "V" and WALL2_BlockBeta( f, x, F, Qm, Uv, m, "V" ) = p ) or
             ( kind <> "V" and WALL2_BlockBeta( f, x, F, Qm, Uv, m, "W" ) = p ) ) then break; fi;
        if tries = 200 then Error( "WALL2_UnipotentAdapted: splitting failed" ); fi;
      od;
      Add( done.( String( m ) ), [ kind, p, List( g, v -> v * M ) ] );
      # complement of U in M
      cmp := NullspaceMat( Fsub * TransposedMat( U ) );
      if Length( cmp ) = 0 then M := []; else M := cmp * M; fi;
    od;
  od;
  # isometries onto the model pieces, in model order
  rows := [];
  for mm in mults do
    m := mm[ 1 ];
    for a in done.( String( m ) ) do
      pc := WALL2_Piece( f, a[ 1 ], m, a[ 2 ] );
      Append( rows, WALL2_PieceIsometry( f, x, F, Qm, a[ 3 ], m, pc, rs ) );
    od;
  od;
  return rows;
end );

BindGlobal( "WALL2_ConjugatingElement", function( f, x )
  local K, inv, rs, rows, p, c, dual, comp, str, LD, H, Z, PW, cd, Q, G, C, B1, x1, F1, Q1,
        md, P, S, Qt, N, m1;
  K := f.field;
  inv := WallInvariant( f, x );
  rs := RandomSource( IsMersenneTwister, 271828 );
  rows := [];
  for p in inv.polys do
    c := p[ 1 ]; dual := WALL_DualCoeffs( f, c );
    if c = [ f.one, f.one ] then
      N := x + IdentityMat( f.n, K );
      B1 := NullspaceMat( N^f.n );
      x1 := List( B1, b -> SolutionMat( B1, b * x ) );
      F1 := B1 * f.gram * TransposedMat( B1 );
      if f.type = "O" then Q1 := B1 * f.quad * TransposedMat( B1 ); else Q1 := fail; fi;
      Append( rows, WALL2_UnipotentAdapted( f, x1, F1, Q1, inv, rs ) * B1 );
    elif dual = c or c < dual then
      if dual = c then comp := WALL_SelfDualComponent( f, c, p[ 2 ], [] );
      else comp := WALL_PairComponent( f, c, p[ 2 ] ); fi;
      Append( rows, WALL_ComponentRows( f, x, comp ) );
    fi;
  od;
  P := rows;
  md := WALL2_Model( f, inv );
  if P * x <> md.x * P or P * f.gram * TransposedMat( P ) <> md.F or
     ( f.type = "O" and ForAny( [ 1 .. f.n ], i -> P[ i ] * f.quad * P[ i ] <> md.Qm[ i ][ i ] ) ) then
    Error( "WALL2_ConjugatingElement: adapted basis failed" );
  fi;
  if f.type = "O" then Qt := f.quad; else Qt := fail; fi;
  S := WALL2_FormIsometry( f, md.F, md.Qm, f.gram, Qt );
  return rec( invariant := inv, representative := S * md.x * S^-1, conjugator := S * P );
end );

#############################################################################
##  characteristic 2: centralizers
##
##  For uniformly random h in G and y the (deterministic) conjugating element
##  of h x h^-1 to the representative x, the element y h is uniformly random
##  in C_G(x) (y depends only on the coset h C_G(x)).  Random elements are
##  added until the generated group has the order given by Wall's formula.
#############################################################################

# the group G(F) as a GAP matrix group (cached)
BindGlobal( "WALL2_Group", function( f )
  local G0, F0, Q0, S;
  if IsBound( f.group ) then return f.group; fi;
  if f.type = "Sp" then
    G0 := Sp( f.n, f.q ); F0 := InvariantBilinearForm( G0 ).matrix;
    S := WallFormIsometry( f, F0, f.gram );
  else
    G0 := GO( f.sign, f.n, f.q ); Q0 := InvariantQuadraticForm( G0 ).matrix;
    F0 := Q0 + TransposedMat( Q0 );
    S := WALL2_FormIsometry( f, F0, Q0, f.gram, f.quad );
  fi;
  f.group := Group( List( GeneratorsOfGroup( G0 ), g -> S * g * S^-1 ) );
  SetSize( f.group, WallGroupOrder( f ) );
  WALL_SetFormAttributes( f, f.group );
  return f.group;
end );

# random generation of the centralizer of the representative, with at most
# cap random elements; status "ok" (generated group has the order of Wall's
# formula), "cap" (cap reached below that order), "exceeded" (generated
# group larger than the formula value)
BindGlobal( "WALL2_CentralizerCapped", function( f, inv, cap )
  local x, ord, G, gens, H, h, a, c, nextcheck, one, tries;
  x := WallRepresentative( f, inv );
  ord := WallCentralizerOrder( f, inv );
  G := WALL2_Group( f );
  one := IdentityMat( f.n, f.field );
  gens := []; H := Group( [ one ] ); nextcheck := 2; tries := 0;
  while Size( H ) < ord do
    if tries >= cap then
      return rec( representative := x, generators := gens, centralizerOrder := ord,
                  status := "cap", order := Size( Group( gens, one ) ) );
    fi;
    tries := tries + 1;
    h := PseudoRandom( G );
    a := WallConjugatingElement( f, h * x * h^-1 );
    if a.representative <> x then Error( "WALL2: representative mismatch" ); fi;
    c := a.conjugator * h;
    if c * x <> x * c then Error( "WALL2: not in the centralizer" ); fi;
    if not c in H then
      Add( gens, c );
      if Length( gens ) >= nextcheck or tries >= cap then
        H := Group( gens, one );
        if Size( H ) > ord then
          return rec( representative := x, generators := gens, centralizerOrder := ord,
                      status := "exceeded", order := Size( H ) );
        fi;
        nextcheck := Length( gens ) + 1;
      fi;
    fi;
  od;
  return rec( representative := x, generators := gens, centralizerOrder := ord,
              status := "ok", order := ord );
end );

BindGlobal( "WALL2_RepresentativeWithCentralizer", function( f, inv )
  local r;
  r := WALL2_CentralizerCapped( f, inv, infinity );
  if r.status <> "ok" then Error( "WALL2: centralizer larger than Wall's formula" ); fi;
  return rec( representative := r.representative, generators := r.generators,
              centralizerOrder := r.centralizerOrder );
end );

#############################################################################
##  WallCertifyChar2( f [, opts ] )
##
##  Certifies, for a given group Sp(2m,q) or GO+-(2m,q), q even, that
##   (1) the invariants are complete: every listed invariant gives a
##       representative in G with exactly this invariant (so they are
##       pairwise non-conjugate), and their number equals k(G) from
##       Wall's Theorem 3.7.3;
##   (2) (unless opts.centralizers = false) the centralizer orders and
##       generators: for every class a subgroup H <= C_G(x) of order c_I
##       (Wall's Theorem 3.7.4 as implemented) is found with at most
##       opts.cap random elements, and sum |G|/c_I = |G|.  Then
##       |C_G(x)| = c_I and H = C_G(x) for all classes.
##  Only Theorem 3.7.3 is assumed (for (1)).
#############################################################################
##
##  <#GAPDoc Label="WallCertifyChar2">
##  <ManSection>
##  <Func Name="WallCertifyChar2" Arg="f[, opts]"/>
##  <Returns>a record</Returns>
##  <Description>
##  For even <M>q</M>, certifies the results for the given group, assuming
##  only Wall's Theorem&nbsp;3.7.3 (the number of classes): every listed
##  invariant has a representative in <M>G(F)</M> with exactly this invariant,
##  and the number of invariants equals Wall's class number (component
##  <C>complete</C>); and, unless <C>opts.centralizers</C> is <K>false</K>, for
##  every class a subgroup of the centralizer of the order given by Wall's
##  formula is found with at most <C>opts.cap</C> (default <M>50</M>) random
##  elements, and the class sizes add up to the group order (component
##  <C>centralizersCertified</C>). Further components: <C>nrInvariants</C>,
##  <C>nrClassesWall</C>, <C>badRepresentatives</C>, <C>sumOfClassLengths</C>,
##  <C>centralizerFailures</C>, <C>time</C>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallCertifyChar2", function( f, arg... )
  local opts, cap, doCent, t, invs, nr, bad, inv, x, res, sum, r, failed, ordG;
  if IsBound( f.oddChar2 ) then return CallFuncList( WallCertifyChar2, Concatenation( [ f.sp ], arg ) ); fi;
  if not IsBound( f.char2 ) then Error( "WallCertifyChar2: only for q even (Sp, GO+-)" ); fi;
  opts := rec();
  if Length( arg ) > 0 then opts := arg[ 1 ]; fi;
  if IsBound( opts.cap ) then cap := opts.cap; else cap := 50; fi;
  doCent := not IsBound( opts.centralizers ) or opts.centralizers;
  t := Runtime();
  invs := WallClassInvariants( f );
  nr := WallNrClasses( f );
  bad := [];
  for inv in invs do
    x := WallRepresentative( f, inv );
    if not WallIsInGroup( f, x ) or WallInvariant( f, x ) <> inv then Add( bad, inv ); fi;
  od;
  res := rec( nrInvariants := Length( invs ), nrClassesWall := nr,
              badRepresentatives := bad,
              complete := bad = [] and Length( invs ) = nr );
  if doCent then
    ordG := WallGroupOrder( f );
    sum := Sum( invs, inv -> ordG / WallCentralizerOrder( f, inv ) );
    failed := [];
    if res.complete then
      for inv in invs do
        r := WALL2_CentralizerCapped( f, inv, cap );
        if r.status <> "ok" then Add( failed, [ inv, r.status, r.order, r.centralizerOrder ] ); fi;
      od;
    fi;
    res.sumOfClassLengths := sum = ordG;
    res.centralizerFailures := failed;
    res.centralizersCertified := res.complete and res.sumOfClassLengths and failed = [];
  else
    res.centralizersCertified := "skipped";
  fi;
  res.time := Runtime() - t;
  return res;
end );

#############################################################################
#############################################################################
##
##  CONFORMAL GROUPS
##
##  Twisted classes: G-classes of nu-similitudes (x F x^* = nu F) for
##  Sp(2m,q) and GO+-(2m,q), q odd, nu = PrimitiveRoot(K) (a non-square).
##  Twisted duality: roots alpha <-> nu/alpha.  Special factor t^2 - nu with
##  Lambda = GF(q^2) and trivial involution (sign invariants over GF(q^2)).
##
#############################################################################
#############################################################################

# the twisted form record (cached)
BindGlobal( "WALL3_TwistedForm", function( f )
  local ft;
  if IsBound( f.twisted ) then return f.twisted; fi;
  if f.type = "U" or IsBound( f.char2 ) or IsOddInt( f.n ) then
    Error( "twisted classes only for Sp and GO+- in even dimension, q odd" );
  fi;
  ft := ShallowCopy( f );
  Unbind( ft.pieces ); Unbind( ft.group ); Unbind( ft.piElements );
  ft.twist := PrimitiveRoot( f.field );
  ft.special := [ -ft.twist, Zero( f.field ), f.one ];      # t^2 - nu
  f.twisted := ft;
  return ft;
end );

##
##  <#GAPDoc Label="WallMultiplier">
##  <ManSection>
##  <Func Name="WallMultiplier" Arg="f, x"/>
##  <Returns>a field element</Returns>
##  <Description>
##  returns <M>\lambda</M> with <M>x F \bar{x}^{tr} = \lambda F</M>, assuming
##  that <A>x</A> is a similitude (no check).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallMultiplier", function( f, x )
  local M, i, j;
  M := x * f.gram * WALL_Star( f, x );
  i := PositionProperty( f.gram, r -> not IsZero( r ) );
  j := PositionProperty( f.gram[ i ], z -> not IsZero( z ) );
  return M[ i ][ j ] / f.gram[ i ][ j ];
end );

BindGlobal( "WALL3_IsSimilitude", function( ft, x )
  return x * ft.gram * WALL_Star( ft, x ) = ft.twist * ft.gram;
end );

# special component: Lambda = GF(q^2), alpha = sqrt(nu), tau = id
BindGlobal( "WALL3_SpecialLD", function( ft )
  local LD;
  LD := WALL_LambdaData( ft, ft.special, true );
  LD.T := 1;
  return LD;
end );

# sign data for the special part of a twisted x (signs over GF(q^2))
BindGlobal( "WALL3_SpecialSigns", function( ft, x, part )
  local LD, str, H, res, m, tops, h, Q2;
  LD := WALL3_SpecialLD( ft );
  str := WALL_LambdaStructure( ft, LD, x, ft.special, true );
  H := WALL_HFromF( ft, LD, str, ft.gram );
  Q2 := Size( LD.L ); res := [];
  for m in Set( part ) do
    if ft.eps * (-1)^( m - 1 ) = 1 then
      tops := WALL_Tops( str.YL, m );
      h := List( tops, u -> List( tops, v -> u * H * ( v * str.YL^( m - 1 ) ) ) );
      Add( res, [ ft.special, m, WALL_Leg( DeterminantMat( h ), Q2 ) ] );
    fi;
  od;
  return res;
end );

BindGlobal( "WALL3_Invariant", function( ft, x )
  local K, chi, facs, polys, signs, pr, c, part;
  if not WALL3_IsSimilitude( ft, x ) then Error( "WALL3_Invariant: not a nu-similitude" ); fi;
  K := ft.field;
  chi := CharacteristicPolynomial( K, K, x );
  facs := Collected( Factors( PolynomialRing( K ), chi ) );
  polys := []; signs := [];
  for pr in facs do
    c := CoefficientsOfUnivariatePolynomial( pr[ 1 ] );
    c := c / c[ Length( c ) ];
    part := WALL_Partition( ft, x, pr[ 1 ], pr[ 2 ] );
    Add( polys, [ c, part ] );
    if c = ft.special then Append( signs, WALL3_SpecialSigns( ft, x, part ) ); fi;
  od;
  return WALL_MakeInvariant( ft, polys, signs );
end );

# atoms for the twisted duality
BindGlobal( "WALL3_Atoms", function( ft )
  local K, Q, n, atoms, d, e, L, w, N, k0, seen, j, k, o, c, dk, cd, lognu;
  K := ft.field; Q := ft.q; n := ft.n;
  atoms := [];
  # self-dual with tau <> id: alpha^(q^e+1) = nu, degree d = 2e
  for e in [ 1 .. QuoInt( n, 2 ) ] do
    d := 2 * e; L := WALL_ExtField( Q, d ); w := PrimitiveRoot( L ); N := Q^d - 1;
    k0 := ( Q^e - 1 ) / ( Q - 1 );
    seen := [];
    for j in [ 0 .. Q^e ] do
      k := ( k0 + j * ( Q^e - 1 ) ) mod N;
      if k in seen then continue; fi;
      o := WALL_OrbitOf( k, Q, N ); UniteSet( seen, o );
      if Length( o ) <> d then continue; fi;
      c := List( CoefficientsOfUnivariatePolynomial( MinimalPolynomial( K, w^k ) ), WALL_K );
      if c = ft.special then continue; fi;
      Add( atoms, rec( pols := [ c ], weight := d, selfdual := true ) );
    od;
  od;
  # pairs
  for d in [ 1 .. QuoInt( n, 2 ) ] do
    L := WALL_ExtField( Q, d ); w := PrimitiveRoot( L ); N := Q^d - 1;
    lognu := N / ( Q - 1 );
    seen := BlistList( [ 1 .. N ], [] );
    for k in [ 0 .. N - 1 ] do
      if seen[ k + 1 ] then continue; fi;
      o := WALL_OrbitOf( k, Q, N );
      for j in o do seen[ j + 1 ] := true; od;
      if Length( o ) <> d then continue; fi;
      dk := ( lognu - k ) mod N;
      if dk in o then continue; fi;
      for j in WALL_OrbitOf( dk, Q, N ) do seen[ j + 1 ] := true; od;
      c := List( CoefficientsOfUnivariatePolynomial( MinimalPolynomial( K, w^k ) ), WALL_K );
      cd := WALL_DualCoeffs( ft, c );
      Add( atoms, rec( pols := [ c, cd ], weight := 2 * d, selfdual := false ) );
    od;
  od;
  SortBy( atoms, a -> a.weight );
  return atoms;
end );

# determinant class (Legendre symbol) of the form, read off from a twisted
# invariant (orthogonal case)
BindGlobal( "WALL3_DetClass", function( ft, inv )
  local q, lm1, res, p, c, d, dual, s;
  q := ft.q; lm1 := WALL_Leg( -ft.one, q ); res := 1;
  for p in inv.polys do
    c := p[ 1 ]; d := Length( c ) - 1; dual := WALL_DualCoeffs( ft, c );
    if c = ft.special then
      res := res * (-1)^Sum( p[ 2 ] );
    elif dual = c then
      res := res * ( - lm1^( d / 2 ) )^Sum( p[ 2 ] );
    elif c < dual then
      res := res * lm1^( d * Sum( p[ 2 ] ) );
    fi;
  od;
  for s in inv.signs do res := res * s[ 3 ]; od;
  return res;
end );

BindGlobal( "WALL3_SpecialOptions", function( ft, s )
  local res, lam, good, symparts, ch;
  res := [];
  for lam in Partitions( s ) do
    good := ForAll( Set( lam ), m -> ft.eps * (-1)^( m - 1 ) = 1 or
                                     IsEvenInt( Number( lam, i -> i = m ) ) );
    if not good then continue; fi;
    symparts := Filtered( Set( lam ), m -> ft.eps * (-1)^( m - 1 ) = 1 );
    for ch in Tuples( [ 1, -1 ], Length( symparts ) ) do
      Add( res, rec( part := lam,
                     signs := List( [ 1 .. Length( symparts ) ], i -> [ ft.special, symparts[ i ], ch[ i ] ] ) ) );
    od;
  od;
  return res;
end );

BindGlobal( "WALL3_ClassInvariants", function( ft )
  local n, atoms, result, recurse, s, o;
  n := ft.n;
  atoms := WALL3_Atoms( ft );
  result := [];
  recurse := function( start, remaining, polys, signs )
    local i, a, k, lam, inv;
    if remaining = 0 then
      inv := WALL_MakeInvariant( ft, polys, signs );
      if ft.type <> "O" or WALL3_DetClass( ft, inv ) = ft.det then Add( result, inv ); fi;
      return;
    fi;
    for i in [ start .. Length( atoms ) ] do
      a := atoms[ i ];
      if a.weight > remaining then break; fi;
      for k in [ 1 .. QuoInt( remaining, a.weight ) ] do
        for lam in Partitions( k ) do
          recurse( i + 1, remaining - k * a.weight,
                   Concatenation( polys, List( a.pols, c -> [ c, lam ] ) ), signs );
        od;
      od;
    od;
  end;
  for s in [ 0 .. QuoInt( n, 2 ) ] do
    if s = 0 then recurse( 1, n, [], [] );
    else
      for o in WALL3_SpecialOptions( ft, s ) do
        recurse( 1, n - 2 * s, [ [ ft.special, o.part ] ], o.signs );
      od;
    fi;
  od;
  return result;
end );

BindGlobal( "WALL3_CentralizerOrder", function( ft, inv )
  local res, Q, Q2, p, c, d, dual, part, ml, e2, mm, s, sg, ord;
  res := 1; Q := ft.q; Q2 := Q^2;
  for p in inv.polys do
    c := p[ 1 ]; part := p[ 2 ]; d := Length( c ) - 1;
    ml := WALL_Mults( part ); e2 := WALL_E2( part );
    dual := WALL_DualCoeffs( ft, c );
    if c = ft.special then
      if ft.type = "Sp" then
        e2 := e2 + Sum( Filtered( ml, x -> IsEvenInt( x[ 1 ] ) ), x -> x[ 2 ] );
      else
        e2 := e2 - Sum( Filtered( ml, x -> IsEvenInt( x[ 1 ] ) ), x -> x[ 2 ] );
      fi;
      res := res * Q2^( e2 / 2 );
      for mm in ml do
        if ( ft.type = "Sp" ) = IsOddInt( mm[ 1 ] ) then
          res := res * WALL_OrderSp( mm[ 2 ], Q2 );
        else
          s := First( inv.signs, x -> x[ 2 ] = mm[ 1 ] )[ 3 ];
          if IsEvenInt( mm[ 2 ] ) then sg := s; else sg := 0; fi;   # -1 is a square in GF(q^2)
          res := res * WALL_OrderO( mm[ 2 ], Q2, sg );
        fi;
      od;
    elif dual = c then
      ord := Q^( d / 2 );
      res := res * ord^e2 * Product( ml, x -> WALL_OrderGU( x[ 2 ], ord ) );
    elif c < dual then
      res := res * ( Q^d )^e2 * Product( ml, x -> WALL_OrderGL( x[ 2 ], Q^d ) );
    fi;
  od;
  return res;
end );

# special component (like t -+ 1, but over GF(q^2))
BindGlobal( "WALL3_SpecialComponent", function( ft, part, signs )
  local LD, L, ml, comp, mm, mu, m, need, s, h, kind, beta, i, xmu, xs, Hs, nuL;
  LD := WALL3_SpecialLD( ft ); L := LD.L; nuL := PrimitiveRoot( L );
  ml := WALL_Mults( part );
  comp := rec( kind := "self", LD := LD, c := ft.special, parts := [] );
  xs := []; Hs := [];
  for mm in ml do
    mu := mm[ 1 ]; m := mm[ 2 ];
    need := ft.eps * (-1)^( mu - 1 );
    if need = 1 then
      s := First( signs, x -> x[ 2 ] = mu )[ 3 ];
      h := List( IdentityMat( m, L ), ShallowCopy );
      if s = -1 then h[ m ][ m ] := nuL; fi;
      kind := "O";
    else
      h := NullMat( m, m, L );
      for i in [ 1 .. m / 2 ] do h[ i ][ m / 2 + i ] := One( L ); h[ m / 2 + i ][ i ] := -One( L ); od;
      kind := "Sp";
    fi;
    beta := NullMat( mu, mu, L );
    for i in [ 0 .. mu - 1 ] do beta[ i + 1 ][ mu - i ] := (-1)^i * One( L ); od;
    xmu := LD.alpha * WALL_Cayley( ft, LD, WALL_Shift( mu, L ) );
    Add( xs, KroneckerProduct( IdentityMat( m, L ), xmu ) );
    Add( Hs, KroneckerProduct( h, beta ) );
    Add( comp.parts, rec( mu := mu, m := m, h := h, kind := kind ) );
  od;
  comp.xL := WALL_BlockDiag( L, xs );
  comp.HL := WALL_BlockDiag( L, Hs );
  comp.x := WALL_Realize( ft, LD, comp.xL );
  comp.F := WALL_RealizeForm( ft, LD, comp.HL );
  return comp;
end );

BindGlobal( "WALL3_Model", function( ft, inv )
  local comps, p, c, dual;
  comps := [];
  for p in inv.polys do
    c := p[ 1 ]; dual := WALL_DualCoeffs( ft, c );
    if c = ft.special then
      Add( comps, WALL3_SpecialComponent( ft, p[ 2 ], inv.signs ) );
    elif dual = c then
      Add( comps, WALL_SelfDualComponent( ft, c, p[ 2 ], [] ) );
    elif c < dual then
      Add( comps, WALL_PairComponent( ft, c, p[ 2 ] ) );
    fi;
  od;
  return rec( comps := comps,
              x := WALL_BlockDiag( ft.field, List( comps, x -> x.x ) ),
              F := WALL_BlockDiag( ft.field, List( comps, x -> x.F ) ) );
end );

BindGlobal( "WALL3_Representative", function( ft, inv )
  local md, S;
  md := WALL3_Model( ft, inv );
  if md.x * md.F * WALL_Star( ft, md.x ) <> ft.twist * md.F then
    Error( "WALL3_Representative: model is not a nu-similitude" );
  fi;
  S := WallFormIsometry( ft, md.F, ft.gram );
  return S * md.x * S^-1;
end );

BindGlobal( "WALL3_ConjugatingElement", function( ft, x )
  local inv, model, rows, comp, P, S;
  inv := WALL3_Invariant( ft, x );
  model := WALL3_Model( ft, inv );
  rows := [];
  for comp in model.comps do
    Append( rows, WALL_ComponentRows( ft, x, comp ) );
  od;
  P := rows;
  if P * x <> model.x * P or P * ft.gram * WALL_Star( ft, P ) <> model.F then
    Error( "WALL3_ConjugatingElement: adapted basis failed" );
  fi;
  S := WallFormIsometry( ft, model.F, ft.gram );
  return rec( invariant := inv, representative := S * model.x * S^-1, conjugator := S * P );
end );

#############################################################################
##  conformal groups CG(F) = { x : x F x^* = lambda F }
#############################################################################

# "scalar": CG = G Z  (U, odd-dimensional O, characteristic 2)
# "fusion": CG / G Z of order 2 (Sp, GO+- even dimension, q odd)
BindGlobal( "WALL3_ConfKind", function( f )
  if f.type = "U" or IsBound( f.char2 ) or IsOddInt( f.n ) then return "scalar"; fi;
  return "fusion";
end );

# multiplier group generator and its index in the scalar group
BindGlobal( "WALL3_MultGen", function( f )
  local w;
  w := PrimitiveRoot( f.field );
  if f.type = "U" then return w^( f.r + 1 ); fi;
  if f.type = "O" and IsOddInt( f.n ) and not IsBound( f.char2 ) then return w^2; fi;
  return w;
end );

BindGlobal( "WALL3_ScalarFactor", function( f )      # |Z : Z cap G| restricted to the
  if f.type = "U" then return f.r - 1; fi; # multiplier image
  if IsBound( f.char2 ) then return f.q - 1; fi;
  if IsOddInt( f.n ) then return ( f.q - 1 ) / 2; fi;
  return f.q - 1;
end );

##
##  <#GAPDoc Label="WallConformalGroupOrder">
##  <ManSection>
##  <Func Name="WallConformalGroupOrder" Arg="f"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  returns the order of the conformal group <M>CG(F)</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalGroupOrder", function( f )
  return WallGroupOrder( f ) * WALL3_ScalarFactor( f );
end );

# canonical scalar mu and twist flag for a multiplier lambda:
#   x = mu * g,  g in G (twisted = false) or g a nu-similitude (twisted = true)
BindGlobal( "WALL3_ScalarPart", function( f, lambda )
  local w, k;
  w := PrimitiveRoot( f.field );
  if f.type = "U" then
    k := LogFFE( lambda, w^( f.r + 1 ) );
    return rec( mu := w^k, twisted := false );
  fi;
  if IsBound( f.char2 ) then return rec( mu := lambda^( f.q / 2 ), twisted := false ); fi;
  k := LogFFE( lambda, w );
  if IsEvenInt( k ) then return rec( mu := w^( k / 2 ), twisted := false ); fi;
  if IsOddInt( f.n ) then Error( "odd dimension: multipliers are squares" ); fi;
  return rec( mu := w^( ( k - 1 ) / 2 ), twisted := true );
end );

##
##  <#GAPDoc Label="WallConformalMultiplier">
##  <ManSection>
##  <Func Name="WallConformalMultiplier" Arg="f, x"/>
##  <Returns>a field element</Returns>
##  <Description>
##  returns the multiplier <M>\lambda</M> of the similitude <A>x</A>
##  <M>\in CG(F)</M> (for even <M>q</M> and orthogonal forms with respect to the
##  quadratic form); an error is raised if <A>x</A> is not a similitude.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalMultiplier", function( f, x )
  local lambda;
  lambda := WallMultiplier( f, x );
  if x * f.gram * WALL_Star( f, x ) <> lambda * f.gram then
    Error( "x is not a similitude" );
  fi;
  if IsBound( f.quad ) and ForAny( [ 1 .. f.n ], i -> x[ i ] * f.quad * x[ i ] <> lambda * f.quad[ i ][ i ] ) then
    Error( "x is not a similitude of the quadratic form" );
  fi;
  return lambda;
end );

# a fixed similitude with multiplier nu (fusion case)
BindGlobal( "WALL3_Delta", function( f )
  if not IsBound( f.delta ) then
    f.delta := WallFormIsometry( f, f.gram, PrimitiveRoot( f.field ) * f.gram );
  fi;
  return f.delta;
end );

# image of a G-invariant under conjugation by delta: signs of symmetric
# multiplicity forms of odd multiplicity flip
BindGlobal( "WALL3_DeltaImage", function( f, inv )
  local signs, s, p, mult;
  signs := [];
  for s in inv.signs do
    p := First( inv.polys, p -> Length( p[ 1 ] ) = 2 and p[ 1 ][ 1 ] = -s[ 1 ] );
    mult := Number( p[ 2 ], i -> i = s[ 2 ] );
    Add( signs, [ s[ 1 ], s[ 2 ], s[ 3 ] * (-1)^mult ] );
  od;
  return WALL_MakeInvariant( f, inv.polys, signs );
end );
BindGlobal( "WALL3_FusionCanonical", function( f, inv )
  local i2;
  i2 := WALL3_DeltaImage( f, inv );
  if i2.signs < inv.signs then return i2; fi;
  return inv;
end );

##
##  <#GAPDoc Label="WallConformalInvariant">
##  <ManSection>
##  <Func Name="WallConformalInvariant" Arg="f, x"/>
##  <Returns>a record</Returns>
##  <Description>
##  returns the class invariant <C>rec( mult, twisted, inv )</C> of <A>x</A>
##  <M>\in CG(F)</M>; two elements are conjugate in <M>CG(F)</M> if and only if
##  their invariants are equal.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalInvariant", function( f, x )
  local lambda, sp, g, inv;
  lambda := WallConformalMultiplier( f, x );
  sp := WALL3_ScalarPart( f, lambda );
  g := sp.mu^-1 * x;
  if sp.twisted then
    inv := WALL3_Invariant( WALL3_TwistedForm( f ), g );
  else
    inv := WallInvariant( f, g );
    if WALL3_ConfKind( f ) = "fusion" then inv := WALL3_FusionCanonical( f, inv ); fi;
  fi;
  return rec( mult := lambda, twisted := sp.twisted, inv := inv );
end );

##
##  <#GAPDoc Label="WallConformalClassInvariants">
##  <ManSection>
##  <Func Name="WallConformalClassInvariants" Arg="f"/>
##  <Returns>a list of records</Returns>
##  <Description>
##  returns the invariants of all conjugacy classes of <M>CG(F)</M>: records
##  <C>rec( mult, twisted, inv )</C> with the multiplier <C>mult</C>, a flag
##  <C>twisted</C> (<K>true</K> for the classes of non-square multiplier in the
##  symplectic and even-dimensional orthogonal cases for odd <M>q</M>), and
##  <C>inv</C>, the invariant of <M>\mu^{-1} x</M> for a canonical scalar
##  <M>\mu</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalClassInvariants", function( f )
  local res, w, lambdas, lambda, sp, ginvs, tinvs, inv;
  res := [];
  w := WALL3_MultGen( f );
  lambdas := List( [ 0 .. Order( w ) - 1 ], k -> w^k );
  ginvs := WallClassInvariants( f );
  if WALL3_ConfKind( f ) = "fusion" then
    ginvs := Filtered( ginvs, i -> WALL3_FusionCanonical( f, i ) = i );
    tinvs := WALL3_ClassInvariants( WALL3_TwistedForm( f ) );
  fi;
  for lambda in lambdas do
    sp := WALL3_ScalarPart( f, lambda );
    if sp.twisted then
      Append( res, List( tinvs, i -> rec( mult := lambda, twisted := true, inv := i ) ) );
    else
      Append( res, List( ginvs, i -> rec( mult := lambda, twisted := false, inv := i ) ) );
    fi;
  od;
  return res;
end );

##
##  <#GAPDoc Label="WallConformalNrClasses">
##  <ManSection>
##  <Func Name="WallConformalNrClasses" Arg="f"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  returns the number of conjugacy classes of <M>CG(F)</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalNrClasses", function( f )
  return Length( WallConformalClassInvariants( f ) );
end );

##
##  <#GAPDoc Label="WallConformalCentralizerOrder">
##  <ManSection>
##  <Func Name="WallConformalCentralizerOrder" Arg="f, ci"/>
##  <Func Name="WallConformalClassSize" Arg="f, ci"/>
##  <Returns>a positive integer</Returns>
##  <Description>
##  return the centralizer order in <M>CG(F)</M> and the size of the class
##  with invariant <A>ci</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalCentralizerOrder", function( f, ci )
  local c;
  if ci.twisted then
    return ( f.q - 1 ) * WALL3_CentralizerOrder( WALL3_TwistedForm( f ), ci.inv );
  fi;
  c := WallCentralizerOrder( f, ci.inv );
  if WALL3_ConfKind( f ) = "scalar" then return c * WALL3_ScalarFactor( f ); fi;
  if WALL3_DeltaImage( f, ci.inv ) = ci.inv then return c * ( f.q - 1 ); fi;
  return c * ( f.q - 1 ) / 2;
end );

BindGlobal( "WallConformalClassSize", function( f, ci )
  return WallConformalGroupOrder( f ) / WallConformalCentralizerOrder( f, ci );
end );

##
##  <#GAPDoc Label="WallConformalRepresentative">
##  <ManSection>
##  <Func Name="WallConformalRepresentative" Arg="f, ci"/>
##  <Returns>a matrix</Returns>
##  <Description>
##  returns a representative of the class of <M>CG(F)</M> with invariant
##  <A>ci</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalRepresentative", function( f, ci )
  local sp;
  sp := WALL3_ScalarPart( f, ci.mult );
  if ci.twisted then return sp.mu * WALL3_Representative( WALL3_TwistedForm( f ), ci.inv ); fi;
  return sp.mu * WallRepresentative( f, ci.inv );
end );

##
##  <#GAPDoc Label="WallConformalConjugatingElement">
##  <ManSection>
##  <Func Name="WallConformalConjugatingElement" Arg="f, x"/>
##  <Returns>a record</Returns>
##  <Description>
##  For <A>x</A> <M>\in CG(F)</M>, returns a record with components
##  <C>invariant</C>, <C>representative</C> <M>r</M> and <C>conjugator</C>
##  <M>y \in CG(F)</M> with <M>y x y^{-1} = r</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalConjugatingElement", function( f, x )
  local ci, sp, g, a, inv, d, y;
  ci := WallConformalInvariant( f, x );
  sp := WALL3_ScalarPart( f, ci.mult );
  g := sp.mu^-1 * x;
  if ci.twisted then
    a := WALL3_ConjugatingElement( WALL3_TwistedForm( f ), g );
    y := a.conjugator;
  else
    inv := WallInvariant( f, g );
    if inv = ci.inv then
      a := WallConjugatingElement( f, g ); y := a.conjugator;
    else
      d := WALL3_Delta( f );
      a := WallConjugatingElement( f, d * g * d^-1 ); y := a.conjugator * d;
    fi;
  fi;
  return rec( invariant := ci, representative := sp.mu * a.representative, conjugator := y );
end );

##
##  <#GAPDoc Label="WallConformalRepresentativeWithCentralizer">
##  <ManSection>
##  <Func Name="WallConformalRepresentativeWithCentralizer" Arg="f, ci"/>
##  <Returns>a record</Returns>
##  <Description>
##  returns a record with components <C>representative</C>,
##  <C>generators</C> (of its centralizer in <M>CG(F)</M>) and
##  <C>centralizerOrder</C>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalRepresentativeWithCentralizer", function( f, ci )
  local sp, r, gens, d, g0, a, w;
  sp := WALL3_ScalarPart( f, ci.mult );
  w := PrimitiveRoot( f.field ) * IdentityMat( f.n, f.field );
  if ci.twisted then
    r := WallRepresentativeWithCentralizer( WALL3_TwistedForm( f ), ci.inv );
    gens := Concatenation( r.generators, [ w, r.representative ] );
  else
    r := WallRepresentativeWithCentralizer( f, ci.inv );
    gens := Concatenation( r.generators, [ w ] );
    if WALL3_ConfKind( f ) = "fusion" and WALL3_DeltaImage( f, ci.inv ) = ci.inv then
      d := WALL3_Delta( f ); g0 := r.representative;
      a := WallConjugatingElement( f, d * g0 * d^-1 );
      Add( gens, a.conjugator * d );
    fi;
  fi;
  return rec( representative := sp.mu * r.representative, generators := gens,
              centralizerOrder := WallConformalCentralizerOrder( f, ci ) );
end );

##
##  <#GAPDoc Label="WallConformalCentralizer">
##  <ManSection>
##  <Func Name="WallConformalCentralizer" Arg="f, x"/>
##  <Returns>a list of matrices</Returns>
##  <Description>
##  returns generators of the centralizer of <A>x</A> in <M>CG(F)</M>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalCentralizer", function( f, x )
  local a, r, yi;
  a := WallConformalConjugatingElement( f, x );
  r := WallConformalRepresentativeWithCentralizer( f, a.invariant );
  yi := a.conjugator^-1;
  return List( r.generators, g -> yi * g * a.conjugator );
end );

# GAP's classical group transported to the form f, and the conformal group
# form attributes of G(F), so that GAP tests membership by the form
BindGlobal( "WALL_SetFormAttributes", function( f, G )
  if f.type = "U" then
    SetInvariantSesquilinearForm( G, rec( matrix := f.gram ) );
    SetIsFullSubgroupGLorSLRespectingSesquilinearForm( G, true );
  elif IsBound( f.quad ) then
    SetInvariantQuadraticForm( G, rec( matrix := f.quad ) );
    SetInvariantBilinearForm( G, rec( matrix := f.gram ) );
    SetIsFullSubgroupGLorSLRespectingQuadraticForm( G, true );
  else
    SetInvariantBilinearForm( G, rec( matrix := f.gram ) );
    SetIsFullSubgroupGLorSLRespectingBilinearForm( G, true );
  fi;
end );

##
##  <#GAPDoc Label="WallGroup">
##  <ManSection>
##  <Func Name="WallGroup" Arg="f"/>
##  <Returns>a matrix group</Returns>
##  <Description>
##  returns the isometry group <M>G(F)</M> of the form record <A>f</A> as a
##  &GAP; matrix group (&GAP;'s classical group transported to the form). Its size
##  and invariant forms are stored, so membership tests are cheap.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallGroup", function( f )
  local G0, F0, Q0, S, nu;
  if IsBound( f.oddChar2 ) then return WALL2_OddGroup( f ); fi;
  if IsBound( f.group ) then return f.group; fi;
  if IsBound( f.char2 ) then return WALL2_Group( f ); fi;
  if f.type = "U" then
    G0 := GU( f.n, f.r ); F0 := InvariantSesquilinearForm( G0 ).matrix;
  elif f.type = "Sp" then
    G0 := Sp( f.n, f.q ); F0 := InvariantBilinearForm( G0 ).matrix;
  else
    if IsOddInt( f.n ) then G0 := GO( f.n, f.q ); else G0 := GO( f.sign, f.n, f.q ); fi;
    F0 := InvariantBilinearForm( G0 ).matrix;
    if IsOddInt( f.n ) and WALL_Leg( DeterminantMat( F0 ), f.q ) <> f.det then
      F0 := PrimitiveRoot( f.field ) * F0;
    fi;
  fi;
  S := WallFormIsometry( f, F0, f.gram );
  f.group := Group( List( GeneratorsOfGroup( G0 ), g -> S * g * S^-1 ) );
  SetSize( f.group, WallGroupOrder( f ) );
  WALL_SetFormAttributes( f, f.group );
  return f.group;
end );

##
##  <#GAPDoc Label="WallConformalGroup">
##  <ManSection>
##  <Func Name="WallConformalGroup" Arg="f"/>
##  <Returns>a matrix group</Returns>
##  <Description>
##  returns the conformal group <M>CG(F)</M> of all similitudes
##  <M>x F \bar{x}^{tr} = \lambda F</M> (for even <M>q</M> and orthogonal
##  forms: <M>Q(vx) = \lambda Q(v)</M>) as a &GAP; matrix group, with its size
##  stored.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "WallConformalGroup", function( f )
  local gens, CG;
  gens := ShallowCopy( GeneratorsOfGroup( WallGroup( f ) ) );
  Add( gens, PrimitiveRoot( f.field ) * IdentityMat( f.n, f.field ) );
  if WALL3_ConfKind( f ) = "fusion" then Add( gens, WALL3_Delta( f ) ); fi;
  CG := Group( gens );
  SetSize( CG, WallConformalGroupOrder( f ) );
  return CG;
end );

#############################################################################
##  characteristic 2: labels by the algorithm of De Franceschi-Liebeck-
##  O'Brien, Sect. 5.3 (Lemmas 5.3.1-5.3.5, Thm. 5.3.6)
#############################################################################

# action of x and Gram matrix on the quotient Fs/Rad(Fs) of an x-invariant
# subspace Fs (rows); returns rec( N, G ) in a basis of a complement of Rad
BindGlobal( "WALL2_QuotientData", function( K, x, F, Fs )
  local G, R, Cc, Cb, Rb, I, N, n;
  Fs := BaseMat( Fs );
  G := Fs * F * TransposedMat( Fs );
  R := NullspaceMat( G );
  I := IdentityMat( Length( Fs ), K );
  if Length( R ) = 0 then Cc := I; else Cc := BaseSteinitzVectors( I, R ).factorspace; fi;
  Cb := Cc * Fs;
  if Length( R ) = 0 then Rb := []; else Rb := R * Fs; fi;
  n := Length( Cb );
  N := List( Cb, c -> SolutionMat( Concatenation( Cb, Rb ), c * x - c ){ [ 1 .. n ] } );
  return rec( N := N, G := Cb * F * TransposedMat( Cb ) );
end );

BindGlobal( "WALL2_IsIrredAS", function( q, c )        # x^2 + x + c irreducible
  return IsOne( WALL2_Tr2( c, q ) );
end );

# beta (0 or 1, i.e. 0 or alpha) of a single block U0 (rows, x-invariant,
# non-degenerate) of block size r, kind "W" (two blocks, r odd) or "V" (one
# block, r even), by De Franceschi-Liebeck-O'Brien, Lemmas 5.3.1, 5.3.3, 5.3.4
BindGlobal( "WALL2_BlockBeta", function( f, x, F, Qm, U0, r, kind )
  local K, q, N, Fs, qd, e, v1, w1, v2, w2, v3, g1, g2, g3, lam, mu;
  K := f.field; q := f.q; N := x - IdentityMat( Length( x ), K );
  if r <= 2 then
    if f.type = "O" then return WallClassicalForm( "O", U0 * Qm * TransposedMat( U0 ), K ).arf; fi;
    return 0;
  fi;
  if kind = "W" then
    Fs := List( U0, v -> v * N^( ( r - 3 ) / 2 ) );
    qd := WALL2_QuotientData( K, x, F, Fs );
    e := WALL_Tops( qd.N, 3 ); v1 := e[ 1 ]; w1 := e[ 2 ];
    v2 := v1 * qd.N; w2 := w1 * qd.N;
    g1 := v2 * qd.G * w2; g2 := v1 * qd.G * v2; g3 := w1 * qd.G * w2;
    if IsZero( g1 ) then return 0; fi;
    if WALL2_IsIrredAS( q, g2 * g3 / g1^2 ) then return 1; fi;
    return 0;
  fi;
  Fs := List( U0, v -> v * N^( r / 2 - 2 ) );
  qd := WALL2_QuotientData( K, x, F, Fs );
  v1 := WALL_Tops( qd.N, 4 )[ 1 ];
  v2 := v1 * qd.N; v3 := v2 * qd.N;
  lam := v2 * qd.G * v3; mu := v1 * qd.G * v2;
  if WALL2_IsIrredAS( q, mu / lam ) then return 1; fi;
  return 0;
end );

BindGlobal( "WALL2_UnipotentLabelsDLO", function( f, x, F, Qm )
  local K, q, n, I, N, part, sl, M, blocks, sub, restr, r, Ub, U, Uall, h, i, j, a, b,
        U0, e, Fs, qd, t, v1, w1, v2, w2, g1, g2, g3, beta, k, lam, mu, v3, comp,
        sizes, S, cls, merged, changed, nA, S0, comps, free, d0free, deltas, delta0, L, sz;
  K := f.field; q := f.q; n := Length( x ); I := IdentityMat( n, K ); N := x - I;
  part := WALL_Partition( f, x, UnivariatePolynomial( K, [ f.one, f.one ] ), n );
  sl := WALL2_SBits( K, x, F, part );
  # restriction of N to a subspace (rows): matrix in coordinates of the rows
  restr := B -> List( B, v -> SolutionMat( B, v * N ) );
  # orthogonal complement of the rows U inside the rows B
  comp := function( B, U )
    local c;
    if Length( U ) = 0 then return B; fi;
    c := NullspaceMat( B * F * TransposedMat( U ) );
    if Length( c ) = 0 then return []; fi;
    return c * B;
  end;
  M := I; blocks := [];
  while Length( M ) > 0 do
    sub := restr( M );
    r := 1; e := sub; while not IsZero( e ) do e := e * sub; r := r + 1; od;
    # homocyclic component of block size r
    Ub := Concatenation( List( WALL_Tops( sub, r ), t -> List( [ 0 .. r - 1 ], i -> t * sub^i ) ) ) * M;
    Uall := Ub; U := Ub;
    while Length( U ) > 0 do
      sub := restr( U );
      t := WALL_Tops( sub, r );
      h := List( t, a -> List( t, b -> a * ( U * F * TransposedMat( U ) ) * ( b * sub^( r - 1 ) ) ) );
      if IsOddInt( r ) then
        i := First( [ 1 .. Length( t ) ], i -> not IsZero( h[ i ] ) );
        j := PositionProperty( h[ i ], z -> not IsZero( z ) );
        U0 := Concatenation( List( [ t[ i ], t[ j ] ], a -> List( [ 0 .. r - 1 ], k -> a * sub^k ) ) ) * U;
        beta := WALL2_BlockBeta( f, x, F, Qm, U0, r, "W" );
        Add( blocks, [ r, "W", beta ] );
      else
        k := r / 2;
        i := First( [ 1 .. Length( t ) ], i -> not IsZero( h[ i ][ i ] ) );
        if i = fail then
          # U = W(2k)^a  (Lemma 5.3.2)
          Append( blocks, List( [ 1 .. Length( t ) / 2 ], i -> [ r, "W", 0 ] ) );
          break;
        fi;
        U0 := List( [ 0 .. r - 1 ], k -> t[ i ] * sub^k ) * U;
        beta := WALL2_BlockBeta( f, x, F, Qm, U0, r, "V" );
        Add( blocks, [ r, "V", beta ] );
      fi;
      U := comp( U, U0 );
    od;
    M := comp( M, Uall );
  od;
  # Step 5: equivalence classes of block sizes
  sizes := Set( blocks, b -> b[ 1 ] );
  S := Filtered( sizes, r -> IsOddInt( r ) or ForAny( blocks, b -> b[ 1 ] = r and b[ 2 ] = "V" ) );
  cls := List( sizes, r -> [ r ] );
  repeat
    changed := false;
    for a in [ 1 .. Length( cls ) ] do
      for b in [ a + 1 .. Length( cls ) ] do
        if ForAny( cls[ a ], r -> ForAny( cls[ b ], s -> r in S and s in S and
             ( AbsInt( r - s ) = 1 or ( AbsInt( r - s ) = 2 and IsEvenInt( r ) and IsEvenInt( s ) ) ) ) ) then
          cls[ a ] := Union( cls[ a ], cls[ b ] ); Remove( cls, b ); changed := true; break;
        fi;
      od;
      if changed then break; fi;
    od;
  until not changed;
  nA := S0 -> Sum( Filtered( blocks, b -> b[ 1 ] in S0 ), b -> b[ 3 ] ) mod 2;
  # translate to Wall's labels (component sets of P-indices, delta0)
  comps := WALL2_ComponentSets( part, sl );
  free := Filtered( comps, L -> WALL2_DeltaFree( f.type, L, sl ) );
  d0free := f.type = "O" and WALL2_SOf( sl, 2 ) = 0 and 1 in part;
  deltas := [];
  for L in free do
    S0 := First( cls, c -> L[ 1 ] + 1 in c );
    if not IsSubset( S0, List( L, e -> e + 1 ) ) then Error( "WALL2_UnipotentLabelsDLO: component sets differ" ); fi;
    if f.type = "Sp" and 2 in S0 then Add( deltas, [ L, 0 ] ); else Add( deltas, [ L, nA( S0 ) ] ); fi;
  od;
  if d0free then delta0 := nA( [ 1 ] ); else delta0 := fail; fi;
  return rec( part := part, s := sl, deltas := deltas, delta0 := delta0 );
end );

# |C_G(u)| for a unipotent u in Sp(V) or O(V) (q even; for O: u in Omega,
# i.e. an even number of V-blocks) after Liebeck-Seitz [Thm. 7.3], as stated in
# De Franceschi-Liebeck-O'Brien, Thm. 5.2.1.  Independent check of Wall's
# Thm. 3.7.4 (WALL2_UnipotentCentralizerOrder).
BindGlobal( "WALL2_LSCentralizerOrder", function( f, part, slist, deltas, delta0 )
  local q, ml, Vsizes, a, f2, Nu, chi, i, mm, m, dimSum, ordProd, Ls, L, eps, ks, t, delta,
        hasV, odd, sp, dimSp, dimO, b;
  q := f.q;
  ml := WALL_Mults( part );
  hasV := m -> IsEvenInt( m ) and WALL2_SOf( slist, m ) = 1;
  Vsizes := Filtered( Set( part ), hasV );
  chi := function( n )
    if f.type = "Sp" then
      if hasV( n ) then return n / 2; fi; return QuoInt( n - 1, 2 );
    fi;
    if hasV( n ) then return ( n + 2 ) / 2; fi; return QuoInt( n + 1, 2 );
  end;
  f2 := Reversed( SortedList( part ) );
  Nu := Sum( [ 1 .. Length( f2 ) ], i -> i * f2[ i ] - chi( f2[ i ] ) );
  dimSp := a -> a * ( 2 * a + 1 ); dimO := a -> a * ( 2 * a - 1 );
  Ls := WALL2_ComponentSets( part, slist );
  dimSum := 0; ordProd := 1;
  for mm in ml do
    m := mm[ 1 ];
    if IsEvenInt( m ) then
      if hasV( m ) then b := 2 - ( mm[ 2 ] mod 2 ); else b := 0; fi;    # number of V-blocks
      a := ( mm[ 2 ] - b ) / 2;
      dimSum := dimSum + dimSp( a ); ordProd := ordProd * WALL_OrderSp( 2 * a, q );
    else
      a := mm[ 2 ] / 2;
      if ( m + 1 ) in Vsizes or ( m - 1 ) in Vsizes or ( m = 1 and f.type = "Sp" ) then
        dimSum := dimSum + dimSp( a ); ordProd := ordProd * WALL_OrderSp( 2 * a, q );
      else
        # O^eps_{2a}, eps from the parameter of the W-blocks of size m
        if m = 1 then
          if delta0 = 1 then eps := -1; else eps := 1; fi;
        else
          L := First( Ls, L -> m - 1 in L );
          if First( deltas, d -> d[ 1 ] = L ) <> fail and First( deltas, d -> d[ 1 ] = L )[ 2 ] = 1 then
            eps := -1; else eps := 1; fi;
        fi;
        dimSum := dimSum + dimO( a ); ordProd := ordProd * WALL_OrderO( 2 * a, q, eps );
      fi;
    fi;
  od;
  ks := Reversed( List( Vsizes, m -> m / 2 ) );
  t := Number( [ 1 .. Length( ks ) - 1 ], j -> ks[ j ] - ks[ j + 1 ] >= 2 );
  if Vsizes = [] or ( f.type = "Sp" and 2 in Vsizes ) then delta := 0; else delta := 1; fi;
  return q^( Nu - dimSum ) * ordProd * 2^( t + delta );
end );


#############################################################################
##  GO(2m+1,q), q even:  isomorphism with Sp(2m,q)
##
##  The polar form B of Q has a radical <r> of dimension 1 with Q(r) <> 0.
##  An isometry fixes r, and its action on V/<r> preserves the induced
##  symplectic form: this gives GO(V,Q) -> Sp(V/<r>), an isomorphism.
##  With the basis T = (w_1, ..., w_2m, r):
##    image(x)    = upper left 2m x 2m block of T x T^-1,
##    preimage(s) = T^-1 [[ s, lambda ], [ 0, 1 ]] T,
##                  lambda_i = sqrt( ( Q(w_i s) + Q(w_i) ) / Q(r) ).
##  All other functions for such forms delegate to the symplectic group.
#############################################################################

BindGlobal( "WALL2_OddForm", function( F, K )
  local n, q, Qm, i, j, B, r, W, T, f, Fsp;
  n := Length( F ); q := Size( K );
  Qm := List( F, ShallowCopy );
  for i in [ 1 .. n ] do
    for j in [ 1 .. i - 1 ] do
      Qm[ j ][ i ] := Qm[ j ][ i ] + Qm[ i ][ j ]; Qm[ i ][ j ] := Zero( K );
    od;
  od;
  B := Qm + TransposedMat( Qm );
  r := NullspaceMat( B );
  if Length( r ) <> 1 then Error( "WallClassicalForm: degenerate quadratic form" ); fi;
  r := r[ 1 ];
  if IsZero( r * Qm * r ) then Error( "WallClassicalForm: degenerate quadratic form" ); fi;
  W := BaseSteinitzVectors( IdentityMat( n, K ), [ r ] ).factorspace;
  T := Concatenation( W, [ r ] );
  Fsp := W * B * TransposedMat( W );
  f := rec( type := "O", field := K, n := n, p := 2, one := One( K ), q := q,
            sigma := 1, eps := 1, char2 := true, oddChar2 := true, sign := 0,
            quad := Immutable( Qm ), gram := Immutable( B ),
            radical := r, Qr := r * Qm * r, T := T, Ti := T^-1,
            sp := WALL2_Form( "Sp", Fsp, K ) );
  return f;
end );

# image in the symplectic group of the form f.sp
BindGlobal( "WALL2_OddImage", function( f, x )
  local m;
  m := f.n - 1;
  return ( f.T * x * f.Ti ){ [ 1 .. m ] }{ [ 1 .. m ] };
end );

# preimage of an element s of Sp(f.sp)
BindGlobal( "WALL2_OddPreImage", function( f, s )
  local K, n, m, W, X, i, ws, d;
  K := f.field; n := f.n; m := n - 1;
  W := f.T{ [ 1 .. m ] };
  X := NullMat( n, n, K );
  for i in [ 1 .. m ] do
    X[ i ]{ [ 1 .. m ] } := s[ i ];
    ws := s[ i ] * W;
    d := ( ws * f.quad * ws + W[ i ] * f.quad * W[ i ] ) / f.Qr;
    X[ i ][ n ] := d^( f.q / 2 );               # square root in characteristic 2
  od;
  X[ n ][ n ] := One( K );
  return f.Ti * X * f.T;
end );

##
##  <#GAPDoc Label="IsomorphismSymplecticGroup">
##  <ManSection>
##  <Func Name="IsomorphismSymplecticGroup" Arg="G"/>
##  <Returns>a group homomorphism</Returns>
##  <Description>
##  For an orthogonal group <A>G</A> <M>= GO(2m+1,q)</M> with even <M>q</M>
##  (or a form record of such a group), returns the isomorphism onto
##  <M>Sp(2m,q)</M> induced on <M>V/\mathrm{Rad}(B)</M>, where <M>B</M> is the
##  polar form. Images and preimages are computed with <M>O(n^2)</M> field
##  operations. All class functions for such a form record delegate to
##  <M>Sp(2m,q)</M> through this isomorphism; the invariants are those of the
##  image.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal( "IsomorphismSymplecticGroup", function( arg... )
  local f, G, H;
  if IsGroup( arg[ 1 ] ) then f := WallFormOfGroup( arg[ 1 ] ); else f := arg[ 1 ]; fi;
  if not IsBound( f.oddChar2 ) then
    Error( "IsomorphismSymplecticGroup: needs an orthogonal form in odd dimension, q even" );
  fi;
  G := WallGroup( f ); H := WallGroup( f.sp );
  return GroupHomomorphismByFunction( G, H, x -> WALL2_OddImage( f, x ),
                                      s -> WALL2_OddPreImage( f, s ) );
end );

# delegation of the main functions
BindGlobal( "WALL2_OddGroup", function( f )
  if not IsBound( f.group ) then
    f.group := Group( List( GeneratorsOfGroup( WallGroup( f.sp ) ), s -> WALL2_OddPreImage( f, s ) ) );
    SetSize( f.group, WallGroupOrder( f.sp ) );
    WALL_SetFormAttributes( f, f.group );
  fi;
  return f.group;
end );

BindGlobal( "WALL2_OddConjugatingElement", function( f, x )
  local a;
  a := WallConjugatingElement( f.sp, WALL2_OddImage( f, x ) );
  return rec( invariant := a.invariant,
              representative := WALL2_OddPreImage( f, a.representative ),
              conjugator := WALL2_OddPreImage( f, a.conjugator ) );
end );

BindGlobal( "WALL2_OddRepresentativeWithCentralizer", function( f, inv )
  local r;
  r := WallRepresentativeWithCentralizer( f.sp, inv );
  return rec( representative := WALL2_OddPreImage( f, r.representative ),
              generators := List( r.generators, s -> WALL2_OddPreImage( f, s ) ),
              centralizerOrder := r.centralizerOrder );
end );
