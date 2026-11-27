###########################################################################
##  ClUtils.gi
##
##  (C) 2026 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##
##  Enumeration of monic irreducible polynomials over finite fields, also
##  grouped with respect to the duality used for classical groups.
##
##  The roots of the polynomials of degree d over F = GF(q) are the powers
##  w^k of a root w of a primitive polynomial of degree d, and the
##  polynomials correspond to the orbits of k -> q*k on Z/(q^d-1) of
##  length d.  Instead of computing in the field GF(q^d) we use the linear
##  recurrence a_t = lambda(w^t), lambda the first coordinate with respect to
##  the basis 1, w, ..., w^(d-1); the minimal polynomial of w^k is found by
##  the Berlekamp-Massey algorithm from the subsequence a_0, a_k, a_2k, ...
##
##  Costs, N = q^d - 1, R the number of results:
##  Step                               Cost
##  Scalar recurrence table            O(Nh) operations in F (h = number of
##                                     nonzero coefficients of the input)
##  Cyclotomic coset enumeration       O(N) modular-index operations
##  Berlekamp-Massey for all answers   O(R d^2) operations in F
##  Storage, including output          O(N) field-element slots, plus a bitlist
##

##  <#GAPDoc Label="MonicIrreduciblesFromPrimitivePolynomial">
##  <ManSection>
##  <Func Name="MonicIrreduciblesFromPrimitivePolynomial" Arg="F, coeff"/>
##  <Returns>a list of coefficient lists</Returns>
##  <Description>
##  Let <A>F</A> be a finite field with <M>q</M> elements and <A>coeff</A>
##  the coefficient list (constant term first) of a monic primitive
##  polynomial of degree <M>d</M> over <A>F</A>. This function returns the
##  list of all monic irreducible polynomials of degree <M>d</M> over
##  <A>F</A>, each given by its coefficient list (constant term first).
##  <P/>
##  Instead of <A>coeff</A> one can also give the degree <M>d</M>, then a
##  random primitive polynomial of degree <M>d</M> is used (see <Ref
##  BookName="Reference" Func="RandomPrimitivePolynomial"/>). The order of
##  the result depends on the primitive polynomial.
##  <P/>
##  The primitivity of the input polynomial is not checked. The
##  computation does not use the field with <M>q^d</M> elements, it uses
##  <M>O(q^d)</M> operations in <A>F</A> and storage for <M>q^d</M> elements
##  of <A>F</A>. For <M>d = 1</M> the
##  result contains all <M>q</M> polynomials <M>X-a</M>, <M>a \in</M>
##  <A>F</A>.
##
##  <Example>gap> c := CoefficientsOfUnivariatePolynomial(ConwayPolynomial(3,2));
##  [ Z(3), Z(3), Z(3)^0 ]
##  gap> l := MonicIrreduciblesFromPrimitivePolynomial(GF(3), c);;
##  gap> List(l, a -> UnivariatePolynomial(GF(3), a, 1));
##  [ x_1^2-x_1-Z(3)^0, x_1^2+Z(3)^0, x_1^2+x_1-Z(3)^0 ]
##  gap> Length(MonicIrreduciblesFromPrimitivePolynomial(GF(5), 6));
##  2580
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal("MonicIrreduciblesFromPrimitivePolynomial", function(F, coeff)
    local q, d, N, zero, one, negcoeff, support,
          a, seen, seq, result, BM,
          t, j, v, k, r, orbitLength, pos;

    # Basic validation. Irreducibility and primitivity are assumed.
    if not IsField(F) or not IsFinite(F) then
        Error("F must be a finite field");
    fi;

    if IsInt(coeff) then
      if coeff < 1 then
        Error("degree must be at least 1");
      else
        coeff := CoefficientsOfUnivariatePolynomial(
                           RandomPrimitivePolynomial(F, coeff));
      fi;
    fi;

    if not IsList(coeff) or Length(coeff) < 2 then
        Error("coeff must be a coefficient list of positive degree");
    fi;

    q := Size(F);
    d := Length(coeff) - 1;
    zero := Zero(F);
    one := One(F);

    if not ForAll(coeff, x -> x in F) then
        Error("all coefficients must belong to F");
    fi;
    if coeff[d + 1] <> one then
        Error("the input polynomial must be monic");
    fi;
    if coeff[1] = zero then
        Error("a primitive polynomial must have nonzero constant term");
    fi;

    # Degree 1: include X, which does not arise from a nonzero power of w.
    if d = 1 then
        return List(AsList(F), x -> [-x, one]);
    fi;

    N := q^d - 1;

    # Berlekamp-Massey, specialized to sequences of length 2*d
    # whose minimal recurrence has degree exactly d.
    #
    # C represents the connection polynomial:
    #   s_n + C[2]*s_(n-1) + ... + C[L+1]*s_(n-L) = 0.
    #
    # Its reversed coefficient list is the desired monic polynomial.
    BM := function(s)
        local C, B, oldC, L, LB, shift, prevDelta,
              delta, factor, n, i;

        C := ListWithIdenticalEntries(d + 1, zero);
        C[1] := one;
        B := ShallowCopy(C);

        L := 0;
        LB := 0;
        shift := 1;
        prevDelta := one;

        for n in [0 .. 2*d - 1] do
            delta := s[n + 1];
            for i in [1 .. L] do
                delta := delta + C[i + 1] * s[n - i + 1];
            od;

            if delta = zero then
                shift := shift + 1;
            else
                if 2*L <= n then
                    oldC := ShallowCopy(C);
                fi;

                factor := delta / prevDelta;
                for i in [0 .. LB] do
                    C[i + shift + 1] :=
                        C[i + shift + 1] - factor * B[i + 1];
                od;

                if 2*L <= n then
                    B := oldC;
                    LB := L;
                    L := n + 1 - L;
                    prevDelta := delta;
                    shift := 1;
                else
                    shift := shift + 1;
                fi;
            fi;
        od;

        if L <> d then
            Error("unexpected recurrence degree; check the input polynomial");
        fi;

        return Reversed(C);
    end;

    # Build one period of a_t = lambda(w^t), where lambda extracts
    # the constant coefficient in the basis 1,w,...,w^(d-1).
    #
    # Thus a_0 = 1, a_1 = ... = a_(d-1) = 0, followed by
    # the recurrence given by coeff.
    #
    # GAP indexing: a[t+1] represents a_t.
    a := ListWithIdenticalEntries(N, zero);
    a[1] := one;

    negcoeff := List(coeff{[1 .. d]}, x -> -x);
    support := Filtered([1 .. d], i -> negcoeff[i] <> zero);

    for t in [d .. N - 1] do
        v := zero;
        for j in support do
            v := v + negcoeff[j] * a[t - d + j];
        od;
        a[t + 1] := v;
    od;

    # A packed boolean list for orbit bookkeeping.
    seen := BlistList([1 .. N], []);

    seq := ListWithIdenticalEntries(2*d, zero);
    result := [];

    for k in [0 .. N - 1] do
        if not seen[k + 1] then

            # Mark the entire q-cyclotomic coset of k modulo N.
            r := k;
            orbitLength := 0;
            repeat
                seen[r + 1] := true;
                orbitLength := orbitLength + 1;
                r := (q * r) mod N;
            until r = k;

            # Only full-size orbits give degree-d polynomials.
            if orbitLength = d then

                # seq[j+1] = a_(k*j mod N).
                # Repeated addition avoids multiplication/mod at each step.
                pos := 0;
                for j in [1 .. 2*d] do
                    seq[j] := a[pos + 1];
                    pos := pos + k;
                    if pos >= N then
                        pos := pos - N;
                    fi;
                od;

                Add(result, BM(seq));
            fi;
        fi;
    od;

    return result;
end);

# args: finite field, number n or coefficient list of primitive polynomial,
#       "selfdual" or "pairs" [, r]
#
# Without r the duality is f(X) -> X^d f(1/X)/f(0), i.e. on roots
# alpha -> alpha^-1.  If r is given then |F| = r^2 and the duality is the
# twisted one used for unitary groups, alpha -> alpha^-r (coefficients
# conjugated by the field automorphism of order 2).  The selfdual ones
# then have odd degree, their roots lie in the subgroup of order r^d+1.
BindGlobal("CCTAB_DualityEnumeration", function(F, input, mode, opt...)
    local q, d, tw, T, zero, one, storageQ,
          Pack, NewVector, BM,
          coeff, h, poly, x, beta, power, seed, half,
          M, a, negcoeff, support, seen, seq, result,
          t, j, v, k, r, orbitLength, negativeK,
          selfdual, pos;

    if mode <> "selfdual" and mode <> "pairs" then
        Error("mode must be \"selfdual\" or \"pairs\"");
    fi;

    if not IsField(F) or not IsFinite(F) then
        Error("F must be a finite field");
    fi;

    q := Size(F);
    if Length(opt) = 0 then
        tw := 1;
    else
        tw := opt[1];
        if tw^2 <> q then
            Error("r^2 must be the size of F");
        fi;
    fi;
    zero := Zero(F);
    one := One(F);

    # Force Is8BitVectorRep for canonical finite fields of size <= 256.
    if q <= 256 and IsFFE(one) then
      storageQ := q;
    else
      storageQ := fail;
    fi;

    Pack := function(v)
        if storageQ <> fail then
            ConvertToVectorRep(v, storageQ);
        fi;
        return v;
    end;

    NewVector := function(n)
        return Pack(ListWithIdenticalEntries(n, zero));
    end;

    # Accept either a degree or a primitive coefficient list.
    if IsInt(input) then
        if input < 1 then
            Error("the degree must be positive");
        fi;
        poly := RandomPrimitivePolynomial(F, input);
        coeff := Pack(ShallowCopy(
            CoefficientsOfUnivariatePolynomial(poly)
        ));
    elif IsList(input) then
        coeff := ShallowCopy(input);
    else
        Error("input must be a positive degree or a coefficient list");
    fi;

    if Length(coeff) < 2 then
        Error("the input polynomial must have positive degree");
    fi;

    d := Length(coeff) - 1;

    if not ForAll(coeff, c -> c in F) then
        Error("all coefficients must belong to F");
    fi;
    if coeff[d + 1] <> one then
        Error("the input polynomial must be monic");
    fi;
    if coeff[1] = zero then
        Error("a primitive polynomial has nonzero constant coefficient");
    fi;

    coeff := Pack(coeff);

    # The only selfdual linear polynomials are X-1 and X+1.
    if mode = "selfdual" and d = 1 and tw = 1 then
        result := [Pack([-one, one])];
        if -one <> one then
            Add(result, Pack([one, one]));
        fi;
        return result;
    fi;

    # A selfdual irreducible polynomial of degree > 1 has even degree.
    # (In the twisted case it has odd degree.)
    if mode = "selfdual" and (d mod 2 = 1) = (tw = 1) then
        return [];
    fi;

    # Berlekamp-Massey for a sequence of length 2*d whose minimal
    # recurrence polynomial is known to have degree exactly d.
    #
    # C stores the connection polynomial:
    # s_n + C[2]*s_(n-1) + ... + C[L+1]*s_(n-L) = 0.
    #
    # Reversing C gives the monic polynomial in ascending order.
    BM := function(s)
        local C, B, oldC, L, LB, shift, prevDelta,
              delta, factor, n, i;

        C := NewVector(d + 1);
        C[1] := one;
        B := Pack(ShallowCopy(C));

        L := 0;
        LB := 0;
        shift := 1;
        prevDelta := one;

        for n in [0 .. 2*d - 1] do
            delta := s[n + 1];
            for i in [1 .. L] do
                delta := delta + C[i + 1] * s[n - i + 1];
            od;

            if delta = zero then
                shift := shift + 1;
            else
                if 2*L <= n then
                    oldC := Pack(ShallowCopy(C));
                fi;

                factor := delta / prevDelta;
                for i in [0 .. LB] do
                    C[i + shift + 1] :=
                        C[i + shift + 1] - factor * B[i + 1];
                od;

                if 2*L <= n then
                    B := oldC;
                    LB := L;
                    L := n + 1 - L;
                    prevDelta := delta;
                    shift := 1;
                else
                    shift := shift + 1;
                fi;
            fi;
        od;

        if L <> d then
            Error("unexpected recurrence degree; check primitivity");
        fi;

        return Pack(Reversed(C));
    end;

    if mode = "selfdual" then
        # Put d = 2*m and T = q^m (untwisted), or T = r^d (twisted).
        #
        # beta = w^(T - 1) generates the subgroup of order T + 1.
        # Every degree-d selfdual root is in this subgroup.
        if tw = 1 then
            half := QuoInt(d, 2);
            T := q^half;
        else
            T := tw^d;
        fi;
        M := T + 1;

        # Obtain the minimal polynomial h of beta using arithmetic
        # modulo the input polynomial, without constructing an
        # extension field.
        poly := UnivariatePolynomial(F, coeff, 1);
        x := Indeterminate(F, 1);
        beta := PowerMod(x, T - 1, poly);

        # Project beta^j onto its constant coefficient in the w-basis.
        seed := NewVector(2*d);
        power := One(poly);

        for j in [1 .. 2*d] do
            seed[j] := Value(power, zero);
            if j < 2*d then
                power := EuclideanRemainder(power * beta, poly);
            fi;
        od;

        # beta has degree d over F.
        h := BM(seed);

    else
        # For pairs, enumerate all nonzero elements.
        M := q^d - 1;
        h := coeff;
    fi;

    # Build a period of the scalar sequence attached to h.
    #
    # If gamma is the root used above (beta or w), let lambda extract
    # the constant coefficient in 1,gamma,...,gamma^(d-1).
    #
    # a[t+1] = lambda(gamma^t).
    a := NewVector(M);
    a[1] := one;

    negcoeff := Pack(List(h{[1 .. d]}, c -> -c));
    support := Filtered([1 .. d], i -> negcoeff[i] <> zero);

    for t in [d .. M - 1] do
        v := zero;
        for j in support do
            v := v + negcoeff[j] * a[t - d + j];
        od;
        a[t + 1] := v;
    od;

    seen := BlistList([1 .. M], []);
    seq := NewVector(2*d);
    result := [];

    for k in [0 .. M - 1] do
        if not seen[k + 1] then
            r := k;
            orbitLength := 0;
            selfdual := false;
            negativeK := (-tw * k) mod M;

            repeat
                seen[r + 1] := true;
                orbitLength := orbitLength + 1;

                if mode = "pairs" then
                    # Does C(k) contain -k?
                    if r = negativeK then
                        selfdual := true;
                    fi;

                    # Also mark the dual orbit C(-tw*k).
                    seen[(-tw * r) mod M + 1] := true;
                fi;

                r := (q * r) mod M;
            until r = k;

            if orbitLength = d
               and (mode = "selfdual" or not selfdual) then

                # seq[j+1] = a_(k*j mod M).
                pos := 0;
                for j in [1 .. 2*d] do
                    seq[j] := a[pos + 1];
                    pos := pos + k;
                    if pos >= M then
                        pos := pos - M;
                    fi;
                od;

                Add(result, BM(seq));
            fi;
        fi;
    od;

    return result;
end);


##  <#GAPDoc Label="SelfDualMonicIrreducibles">
##  <ManSection>
##  <Func Name="SelfDualMonicIrreducibles" Arg="F, coeff[, r]"/>
##  <Func Name="NonSelfDualMonicIrreducibleRepresentatives" Arg="F, coeff[, r]"/>
##  <Returns>a list of coefficient lists</Returns>
##  <Description>
##  Let <A>F</A> be a finite field with <M>q</M> elements. For a monic
##  polynomial <M>f</M> of degree <M>d</M> over <A>F</A> with
##  <M>f(0) \neq 0</M> its <E>dual</E> is the monic polynomial
##  <M>f^*(X) = f(0)^{-1} X^d f(1/X)</M>, whose roots are the inverses of
##  the roots of <M>f</M>. If <M>q = r^2</M> and the optional argument
##  <A>r</A> is given then the twisted dual is used instead, this is
##  <M>f^*(X) = f^\sigma(0)^{-1} X^d f^\sigma(1/X)</M>, where
##  <M>f^\sigma</M> is obtained by applying the automorphism
##  <M>\sigma: a \mapsto a^r</M> of <A>F</A> to the coefficients of
##  <M>f</M>; the roots of <M>f^*</M> are the
##  <M>\alpha^{-r}</M> for the roots <M>\alpha</M> of <M>f</M>. These
##  dualities are used to parameterize the conjugacy classes of
##  symplectic and orthogonal groups, respectively of unitary groups.
##  <P/>
##  The arguments <A>F</A> and <A>coeff</A> are as in <Ref
##  Func="MonicIrreduciblesFromPrimitivePolynomial"/>, that is <A>coeff</A>
##  is the coefficient list of a primitive polynomial of degree <M>d</M>
##  over <A>F</A> or just the degree <M>d</M>.
##  <P/>
##  <Ref Func="SelfDualMonicIrreducibles"/> returns the list of all monic
##  irreducible polynomials <M>f</M> of degree <M>d</M> over <A>F</A> with
##  <M>f^* = f</M>. Without <A>r</A> these are <M>X-1</M>, <M>X+1</M> for
##  <M>d = 1</M>, and otherwise <M>d</M> must be even (for odd
##  <M>d &gt; 1</M> the result is empty). With <A>r</A> such polynomials
##  have odd degree <M>d</M>, their roots lie in the subgroup of order
##  <M>r^d+1</M> of the multiplicative group of the field with <M>q^d</M>
##  elements.
##  <P/>
##  <Ref Func="NonSelfDualMonicIrreducibleRepresentatives"/> returns a
##  list containing one of <M>f</M>, <M>f^*</M> for each pair of monic
##  irreducible polynomials of degree <M>d</M> over <A>F</A> with
##  <M>f^* \neq f</M> (and <M>f \neq X</M>).
##  <P/>
##  The functions use the same method as <Ref
##  Func="MonicIrreduciblesFromPrimitivePolynomial"/>; in the self-dual
##  case only a sequence of length <M>q^{(d/2)}+1</M>, respectively
##  <M>r^d+1</M>, is needed.
##
##  <Example>gap> c := CoefficientsOfUnivariatePolynomial(ConwayPolynomial(3,2));;
##  gap> List(SelfDualMonicIrreducibles(GF(3), c), 
##  >         a -> UnivariatePolynomial(GF(3), a, 1));
##  [ x_1^2+Z(3)^0 ]
##  gap> List(NonSelfDualMonicIrreducibleRepresentatives(GF(3), c), 
##  >         a -> UnivariatePolynomial(GF(3), a, 1));
##  [ x_1^2-x_1-Z(3)^0 ]
##  gap> Length(SelfDualMonicIrreducibles(GF(3), 4));
##  2
##  gap> NonSelfDualMonicIrreducibleRepresentatives(GF(5), [-Z(5), Z(5)^0]);
##  [ [ Z(5)^3, Z(5)^0 ] ]
##  gap> Set(SelfDualMonicIrreducibles(GF(4), 3, 2), List);
##  [ [ Z(2^2), 0*Z(2), 0*Z(2), Z(2)^0 ], 
##    [ Z(2^2)^2, 0*Z(2), 0*Z(2), Z(2)^0 ] ]
##  gap> Length(NonSelfDualMonicIrreducibleRepresentatives(GF(9), 2, 3));
##  18
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BindGlobal("SelfDualMonicIrreducibles",  function(F, input, r...)
    return CallFuncList(CCTAB_DualityEnumeration,
                        Concatenation([F, input, "selfdual"], r));
end);


BindGlobal("NonSelfDualMonicIrreducibleRepresentatives", function(F, input, r...)
    return CallFuncList(CCTAB_DualityEnumeration,
                        Concatenation([F, input, "pairs"], r));
end);

