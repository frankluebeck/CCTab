##  Costs:
##  Step 	                           Cost
##  Scalar recurrence table            O(Nh) operations in FF
##  Cyclotomic coset enumeration       O(N) modular-index operations
##  Berlekamp–Massey for all answers   O(Rd2) operations in FF
##  Storage, including output          O(N) field-element slots, plus a bitlist
# args: finite field, number n or coefficient list of primitive polynomial
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
#       "selfdual" or "pairs"
BindGlobal("CCTAB_DualityEnumeration", function(F, input, mode)
    local q, d, zero, one, storageQ,
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
    if mode = "selfdual" and d = 1 then
        result := [Pack([-one, one])];
        if -one <> one then
            Add(result, Pack([one, one]));
        fi;
        return result;
    fi;

    # A selfdual irreducible polynomial of degree > 1 has even degree.
    if mode = "selfdual" and d mod 2 = 1 then
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
        # Put d = 2*m.
        #
        # beta = w^(q^m - 1) generates the subgroup of order q^m + 1.
        # Every degree-d selfdual root is in this subgroup.
        half := QuoInt(d, 2);
        M := q^half + 1;

        # Obtain the minimal polynomial h of beta using arithmetic
        # modulo the input polynomial, without constructing an
        # extension field.
        poly := UnivariatePolynomial(F, coeff, 1);
        x := Indeterminate(F, 1);
        beta := PowerMod(x, q^half - 1, poly);

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
            negativeK := (M - k) mod M;

            repeat
                seen[r + 1] := true;
                orbitLength := orbitLength + 1;

                if mode = "pairs" then
                    # Does C(k) contain -k?
                    if r = negativeK then
                        selfdual := true;
                    fi;

                    # Also mark the dual orbit C(-k).
                    if r = 0 then
                        seen[1] := true;
                    else
                        seen[M - r + 1] := true;
                    fi;
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


BindGlobal("SelfDualMonicIrreducibles",  function(F, input)
    return CCTAB_DualityEnumeration(F, input, "selfdual");
end);


BindGlobal("NonSelfDualMonicIrreducibleRepresentatives", function(F, input)
    return CCTAB_DualityEnumeration(F, input, "pairs");
end);

