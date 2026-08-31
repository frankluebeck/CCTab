###########################################################################
##  flint.tst
##
##  Tests for the FLINT based standalone programs. Each of them has a pure
##  GAP counterpart, and the package uses the standalone program if it was
##  compiled and the GAP version otherwise. Here we check that both give the
##  same answers, so these tests make sense either way (but of course they
##  only exercise the compiled programs if these were built).
##
gap> START_TEST("flint.tst");
gap> SetInfoLevel(InfoCCTable, 0);

##  Hermite normal form of some integer matrices (square and not)
gap> mats := [ [[2,1,0],[1,3,1],[0,1,2]],
>              [[1,2,3],[4,5,6],[7,8,10]],
>              [[12,-3,7,1],[5,9,-2,4],[0,6,11,-8],[3,3,3,3]],
>              [[1,2,3,4],[5,6,7,8]] ];;
gap> ForAll(mats, m -> HermiteIntMat(m) = HermiteNormalFormIntegerMat(m));
true

##  Unimodular matrices, built as products of unitriangular ones, and the
##  Gram matrices of the corresponding unimodular lattices.
gap> unimod := [
>      [[1,2],[0,1]] * [[1,0],[-3,1]],
>      [[1,2,3],[0,1,4],[0,0,1]] * [[1,0,0],[-1,1,0],[2,-3,1]],
>      [[1,-2,0,5],[0,1,3,-1],[0,0,1,2],[0,0,0,1]]
>        * [[1,0,0,0],[4,1,0,0],[-2,3,1,0],[0,1,-5,1]] ];;
gap> List(unimod, DeterminantMat);
[ 1, 1, 1 ]
gap> grams := List(unimod, u -> u * TransposedMat(u));;
gap> List(grams, DeterminantMat);
[ 1, 1, 1 ]

##  inverse of a unimodular matrix
gap> ForAll(unimod, m -> InverseUnimodularMat(m) = m^-1);
true
gap> ForAll(unimod, m -> InverseUnimodularMat(m) = InverseUnimodularMat_GAP(m));
true

##  fraction free Gauss elimination for symmetric positive definite matrices
gap> ForAll(grams, m -> m = TransposedMat(m));
true
gap> ForAll(grams, m -> PermutedFractionFreeIntegerGaussPositiveDefinite(m)
>            = PermutedFractionFreeIntegerGaussPositiveDefinite_GAP(m));
true

##  LLL transformation of a unimodular Gram matrix: the pure GAP and the
##  FLINT version need not return the same basis, so we check the defining
##  property 'H gr H^t = identity' instead
gap> CheckLLLTransform := function(gr, f)
>      local H;
>      H := f(gr);
>      if not ForAll(H, r -> ForAll(r, IsInt)) then
>        return "not an integer matrix";
>      fi;
>      if H * gr * TransposedMat(H) <> IdentityMat(Length(gr)) then
>        return "does not transform the Gram matrix to the identity";
>      fi;
>      return true;
>    end;;
gap> List(grams, gr -> CheckLLLTransform(gr, LLLTransformUnimodularGram));
[ true, true, true ]
gap> List(grams, gr -> CheckLLLTransform(gr, LLLTransformUnimodularGram_GAP));
[ true, true, true ]

##  The matrices above are too small to make the standalone programs
##  distribute any work over several threads. The following one is big
##  enough; it used to trigger a race condition in 'parallel_do_dyn' which
##  made 'pffgintmat_threads' return wrong results and 'lll_modular_threads'
##  hang, so please keep a test of this size around.
gap> n := 16;;
gap> big := IdentityMat(n);;
gap> for i in [1..n] do
>      for j in [i+1..n] do big[i][j] := ((i*j) mod 7) - 3; od;
>    od;
gap> low := IdentityMat(n);;
gap> for i in [1..n] do
>      for j in [1..i-1] do low[i][j] := ((i+2*j) mod 5) - 2; od;
>    od;
gap> big := big * low;;
gap> DeterminantMat(big);
1
gap> biggram := big * TransposedMat(big);;
gap> HermiteIntMat(big) = HermiteNormalFormIntegerMat(big);
true
gap> InverseUnimodularMat(big) = big^-1;
true
gap> PermutedFractionFreeIntegerGaussPositiveDefinite(biggram)
>      = PermutedFractionFreeIntegerGaussPositiveDefinite_GAP(biggram);
true
gap> CheckLLLTransform(biggram, LLLTransformUnimodularGram);
true

##
gap> STOP_TEST("flint.tst");
