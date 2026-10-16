module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.GoodFlagTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.TwoGenerator
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ParabolicBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators

@[expose] public section


/-!
# `good_plane_cuspidal_span`: reduction to two inputs

Target: `TernaryPeriodPolynomials/BoundaryComparison/GoodPlaneSpan/Span.lean`,
`good_plane_cuspidal_span (n hn ξ hinner) : ∃ ξ' ∈ automorphicPlaneSpan n, VanishesOnGood n
trivialCharacter .plane (ξ - ξ')`. This is the good-plane spanning clause of Lemma C.3: the
good-plane Levi is `Γ₁'(3)` (level three), so Eichler–Shimura here is the level-three statement
`levelPeriodMap_range_eq_parabolic_of_injective` (`AxiomCodeLevelThree/LevelThreePeriodDimension.lean`),
already proved unconditionally in the existing library together with the injectivity
`goodPlaneEdge_injective` (`AxiomCodeLevelThree/GoodPlaneEdge3.lean`). What is **not** already
in the library is (1) that the edge of an *inner* class actually lands in the parabolic subspace,
and (2) that every parabolic class is realized by an actual element of `automorphicPlaneSpan n`
(the "cuspidal supply" step, matching the paper's own cuspidal data to abstract level-three
cusp forms).

## Why `VanishesOnGood` of the *difference* is not an extra difficulty

Unlike every sibling precedent (the line target, and both cases of the bad-plane analogue
`bad_plane_cuspidal_span`), this target takes **no** `VanishesOnGood` hypothesis at all and must
instead *produce* `VanishesOnGood n trivialCharacter .plane (ξ - ξ')` for an existentially chosen
`ξ'`. This looked, before `GoodFlagTransport.lean`, like it might need genuinely new
multi-cusp-coherence machinery (`VanishesOnGood` quantifies over *every* good flag, not just one
reference cusp). It does not: `GoodFlagTransport.vanishesOnGood_of_cuspRes_good_eq_zero` shows,
generically in `side`, that vanishing of the Shapiro coordinate at the single reference good flag
already *implies* `VanishesOnGood` (every good flag is a `rationalLevel`-translate of the
reference one, and `fixedPointH2` transports linearly along that translation). So the two inputs below only ever need to produce a match at the single reference good coordinate
`cuspRes n trivialCharacter .plane true`, exactly like every sibling precedent.

## The two inputs

* `GoodPlaneEdgeParabolic`: the good-plane edge (`goodPlaneEdge`, built from the Hochschild–Serre
  edge map of `1 → ℤ² → Λ → Γ₁'(3) × ℤˣ → 1`) of the *good* Shapiro coordinate of an inner class is
  parabolic for `Γ₁'(3)` acting on `Sym^{n+1} ⊗ det⁻¹`.
* `GoodPlanePeriodsRealized`: every class of `parabolicH1 (levelRep (n+1) (-1)) (upper 1) (lower 1)`
  is realized as the good-edge image of the good Shapiro coordinate of an actual element of
  `automorphicPlaneSpan n`. By `levelPeriodMap_range_eq_parabolic_of_injective` together with
  `levelPeriodMap_injective_goodPlane` (`AxiomCodeLevelThreeInjective/Main.lean`), every such class
  already equals `levelPeriodMap (n+1) (-1) f` for a unique level-three cusp form `f`; what is
  missing is exhibiting `f`'s seed concretely as a `CohomologicalCuspData`/`boundarySummand` element of
  `automorphicPlaneSpan n` with matching edge image — the actual cuspidal-supply construction.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds

/-- **Input 1 (Eichler–Shimura, good-plane edge).** The good-plane edge of the good Shapiro
coordinate of an inner class is parabolic. -/
def GoodPlaneEdgeParabolic (n : ℕ) (hn : 0 < n) : Prop :=
  ∀ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ →
    goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ) ∈
      parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1)

/-- **Input 2 (cuspidal supply, good plane).** Every parabolic class is realized as the
good-plane edge image of the good Shapiro coordinate of an element of `automorphicPlaneSpan n`. -/
def GoodPlanePeriodsRealized (n : ℕ) (hn : 0 < n) : Prop :=
  ∀ y ∈ parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1),
    ∃ ξ' ∈ automorphicPlaneSpan n,
      goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ') = y

/-- **`good_plane_cuspidal_span`, reduced to the two inputs above.** Obtain the parabolic
class of the given inner `ξ` from input 1, realize it via input 2 as the good-edge image of a span
element `ξ'`, use injectivity of `goodPlaneEdge` to see the good coordinate of `ξ - ξ'` vanishes,
and conclude `VanishesOnGood` of the difference by `GoodFlagTransport`'s generic single-flag
bridge. -/
theorem good_plane_cuspidal_span_of_inputs (n : ℕ) (hn : 0 < n)
    (hG1 : GoodPlaneEdgeParabolic n hn) (hG2 : GoodPlanePeriodsRealized n hn)
    (ξ : StratumH2 n trivialCharacter .plane)
    (hinner : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ ξ' ∈ automorphicPlaneSpan n, VanishesOnGood n trivialCharacter .plane (ξ - ξ') := by
  have hpar := hG1 ξ hinner
  obtain ⟨ξ', hξ', hedge⟩ := hG2 _ hpar
  have hsub : cuspRes n trivialCharacter .plane true (ξ - ξ') =
      cuspRes n trivialCharacter .plane true ξ - cuspRes n trivialCharacter .plane true ξ' :=
    map_sub _ ξ ξ'
  have hdiff : goodPlaneEdge hn (cuspRes n trivialCharacter .plane true (ξ - ξ')) = 0 := by
    rw [hsub, map_sub, hedge, sub_self]
  have h0 : goodPlaneEdge hn (0 : CuspH2 n trivialCharacter .plane true) = 0 := map_zero _
  have hzero : cuspRes n trivialCharacter .plane true (ξ - ξ') = 0 :=
    goodPlaneEdge_injective hn (hdiff.trans h0.symm)
  exact ⟨ξ', hξ', vanishesOnGood_of_cuspRes_good_eq_zero _ hzero⟩

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
