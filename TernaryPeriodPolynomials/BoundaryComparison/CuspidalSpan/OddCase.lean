module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan

@[expose] public section


/-!
# `bad_plane_cuspidal_span`, odd case: reduction to two inputs

For odd `n > 0` the bad-plane Levi is `GL₂(ℤ)` (level one) and its cohomology does **not**
vanish, unlike the even case (`EvenCase.lean`). Mirroring the line-side template
(`TernaryPeriodPolynomials.Automorphic.DirectRoute.inner_bad_line_of_direct`), we isolate exactly two
mathematical inputs, named and documented below, and show that together they imply the
odd case of `bad_plane_cuspidal_span`.

## What is already unconditional

* `IdentityPlaneHecke.edgeH2 n hn hodd : CuspH2 n trivialCharacter .plane false →ₗ[ℂ]
  groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))` and its unconditional injectivity
  `IdentityPlaneHecke.edgeH2_injective`.
* `ParabolicDuality.LevelOne.parabolicH1 (arithmeticBinaryRep (n + 1) (-1))`, the classical
  parabolic subspace of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` (`mem_parabolicCocycles_iff`: a cocycle
  is parabolic iff its value at `T` is a coboundary).
* `ParabolicDualityEdgeLevelOne.edgeH2_mem_parabolicH1`: **conditionally**, if `x` is already
  known to be a joint Hecke-eigenclass (`x ∈ localJoint n trivialCharacter c .plane false`) with
  `‖c (T₂) - 1‖ ≤ 3/4` (i.e. away from the Eisenstein eigenvalue), then
  `edgeH2 n hn hodd x ∈ parabolicH1 (arithmeticBinaryRep (n+1) (-1))`. This is *not* available
  for an arbitrary `InnerBoundary` witness, which carries no a priori Hecke-eigenvalue bound.
* `EisensteinScalar.ker_betaGL_eq_range_per`: `ker (betaGL (2*r) σ) = range (per r σ)` exactly,
  so a parabolic class with vanishing `betaGL` *is* a cusp-form period class.

## The two inputs (mirrors of `DirectRoute.InnerEdgeRealized` / `PeriodsRealized`)
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **Input 1 (Eichler–Shimura, plane edge).** Every inner bad-plane class vanishing at the
good planes has a bad-plane Shapiro coordinate whose `edgeH2`-image is parabolic. This is the
plane analogue of `DirectRoute.InnerEdgeRealized`; it generalizes the unconditional-looking but
actually hypothesis-laden `ParabolicDualityEdgeLevelOne.edgeH2_mem_parabolicH1`, replacing its
"known joint Hecke-eigenclass with bounded `T₂`-eigenvalue" hypothesis with the (structurally
different, and so far not found to be formalized anywhere for the plane) `InnerBoundary`
hypothesis itself. -/
def InnerPlaneEdgeParabolic (n : ℕ) (hn : 0 < n) (hodd : Odd n) : Prop :=
  ∀ ξ : StratumH2 n trivialCharacter .plane, VanishesOnGood n trivialCharacter .plane ξ →
    InnerBoundary n trivialCharacter .plane ξ →
    edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false ξ) ∈
      parabolicH1 (arithmeticBinaryRep (n + 1) (-1))

/-- **Input 2 (cuspidal supply, plane).** Every parabolic class of `H¹(GL₂(ℤ),
Sym^{n+1} ⊗ det⁻¹)` is realized as the `edgeH2`-image of the bad-plane coordinate of some element
of `automorphicPlaneSpan n` that vanishes at the good planes. This is the plane analogue of
`DirectRoute.PeriodsRealized` ("every period class is realized by the span"). -/
def PlanePeriodParabolicRealized (n : ℕ) (hn : 0 < n) (hodd : Odd n) : Prop :=
  ∀ y ∈ parabolicH1 (arithmeticBinaryRep (n + 1) (-1)),
    ∃ b ∈ automorphicPlaneSpan n, cuspRes n trivialCharacter .plane true b = 0 ∧
      edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false b) = y

/-- **Odd case of `bad_plane_cuspidal_span`, reduced to the two inputs above.** Mirrors
`DirectRoute.inner_bad_line_of_direct`'s proof exactly: obtain the parabolic class from input 1,
realize it via input 2 as the edge-image of a span element `b`, use injectivity of `edgeH2` (which,
unlike the line side's `badLineEdge_injective`, is unconditional — no radical-kernel restriction
needed) to match bad-plane coordinates, and combine with the shared good-plane vanishing to
conclude `ξ = b` via `eq_zero_iff_cuspRes`. -/
theorem bad_plane_cuspidal_span_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hG1 : InnerPlaneEdgeParabolic n hn hodd) (hG2 : PlanePeriodParabolicRealized n hn hodd)
    (ξ : StratumH2 n trivialCharacter .plane)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hinner : InnerBoundary n trivialCharacter .plane ξ) :
    ξ ∈ automorphicPlaneSpan n := by
  have hpar := hG1 ξ hgood hinner
  obtain ⟨b, hb, hbgood, hbedge⟩ := hG2 _ hpar
  have hg : cuspRes n trivialCharacter .plane true ξ = 0 :=
    (vanishesOnGood_iff_fixedPointH2 ξ).mp hgood (cuspFlag .plane true)
      ((cuspFlag_good_iff .plane true).mpr rfl)
  have hbeq : cuspRes n trivialCharacter .plane false b =
      cuspRes n trivialCharacter .plane false ξ :=
    edgeH2_injective n hn hodd hbedge
  have hzero : ξ - b = 0 := by
    refine (eq_zero_iff_cuspRes .plane (ξ - b)).mpr ⟨?_, ?_⟩
    · rw [map_sub, hg, hbgood, sub_zero]
    · rw [map_sub, hbeq, sub_self]
  have hab : ξ = b := sub_eq_zero.mp hzero
  rw [hab]
  exact hb

end TernaryPeriodPolynomials.Argument.CuspidalSpan
