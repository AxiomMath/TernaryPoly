module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Shapiro
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.PlaneSupply
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjGoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ExactLevel
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner

@[expose] public section


/-!
# The locally inner classes at the good plane are the parabolic `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`

For `n > 0`, at the good reference plane `cuspFlag .plane true` the good-plane edge map
`goodPlaneEdge : H²(Γ_F, Sym^n) → H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` restricts to a linear isomorphism from
the locally inner classes onto the parabolic classes (`goodPlaneLocallyInnerEquivParabolic`):
* inner classes have parabolic edge (`GoodPlaneSpan.goodPlaneEdgeParabolic`, every inner class has a
  locally inner good coordinate and every locally inner class is such a coordinate by Shapiro
  realization);
* every parabolic class is the edge of the good coordinate of an element of the automorphic plane span,
  which is inner (`GoodPlaneSpan.goodPlanePeriodsRealized`);
* the edge map is injective.
Consequently the exact dimension is `⌊(n+3)/3⌋ - 1`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.TwoGenerator (parabolicH1)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3 (goodPlaneEdge)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.GoodPlaneSpan
open TernaryPeriodPolynomials.Argument.CuspidalSpan

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- A locally inner class at the good reference plane is the good coordinate of an inner class. -/
theorem exists_inner_of_locallyInner_goodPlane (n : ℕ)
    (x : CuspH2 n trivialCharacter .plane true)
    (hx : x ∈ locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) :
    ∃ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ ∧
      cuspRes n trivialCharacter .plane true ξ = x := by
  obtain ⟨b, hb⟩ := innerToLocal_surjective n (cuspFlag .plane true) (cuspFlag .plane false)
    ((cuspFlag_good_iff .plane true).mpr rfl)
    (fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)) (⟨x, hx⟩, 0)
  exact ⟨b.val, b.property, congrArg (fun p => p.1.val) hb⟩

/-- The good-plane edge restricted to the locally inner classes, with values in the parabolic classes. -/
def goodPlaneInnerEdge (n : ℕ) (hn : 0 < n) :
    locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true) →ₗ[ℂ]
      parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1) :=
  ((goodPlaneEdge hn).comp (locallyInnerClasses n trivialCharacter .plane
    (cuspFlag .plane true)).subtype).codRestrict _ (by
    intro x
    obtain ⟨ξ, hξ, hξx⟩ := exists_inner_of_locallyInner_goodPlane n x.val x.property
    change goodPlaneEdge hn x.val ∈ _
    rw [← hξx]
    exact goodPlaneEdgeParabolic n hn ξ hξ)

theorem goodPlaneInnerEdge_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (goodPlaneInnerEdge n hn) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3.goodPlaneEdge_injective hn
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨ξ', hξ', hedge⟩ := goodPlanePeriodsRealized n hn y hy
    have hinner := automorphicPlaneSpan_subset_innerBoundary hξ'
    refine ⟨⟨cuspRes n trivialCharacter .plane true ξ', ?_⟩, Subtype.ext hedge⟩
    exact innerBoundary_fixedPointH2_locallyInner hinner (cuspFlag .plane true)

/-- **Good plane: locally inner classes `≅` parabolic `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`.** -/
def goodPlaneLocallyInnerEquivParabolic (n : ℕ) (hn : 0 < n) :
    locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true) ≃ₗ[ℂ]
      parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1) :=
  LinearEquiv.ofBijective (goodPlaneInnerEdge n hn) (goodPlaneInnerEdge_bijective n hn)

/-- **Exact dimension at the good plane:** `dim + 1 = ⌊(n + 3)/3⌋`. -/
theorem finrank_goodPlane_locallyInner (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) + 1 =
      (n + 3) / 3 := by
  rw [(goodPlaneLocallyInnerEquivParabolic n hn).finrank_eq]
  have h := TernaryPeriodPolynomials.LevelThree.ExactLevel.finrank_level_parabolicH1_eq
    (m := n + 1) (e := -1) (by omega)
  have e : (n + 1 + 2) / 3 = (n + 3) / 3 := by omega
  rw [e] at h
  exact h

end TernaryPeriodPolynomials.Argument.FacePairingFull
