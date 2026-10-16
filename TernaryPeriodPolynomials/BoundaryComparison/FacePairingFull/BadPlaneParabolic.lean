module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Shapiro
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.InnerPlaneEdgeParabolicProof
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneSupply
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.GoodFlagTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# The locally inner classes at the identity plane

For odd `n > 0` the binary edge `H²(Λ₀, Sym^n) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` restricts to a linear
isomorphism from the locally inner classes at the identity plane onto the parabolic classes
(`badPlaneLocallyInnerEquivParabolic`): inner classes have parabolic edge
(`CuspidalSpan.innerPlaneEdgeParabolic_proof`), every parabolic class is the edge of a seed in the
automorphic plane span vanishing at the good plane (`CuspidalSpan.cuspFormRealized`), and the edge is
injective. For even `n > 0` the local cohomology at the identity plane is zero
(`badPlane_locallyInner_eq_bot_of_even`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke (edgeH2)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.GoodPlaneSpan
open TernaryPeriodPolynomials.Argument.CuspidalSpan

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- A locally inner class at the identity plane is the bad coordinate of an inner class vanishing at
the good plane. -/
theorem exists_inner_of_locallyInner_badPlane (n : ℕ)
    (x : CuspH2 n trivialCharacter .plane false)
    (hx : x ∈ locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :
    ∃ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ ∧
      cuspRes n trivialCharacter .plane true ξ = 0 ∧
      cuspRes n trivialCharacter .plane false ξ = x := by
  obtain ⟨b, hb⟩ := innerToLocal_surjective n (cuspFlag .plane true) (cuspFlag .plane false)
    ((cuspFlag_good_iff .plane true).mpr rfl)
    (fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)) (0, ⟨x, hx⟩)
  exact ⟨b.val, b.property, congrArg (fun p => p.1.val) hb, congrArg (fun p => p.2.val) hb⟩

/-- For even `n` there are no locally inner classes at the identity plane. -/
theorem badPlane_locallyInner_eq_bot_of_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x _
  exact TernaryPeriodPolynomials.Spectral.IdentityPlaneEven.cuspH2_identityPlane_eq_zero
    n hn heven x

variable (n : ℕ) (hn : 0 < n) (hodd : Odd n)

/-- The identity-plane edge on locally inner classes, with values in the parabolic classes. -/
def badPlaneInnerEdge :
    locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false) →ₗ[ℂ]
      parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  ((edgeH2 n hn hodd).comp (locallyInnerClasses n trivialCharacter .plane
    (cuspFlag .plane false)).subtype).codRestrict _ (by
    intro x
    obtain ⟨ξ, hξ, hξg, hξx⟩ := exists_inner_of_locallyInner_badPlane n x.val x.property
    change edgeH2 n hn hodd x.val ∈ _
    rw [← hξx]
    exact innerPlaneEdgeParabolic_proof hn hodd ξ
      (vanishesOnGood_of_cuspRes_good_eq_zero ξ hξg) hξ)

theorem badPlaneInnerEdge_bijective : Function.Bijective (badPlaneInnerEdge n hn hodd) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke.edgeH2_injective n hn hodd
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨b, hb, -, hbedge⟩ :=
      parabolicPeriodRealized_of_cuspFormRealized n hn hodd (cuspFormRealized n hn hodd) y hy
    have hinner := automorphicPlaneSpan_subset_innerBoundary hb
    refine ⟨⟨cuspRes n trivialCharacter .plane false b, ?_⟩, Subtype.ext hbedge⟩
    exact innerBoundary_fixedPointH2_locallyInner hinner (cuspFlag .plane false)

/-- **Identity plane (odd `n`): locally inner classes `≅` parabolic `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`.** -/
def badPlaneLocallyInnerEquivParabolic :
    locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false) ≃ₗ[ℂ]
      parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  LinearEquiv.ofBijective (badPlaneInnerEdge n hn hodd) (badPlaneInnerEdge_bijective n hn hodd)

end TernaryPeriodPolynomials.Argument.FacePairingFull
