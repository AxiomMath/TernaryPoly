module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicSwapArithmetic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneConj
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore

@[expose] public section


/-!
# Transporting the opposite-edge `Σ`-primitive into `ΛG` coordinates (step 2b, opposite edge)

Mirrors `EdgeParabolicAmbientTransport.lean`, replacing the base edge `mk gF` by the opposite edge
`mk (gF * τ)` (`EdgeParabolicSwapOpp.lean`). Conjugation is still by `gF` alone (not `gF * τ`): the
target subgroup `edgeParabolicSigmaLambdaOpp` is the `gF`-conjugate copy of
`Σopp := fixedPointLevel rationalLevel (mk (gF * τ) : Edges)`, exactly as `edgeParabolicSigmaLambda`
is the `gF`-conjugate copy of `Σ := fixedPointLevel rationalLevel (mk gF : Edges)`. This redoes the upper-leg transport machinery with the base edge replaced
by the edge attached to the opposite frame, while keeping every edge/Σ-independent lemma
(`edgeParabolic_Cambient`, `edgeParabolic_psiG_classOf`, `edgeParabolic_radicalU`,
`edgeParabolic_radicalU_mem`, all in `EdgeParabolicRelativeCycle.lean`) unchanged.

**Fact A-opp**'s stabilizer computation differs from Fact A's: both sides of the relevant
`QuotientGroup.eq` are `mk (gF * τ)` rather than `mk gF`, so the trailing `* gF` cannot cancel
directly via `inv_mul_cancel_right`. Instead `gF * X * gF⁻¹ * (gF * τ) = gF * X * τ`
(`mul_assoc` + `inv_mul_cancel_left`), and membership reduces to
`(τ * X * τ)⁻¹ ∈ parabolic .plane ⊓ parabolic .line`, i.e. to the swapped-translation membership
fact `edgeParabolic_tau_conj_Pg_one` from `EdgeParabolicSwapArithmetic.lean`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- The `gF`-conjugate copy of `Σopp := fixedPointLevel rationalLevel (mk (gF * τ) : Edges)`. -/
def edgeParabolicSigmaLambdaOpp : Subgroup RationalGL3 :=
  (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges)).comap
    (MulAut.conj gF).toMonoidHom

theorem edgeParabolic_mem_sigmaLambdaOpp (h : RationalGL3) :
    h ∈ edgeParabolicSigmaLambdaOpp ↔
      gF * h * gF⁻¹ ∈ fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges) :=
  Iff.rfl

theorem edgeParabolic_sigma_conjOpp :
    ∀ h ∈ edgeParabolicSigmaLambdaOpp,
      gF * h * gF⁻¹ ∈ fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges) :=
  fun _ hh => (edgeParabolic_mem_sigmaLambdaOpp _).mp hh

/-- **Fact A-opp** (good-plane side, opposite edge): every radical-lattice generator's image under
`goodPlaneExtension.inl` lands in `edgeParabolicSigmaLambdaOpp`. -/
theorem edgeParabolic_factA_opp (p : RadicalLattice) :
    (goodPlaneExtension.inl p).val ∈ edgeParabolicSigmaLambdaOpp := by
  have hinl : (goodPlaneExtension.inl p : ΛG) = radInc p := rfl
  rw [hinl, radInc_eq]
  rw [edgeParabolic_mem_sigmaLambdaOpp]
  show gF * Pg p.toAdd 1 1 * gF⁻¹ ∈
    fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hΛ := Pg_mem p.toAdd 1 1
    rw [mem_ΛG] at hΛ
    exact (Subgroup.mem_inf.mp hΛ).1
  · rw [MulAction.mem_stabilizer_iff]
    change (QuotientGroup.mk (gF * Pg p.toAdd 1 1 * gF⁻¹ * (gF * τ)) : Edges) =
      QuotientGroup.mk (gF * τ)
    have hassoc : gF * Pg p.toAdd 1 1 * gF⁻¹ * (gF * τ) = gF * Pg p.toAdd 1 1 * τ := by
      rw [mul_assoc, inv_mul_cancel_left]
    rw [hassoc, QuotientGroup.eq]
    have hmem : τ * Pg p.toAdd 1 1 * τ ∈ parabolic .plane ⊓ parabolic .line := by
      rw [edgeParabolic_tau_conj_Pg_one]
      exact Subgroup.mem_inf.mpr
        ⟨Pg_parabolic (p.toAdd.2, p.toAdd.1) 1 1,
          edgeParabolic_Pg_one_mem_lineParabolic (p.toAdd.2, p.toAdd.1)⟩
    have hgoal_eq :
        (gF * Pg p.toAdd 1 1 * τ)⁻¹ * (gF * τ) = (τ * Pg p.toAdd 1 1 * τ)⁻¹ := by
      simp [mul_inv_rev, τ_inv, mul_assoc]
    rw [hgoal_eq]
    exact (parabolic .plane ⊓ parabolic .line).inv_mem hmem

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
