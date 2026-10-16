module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAmbientTransportOpp
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneModel

@[expose] public section


/-!
# Fact A2-opp: the good Levi element `Pg 0 (lower 1) 1` lies in `edgeParabolicSigmaLambdaOpp`

Continues `EdgeParabolicAmbientTransportOpp.lean`'s Fact A-opp (`edgeParabolic_factA_opp`, for
radical-lattice elements `Pg p.toAdd 1 1`) with the companion fact needed for the lower-leg
assembly: the *Levi* element `Pg 0 (lower 1) 1 = (goodPlaneSplitting (lower 1, 1)).val` itself also
lies in `edgeParabolicSigmaLambdaOpp`. Mirrors `EdgeParabolicLeviFactA.lean`'s Fact A2 exactly,
substituting the opposite edge `mk (gF * τ)` for `mk gF` (so the stabilizer computation uses the
`mul_assoc`/`inv_mul_cancel_left` route of Fact A-opp rather than Fact A's `inv_mul_cancel_right`)
and the membership fact `edgeParabolic_tau_conj_Pg_lower_mem`
(`EdgeParabolicSwapArithmetic.lean`) in place of Fact A2's `κ(upper 1)` vanishing argument.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (lower)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- **Fact A2-opp** (good-plane side, opposite edge): the Levi element `Pg 0 (lower 1) 1`, i.e.
`(goodPlaneSplitting (lower 1, 1)).val`, lands in `edgeParabolicSigmaLambdaOpp`. Mirrors
`edgeParabolic_factA_opp`'s stabilizer computation exactly, substituting the `edgeParabolic_tau_conj_Pg_lower_mem` for the swapped-translation membership step.
-/
theorem edgeParabolic_factA_levi_lowerOpp :
    (goodPlaneSplitting (lower 1, 1)).val ∈ edgeParabolicSigmaLambdaOpp := by
  have hsec : (goodPlaneSplitting (lower 1, 1) : ΛG).val = Pg 0 (lower 1) 1 := by
    show (secL (lower 1, 1)).val = Pg 0 (lower 1) 1
    rw [secL_apply, Gel_val]
  rw [hsec, edgeParabolic_mem_sigmaLambdaOpp]
  show gF * Pg 0 (lower 1) 1 * gF⁻¹ ∈
    fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hΛ := Pg_mem (0 : ℤ × ℤ) (lower 1) 1
    rw [mem_ΛG] at hΛ
    exact (Subgroup.mem_inf.mp hΛ).1
  · rw [MulAction.mem_stabilizer_iff]
    change (QuotientGroup.mk (gF * Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 * gF⁻¹ *
        (gF * τ)) : Edges) = QuotientGroup.mk (gF * τ)
    have hassoc : gF * Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 * gF⁻¹ * (gF * τ) =
        gF * Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 * τ := by
      rw [mul_assoc, inv_mul_cancel_left]
    rw [hassoc, QuotientGroup.eq]
    have hgoal_eq :
        (gF * Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 * τ)⁻¹ * (gF * τ) =
          (τ * Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 * τ)⁻¹ := by
      simp [mul_inv_rev, τ_inv, mul_assoc]
    rw [hgoal_eq]
    exact (parabolic .plane ⊓ parabolic .line).inv_mem edgeParabolic_tau_conj_Pg_lower_mem

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
