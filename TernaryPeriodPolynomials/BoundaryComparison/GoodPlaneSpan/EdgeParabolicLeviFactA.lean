module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAmbientTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneModel

@[expose] public section


/-!
# Fact A2: the good Levi element `Pg 0 (upper 1) 1` lies in `edgeParabolicSigmaLambda`

Continues `EdgeParabolicAmbientTransport.lean`'s Fact A (`edgeParabolic_factA`, for radical-lattice
elements `Pg p.toAdd 1 1`) with the companion fact needed for the final assembly step: the
*Levi* element `Pg 0 (upper 1) 1 = (goodPlaneSplitting (upper 1, 1)).val` itself also lies in
`edgeParabolicSigmaLambda`. The only extra ingredient, versus Fact A, is that `κ(upper 1)`'s
`(1,0)` entry vanishes (so `Pg b (upper 1) 1 ∈ parabolic .line`, exactly as it does for `κ(1) = 1`
in `edgeParabolic_Pg_one_mem_lineParabolic`); the rest of the argument is identical to
`edgeParabolic_factA`'s stabilizer computation.

`upper (parameter : ℤ) : binaryArithmeticLevel` has underlying integer matrix
`!![1, parameter; 0, 1]` (`ArithmeticGenerators.upper`), so its `(1,0)` entry is `0` for every
parameter; `kapMat`'s `(1,0)` entry is that same entry divided by `3`, hence also `0`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- The `(1,0)` entry of `κ(upper 1) = kapMat (upper 1)` vanishes: `upper 1`'s own `(1,0)` entry
is `0`, and `kapMat`'s `(1,0)` entry is that divided by `3`. -/
theorem edgeParabolic_kapMat_upper_zero :
    (kapMat (upper 1 : binaryArithmeticLevel).val.val) 1 0 = 0 := by
  show ((upper (1 : ℤ)).val.val 1 0) / 3 = 0
  simp [upper]

/-- The `(1,0)` entry of `κ(upper 1)` in `GL₂(ℚ)` also vanishes. -/
theorem edgeParabolic_kap_upper_val :
    ((integralEmbed (kap (upper 1)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
  rw [integralEmbed_kap_val, Matrix.map_apply, edgeParabolic_kapMat_upper_zero]
  norm_num

/-- `Pg b (upper 1) 1` lies in `parabolic .line` for every `b`: its `(1,0)` entry is
`(integralEmbed (kap (upper 1))).val 1 0 = 0` by `edgeParabolic_kap_upper_val`, and its `(2,0)`
entry vanishes unconditionally by `P_val`'s shape. -/
theorem edgeParabolic_Pg_upper_mem_lineParabolic (b : ℤ × ℤ) :
    Pg b (upper 1) 1 ∈ parabolic .line := by
  show InLineParabolic (Pg b (upper 1) 1)
  unfold InLineParabolic
  rw [Pg, P_val]
  simp [edgeParabolic_kap_upper_val]

/-- **Fact A2** (good-plane side): the Levi element `Pg 0 (upper 1) 1`, i.e.
`(goodPlaneSplitting (upper 1, 1)).val`, lands in `edgeParabolicSigmaLambda`. Mirrors
`edgeParabolic_factA`'s stabilizer computation exactly, substituting
`edgeParabolic_Pg_upper_mem_lineParabolic` for `edgeParabolic_Pg_one_mem_lineParabolic`. -/
theorem edgeParabolic_factA_levi_upper :
    (goodPlaneSplitting (upper 1, 1)).val ∈ edgeParabolicSigmaLambda := by
  have hsec : (goodPlaneSplitting (upper 1, 1) : ΛG).val = Pg 0 (upper 1) 1 := by
    show (secL (upper 1, 1)).val = Pg 0 (upper 1) 1
    rw [secL_apply, Gel_val]
  rw [hsec, edgeParabolic_mem_sigmaLambda]
  show gF * Pg 0 (upper 1) 1 * gF⁻¹ ∈ fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hΛ := Pg_mem (0 : ℤ × ℤ) (upper 1) 1
    rw [mem_ΛG] at hΛ
    exact (Subgroup.mem_inf.mp hΛ).1
  · rw [MulAction.mem_stabilizer_iff]
    change (QuotientGroup.mk (gF * Pg 0 (upper 1) 1 * gF⁻¹ * gF) : Edges) = QuotientGroup.mk gF
    rw [inv_mul_cancel_right, QuotientGroup.eq]
    have hmem : Pg 0 (upper 1) 1 ∈ parabolic .plane ⊓ parabolic .line :=
      Subgroup.mem_inf.mpr
        ⟨Pg_parabolic 0 (upper 1) 1, edgeParabolic_Pg_upper_mem_lineParabolic 0⟩
    have hinv := (parabolic .plane ⊓ parabolic .line).inv_mem hmem
    simpa [mul_assoc] using hinv

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
