module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.CongruenceFactorization
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A reflection carrying the bottom row to the last coordinate gives the real plane Iwasawa decomposition. -/
theorem realGL_parabolic_compact_factorization (matrix : RealGL3) :
    ∃ (parabolic : planeParabolic ℝ) (compact : RealGL3),
      compact.val.transpose * compact.val = 1 ∧ matrix = parabolic.val * compact := by
  let normal : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun column => matrix.val 2 column)
  let target : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 ‖normal‖
  have norms : ‖normal‖ = ‖target‖ := by
    dsimp only [target]
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  let reflection := (ℝ ∙ (normal - target))ᗮ.reflection
  have reflects : reflection normal = target := Submodule.reflection_sub norms
  let basis := EuclideanSpace.basisFun (Fin 3) ℝ
  let entries := LinearMap.toMatrix basis.toBasis basis.toBasis reflection.toLinearEquiv.toLinearMap
  have unitary : entries ∈ Matrix.unitaryGroup (Fin 3) ℝ :=
    reflection.toMatrix_mem_unitaryGroup basis basis
  have right_inverse : entries * entries.transpose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff.mp unitary
  have left_inverse : entries.transpose * entries = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff'.mp unitary
  let compact : RealGL3 := ⟨entries, entries.transpose, right_inverse, left_inverse⟩
  have action : entries *ᵥ normal.ofLp = target.ofLp := by
    have equality := LinearMap.toMatrix_mulVec_repr basis.toBasis basis.toBasis
      reflection.toLinearEquiv.toLinearMap normal
    have coordinates (vector : EuclideanSpace ℝ (Fin 3)) :
        (fun index => basis.toBasis.repr vector index) = vector.ofLp := by
      funext index
      exact (OrthonormalBasis.coe_toBasis_repr_apply basis vector index).trans
        (EuclideanSpace.basisFun_repr (Fin 3) ℝ vector index)
    change entries *ᵥ (fun index => basis.toBasis.repr normal index) =
      (fun index => basis.toBasis.repr (reflection normal) index) at equality
    rw [coordinates, coordinates, reflects] at equality
    exact equality
  have parabolic_member : matrix * compact⁻¹ ∈ planeParabolic ℝ := by
    have vanishing (index : Fin 2) : (matrix * compact⁻¹).val 2 index.castSucc = 0 := by
      have equality := congrFun action index.castSucc
      have distinct : index.castSucc ≠ (2 : Fin 3) := by fin_cases index <;> decide
      change (∑ position, matrix.val 2 position * entries index.castSucc position) = 0
      simpa only [Matrix.mulVec, dotProduct, normal, WithLp.ofLp_toLp,
        target, PiLp.single_apply, ite_eq_right distinct, mul_comm] using equality
    exact ⟨vanishing 0, vanishing 1⟩
  refine ⟨⟨matrix * compact⁻¹, parabolic_member⟩, compact, left_inverse, ?_⟩
  change matrix = matrix * compact⁻¹ * compact
  rw [inv_mul_cancel_right]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
