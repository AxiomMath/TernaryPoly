module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ContinuousCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryHilbertCocycle_contDiffOn_of_analyticAt_one {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix))) 1) :
    ContDiffOn ℝ ⊤ (fun matrix : BinaryRealMatrix => binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix)))
      {matrix : BinaryRealMatrix | matrix.det ≠ 0} := by
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  apply domain_open.contDiffOn_iff.mpr
  intro center center_invertible
  let fixed := invertibleMatrix center
  have input_regular : ContDiff ℝ ⊤ (fun matrix : BinaryRealMatrix => fixed⁻¹.val * matrix) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [Matrix.mul_apply]
    exact ContDiff.sum (fun position _ => by fun_prop)
  have center_eq : fixed⁻¹.val * center = (1 : BinaryRealMatrix) := by
    rw [← invertibleMatrix_val center center_invertible]
    change fixed⁻¹.val * fixed.val = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have at_input : ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix))) (fixed⁻¹.val * center) := by
    rw [center_eq]
    exact analytic.contDiffAt
  have local_regular := at_input.comp center input_regular.contDiffAt
  have action_regular := ((binaryHilbertOperator cusp basis fixed).restrictScalars ℝ).contDiff.contDiffAt.comp center local_regular
  have combined := (contDiffAt_const (c := binaryHilbertEmbedding cusp basis (cycle fixed))).add action_regular
  apply combined.congr_of_eventuallyEq
  filter_upwards [domain_open.mem_nhds center_invertible] with matrix matrix_invertible
  change binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix)) =
    binaryHilbertEmbedding cusp basis (cycle fixed) + binaryHilbertOperator cusp basis fixed
      (binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix (fixed⁻¹.val * matrix))))
  rw [invertibleMatrix_mul fixed⁻¹.val matrix fixed⁻¹.det_ne_zero matrix_invertible, invertibleMatrix_coe]
  have equality := binaryHilbertCocycle_identity cusp basis cycle fixed (fixed⁻¹ * invertibleMatrix matrix)
  rw [mul_inv_cancel_left] at equality
  exact equality

theorem binaryHilbertCocycle_smooth_of_analyticAt_one {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix))) 1) :
    Smooth (fun point : Fin 1 → BinaryRealGL => binaryHilbertEmbedding cusp basis (cycle (point 0))) := by
  have regular := binaryHilbertCocycle_contDiffOn_of_analyticAt_one cusp basis cycle analytic
  exact regular.comp (contDiff_apply ℝ BinaryRealMatrix (0 : Fin 1)).contDiffOn (fun _ member => member 0)

theorem binaryHilbertCocycle_continuous_of_analyticAt_one {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix))) 1) :
    Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)) :=
  realGL_continuous_of_contDiffOn (binaryHilbertCocycle_contDiffOn_of_analyticAt_one cusp basis cycle analytic)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
