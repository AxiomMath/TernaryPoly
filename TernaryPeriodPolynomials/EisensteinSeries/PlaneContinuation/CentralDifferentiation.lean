module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MatrixRotationSpan
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CohomologicalCenter

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalCenter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CentralDifferentiation

theorem invertibleMatrix_scalar (scalar : ℝ) (nonzero : scalar ≠ 0) :
    invertibleMatrix (scalar • (1 : BinaryMatrix)) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 scalar nonzero) := by
  have equality : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 scalar nonzero)).val =
      scalar • (1 : BinaryMatrix) := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.GeneralLinearGroup.coe_scalar]
  rw [← equality, invertibleMatrix_units]

theorem fderiv_identity_zero {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : BinaryMatrix → Target) (differentiability : DifferentiableAt ℝ function 1)
    (scaling : ∀ scalar : ℝ, 0 < scalar → function (scalar • (1 : BinaryMatrix)) = function 1) :
    fderiv ℝ function 1 (1 : BinaryMatrix) = 0 := by
  have curveDerivative : HasDerivAt (fun scalar : ℝ => scalar • (1 : BinaryMatrix)) (1 : BinaryMatrix) 1 := by
    have derivative := (hasDerivAt_id (1 : ℝ)).smul_const (1 : BinaryMatrix)
    rw [one_smul] at derivative
    exact derivative
  have derivative := differentiability.hasFDerivAt.comp_hasDerivAt_of_eq 1 curveDerivative (one_smul ℝ _).symm
  have germ : (function ∘ (fun scalar : ℝ => scalar • (1 : BinaryMatrix))) =ᶠ[nhds (1 : ℝ)]
      (fun _ => function 1) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with scalar positive
    exact scaling scalar positive
  exact derivative.unique ((hasDerivAt_const (1 : ℝ) (function 1)).congr_of_eventuallyEq germ)

theorem realOrbit_scaling {degree : ℕ} (data : InducingData degree) (vector : data.cusp.H)
    (scalar : ℝ) (positive : 0 < scalar) : realOrbit data.cusp vector (scalar • (1 : BinaryMatrix)) = vector := by
  rw [realOrbit, invertibleMatrix_scalar scalar (ne_of_gt positive)]
  exact positiveReal_scalar_fixed data _ positive vector

theorem directionalOperator_identity {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) :
    directionalOperator data.cusp (1 : BinaryMatrix) vector = 0 := by
  apply Subtype.ext
  change fderiv ℝ (realOrbit data.cusp vector.val) 1 (1 : BinaryMatrix) = 0
  apply fderiv_identity_zero _ ((smooth_orbit_contDiffAt_one data.cusp vector).differentiableAt (by simp))
  intro scalar positive
  change realOrbit data.cusp vector.val (scalar • (1 : BinaryMatrix)) = realOrbit data.cusp vector.val 1
  have atOne := realOrbit_scaling data vector.val 1 (by norm_num)
  rw [one_smul] at atOne
  exact (realOrbit_scaling data vector.val scalar positive).trans atOne.symm

theorem scalarMatrixOrbit_scaling {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (scalar : ℝ) (positive : 0 < scalar) :
    scalarMatrixOrbit data.cusp point vector (scalar • (1 : BinaryMatrix)) = data.cusp.realize vector point := by
  rw [scalarMatrixOrbit, invertibleMatrix_scalar scalar (ne_of_gt positive),
    ← smoothTranslate_realize]
  have equality : smoothTranslate data.cusp
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 scalar (ne_of_gt positive))) vector = vector :=
    Subtype.ext (positiveReal_scalar_fixed data _ positive vector.val)
  rw [equality]

theorem scalarDirectional_identity {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) : scalarDirectional data.cusp point vector (1 : BinaryMatrix) = 0 := by
  have membership : (1 : BinaryMatrix) ∈ binaryDomain := by simp [binaryDomain]
  apply fderiv_identity_zero _
    ((((scalarMatrixOrbit_contDiffOn data.cusp point vector) 1 membership).contDiffAt
      (binaryDomain_isOpen.mem_nhds membership)).differentiableAt (by simp))
  intro scalar positive
  have atOne := scalarMatrixOrbit_scaling data point vector 1 (by norm_num)
  rw [one_smul] at atOne
  exact (scalarMatrixOrbit_scaling data point vector scalar positive).trans atOne.symm

/-- Realization commutes with differentiation in every real binary matrix direction. -/
theorem scalarDirectional_eq_realized {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (direction : BinaryMatrix) :
    scalarDirectional data.cusp point vector direction = realizedDirectional data.cusp point vector direction := by
  have equality : (scalarDirectional data.cusp point vector).toLinearMap =
      realizedDirectional data.cusp point vector := by
    apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixRotationSpan.linearMap_ext
    · change scalarDirectional data.cusp point vector 1 =
        data.cusp.realize (directionalOperator data.cusp 1 vector) point
      rw [scalarDirectional_identity, directionalOperator_identity, map_zero, Pi.zero_apply]
    · exact scalarDirectional_generator data.cusp point vector
    · exact scalarDirectional_conjugateGenerator data.cusp point vector _
    · exact scalarDirectional_conjugateGenerator data.cusp point vector _
  exact congrArg (fun linear : BinaryMatrix →ₗ[ℝ] ℂ => linear direction) equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CentralDifferentiation
