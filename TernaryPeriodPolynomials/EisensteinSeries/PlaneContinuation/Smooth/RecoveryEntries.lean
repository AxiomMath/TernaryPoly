module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth.CoefficientIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.ProjectedEntries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothRecoveryEntries

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) : data.cusp.smooth →ₗ[ℂ] data.cusp.smooth :=
  smoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
    (RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key)
    (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key)

theorem operator_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.smooth) :
    (operator data parameter halfPlane point key vector).val =
      RecoveryCoefficients.projected data parameter halfPlane
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key vector.val := rfl

theorem realize_eq_sum {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (operator data parameter halfPlane point key vector) evaluation =
      (Fintype.card (BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data)) : ℂ)⁻¹ *
        ∑ residue : BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data),
          FiniteCoefficientEvaluation.integral data vector (UniversalFiniteProfiles.boxes data key)
            parameter (GeneralLinearGroup.map integralEmbedding point)
              (evaluation * atFinite (FiniteQuotientIntegral.finiteRepresentative (RecoveryBinarySymmetry.quotient data) residue).val) := by
  rw [operator, SmoothCoefficientIntegral.realize_smoothMap data vector fixed]
  rw [integral_prod_symm _ (ProjectedCoefficientIntegral.joint_integrable data.cusp vector _
    (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) evaluation)]
  apply FiniteQuotientIntegral.level_integral
  · exact (ProjectedCoefficientIntegral.joint_integrable data.cusp vector _
      (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) evaluation).integral_prod_right
  · exact RecoveryProjectedEntries.integral_factors data vector parameter point key evaluation

theorem operator_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (matrix : BinaryRealGL) (vector : data.cusp.smooth) :
    operator data parameter halfPlane point key (DirectionalRealization.smoothTranslate data.cusp matrix vector) =
      DirectionalRealization.smoothTranslate data.cusp matrix (operator data parameter halfPlane point key vector) := by
  apply Subtype.ext
  exact projected_real data.cusp finiteCongruence _ _ matrix vector.val

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothRecoveryEntries
