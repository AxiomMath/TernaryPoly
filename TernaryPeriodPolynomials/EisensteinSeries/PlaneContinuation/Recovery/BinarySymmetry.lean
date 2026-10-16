module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.QuotientAverage
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.OrbitCoefficients

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryBinarySymmetry

def quotient {degree : ℕ} (data : InducingData degree) : IntegralBinaryGL →* FiniteSectionProjection.Quotient data :=
  (QuotientGroup.mk' (FiniteSectionProjection.normal data)).comp
    ((planeLeviHom IntegralAdeles).comp ((MonoidHom.id IntegralBinaryGL).prod 1))

theorem mem_kernel {degree : ℕ} (data : InducingData degree) (matrix : IntegralBinaryGL) :
    matrix ∈ (quotient data).ker ↔ planeLevi matrix 1 ∈ RecoveryLevel.subgroup data := by
  change QuotientGroup.mk' (FiniteSectionProjection.normal data) (planeLevi matrix 1) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

theorem inner_integral {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (matrix : IntegralBinaryGL) :
    innerCharacter data parameter (GeneralLinearGroup.det (BinaryQuotientAverage.inclusion matrix)) =
      (FiniteProfileResidues.character data (planeLevi matrix 1))⁻¹ := by
  have determinant : GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1))) =
      GeneralLinearGroup.det (BinaryQuotientAverage.inclusion matrix) := by
    rw [map_planeLevi, map_one, ← planeLevi_atFinite, det_planeLevi, mul_one]
    rfl
  change (data.chi.toMonoidHom _)⁻¹ * normPower _ _ = _
  rw [normPower]
  change (data.chi.toMonoidHom _)⁻¹ * Complex.exp (_ * (Real.log
    (adeleNorm (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding matrix))) : ℝ) : ℂ)) = _
  rw [Norm.adeleNorm_det_integral]
  simp only [NNReal.coe_one, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [FiniteProfileResidues.character, determinant]

theorem inner_kernel {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (matrix : IntegralBinaryGL)
    (membership : matrix ∈ (quotient data).ker) :
    innerCharacter data parameter (GeneralLinearGroup.det (BinaryQuotientAverage.inclusion matrix)) = 1 := by
  rw [inner_integral, RecoveryLevel.subgroup_character data _ ((mem_kernel data matrix).mp membership), inv_one]

theorem coefficient_left {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) (matrix binary : BinaryFiniteGL) :
    RecoveryCoefficients.coefficient data parameter point key (matrix * binary) =
      innerCharacter data parameter (GeneralLinearGroup.det (atFinite matrix)) *
        RecoveryCoefficients.coefficient data parameter (planeLevi (atFinite matrix)⁻¹ 1 * point) key binary := by
  simp only [RecoveryCoefficients.coefficient, atFinite_mul, Units.val_mul, ← Matrix.mul_assoc,
    FrameProfile.frame_levi, map_mul]
  ring

theorem coefficient_kernel {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (point : IntegralFiniteGL) (key : UniversalFiniteProfiles.Key data)
    (matrix : IntegralBinaryGL) (membership : matrix ∈ (quotient data).ker) (binary : BinaryFiniteGL) :
    RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key
      (GeneralLinearGroup.map integralEmbedding matrix * binary) =
        RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary := by
  let conjugate : IntegralFiniteGL := point⁻¹ * planeLevi matrix⁻¹ 1 * point
  have inverseMember : planeLevi matrix⁻¹ 1 ∈ RecoveryLevel.subgroup data := by
    exact (mem_kernel data matrix⁻¹).mp ((quotient data).ker.inv_mem membership)
  have conjugateMember : conjugate ∈ RecoveryLevel.subgroup data :=
    (RecoveryLevel.subgroup data).isNormal'.conj_mem' _ inverseMember point
  have inclusionLevi : planeLevi (BinaryQuotientAverage.inclusion matrix)⁻¹ 1 =
      FiniteSectionProjection.inclusion (planeLevi matrix⁻¹ 1) := by
    rw [← map_inv]
    change planeLevi (atFinite (GeneralLinearGroup.map integralEmbedding matrix⁻¹)) 1 = _
    rw [planeLevi_atFinite]
    congr 1
    rw [map_planeLevi, map_one]
  have pointEquality : planeLevi (BinaryQuotientAverage.inclusion matrix)⁻¹ 1 *
      FiniteSectionProjection.inclusion point =
        FiniteSectionProjection.inclusion point * FiniteSectionProjection.inclusion conjugate := by
    rw [inclusionLevi, ← map_mul, ← map_mul]
    congr 1
    dsimp [conjugate]
    group
  rw [coefficient_left]
  change innerCharacter data parameter (GeneralLinearGroup.det (BinaryQuotientAverage.inclusion matrix)) *
    RecoveryCoefficients.coefficient data parameter
      (planeLevi (BinaryQuotientAverage.inclusion matrix)⁻¹ 1 * FiniteSectionProjection.inclusion point) key binary = _
  rw [inner_kernel data parameter matrix membership, one_mul, pointEquality]
  exact RecoveryLevel.coefficient_right data parameter _ conjugate conjugateMember key binary

theorem operator_fixed (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (matrix : BinaryFiniteGL)
    (invariant : ∀ binary, coefficient (matrix * binary) = coefficient binary) (vector : data.H) :
    data.π (atFinite matrix) (operator data coefficient integrable vector) = operator data coefficient integrable vector := by
  change action data (atFinite matrix) (operator data coefficient integrable vector) = _
  rw [operator_apply, ← (action data (atFinite matrix)).integral_comp_comm
    (integrand_integrable data coefficient integrable vector)]
  have expression (binary : BinaryFiniteGL) :
      action data (atFinite matrix) (coefficient binary • data.π (atFinite binary) vector) =
        coefficient (matrix * binary) • data.π (atFinite (matrix * binary)) vector := by
    change data.π (atFinite matrix) (coefficient binary • data.π (atFinite binary) vector) = _
    rw [map_smul, invariant, atFinite_mul, map_mul, Module.End.mul_apply]
  simp_rw [expression]
  exact integral_mul_left_eq_self (μ := BinaryProductHaar.finiteMeasure)
    (fun binary => coefficient binary • data.π (atFinite binary) vector) matrix

theorem recovery_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.H) (matrix : IntegralBinaryGL)
    (membership : matrix ∈ (quotient data).ker) :
    data.cusp.π (BinaryQuotientAverage.inclusion matrix)
      (RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
        ⟨point, rfl⟩ key vector) =
      RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
        ⟨point, rfl⟩ key vector :=
  operator_fixed data.cusp _ _ _ (coefficient_kernel data parameter point key matrix membership) vector

theorem projected_eq_average {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.H) :
    RecoveryCoefficients.projected data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
        ⟨point, rfl⟩ key vector =
      BinaryQuotientAverage.average data.cusp (quotient data)
        (RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
          ⟨point, rfl⟩ key vector) :=
  BinaryQuotientAverage.projection_eq data.cusp (quotient data) _
    (recovery_fixed data parameter halfPlane point key vector)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryBinarySymmetry
