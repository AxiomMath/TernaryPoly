module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PrimitiveTupleIdentity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryOperator
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleFiniteAverage

theorem character_mul {degree : ℕ} (data : InducingData degree) (first second : IntegralFiniteGL) :
    character data (first * second) = character data first * character data second := by
  simp only [character, map_mul, atFinite_mul]

theorem row_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point matrix : IntegralFiniteGL)
    (membership : matrix ∈ normal data) (value : Space data) :
    row data parameter halfPlane (point * matrix) value = row data parameter halfPlane point value := by
  simp only [TupleRecoveryOperator.row_apply]
  apply Finset.sum_congr rfl
  intro key _
  change (∫ binary, RecoveryCoefficients.coefficient data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding (point * matrix))) key binary •
      data.cusp.π (atFinite binary) (value key) ∂BinaryProductHaar.finiteMeasure) =
    ∫ binary, RecoveryCoefficients.coefficient data parameter
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary •
        data.cusp.π (atFinite binary) (value key) ∂BinaryProductHaar.finiteMeasure
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  dsimp only
  rw [map_mul, atFinite_mul, RecoveryLevel.coefficient_right data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding point)) matrix membership key binary]

def sectionRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) : data.cusp.H :=
  character data point • row data parameter halfPlane point value

theorem sectionRow_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point matrix : IntegralFiniteGL)
    (membership : matrix ∈ normal data) (value : Space data) :
    sectionRow data parameter halfPlane (point * matrix) value = sectionRow data parameter halfPlane point value := by
  rw [sectionRow, row_right data parameter halfPlane point matrix membership]
  rw [character_mul]
  have trivial : character data matrix = 1 := RecoveryLevel.subgroup_character data matrix membership
  rw [trivial, mul_one]
  rfl

theorem coefficient_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (point : IntegralFiniteGL) (matrix : IntegralBinaryGL) (key : UniversalFiniteProfiles.Key data)
    (binary : BinaryFiniteGL) :
    RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point))) key
      (GeneralLinearGroup.map integralEmbedding matrix * binary) =
        (character data (planeLevi matrix 1))⁻¹ *
          RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary := by
  have levi : inclusion (planeLevi matrix 1) = planeLevi (BinaryQuotientAverage.inclusion matrix) 1 := by
    change atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1)) = _
    rw [map_planeLevi, map_one, ← planeLevi_atFinite]
    rfl
  have pointEquality : planeLevi (BinaryQuotientAverage.inclusion matrix)⁻¹ 1 *
      inclusion (planeLevi matrix 1 * point) = inclusion point := by
    rw [map_mul, levi, ← mul_assoc]
    have inverse : planeLevi (BinaryQuotientAverage.inclusion matrix)⁻¹ 1 *
        planeLevi (BinaryQuotientAverage.inclusion matrix) 1 = 1 := by
      change (planeLeviHom Adeles) ((BinaryQuotientAverage.inclusion matrix)⁻¹, 1) *
        (planeLeviHom Adeles) (BinaryQuotientAverage.inclusion matrix, 1) = 1
      rw [← map_mul]
      change (planeLeviHom Adeles) ((BinaryQuotientAverage.inclusion matrix)⁻¹ * BinaryQuotientAverage.inclusion matrix, (1 : Adelesˣ) * 1) = 1
      rw [inv_mul_cancel, one_mul]
      exact (planeLeviHom Adeles).map_one
    rw [inverse, one_mul]
  rw [RecoveryBinarySymmetry.coefficient_left]
  change GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (BinaryQuotientAverage.inclusion matrix)) *
    RecoveryCoefficients.coefficient data parameter
      (planeLevi (BinaryQuotientAverage.inclusion matrix)⁻¹ 1 * inclusion (planeLevi matrix 1 * point)) key binary = _
  rw [pointEquality, RecoveryBinarySymmetry.inner_integral]
  rfl

theorem operator_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.H) :
    RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point))) ⟨_, rfl⟩ key vector =
      (character data (planeLevi matrix 1))⁻¹ • data.cusp.π (BinaryQuotientAverage.inclusion matrix)
        (RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨_, rfl⟩ key vector) := by
  change (∫ binary, RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point))) key binary •
    data.cusp.π (atFinite binary) vector ∂BinaryProductHaar.finiteMeasure) = _
  rw [← integral_mul_left_eq_self (μ := BinaryProductHaar.finiteMeasure)
    (fun binary => RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point))) key binary •
      data.cusp.π (atFinite binary) vector) (GeneralLinearGroup.map integralEmbedding matrix)]
  simp_rw [coefficient_levi data parameter point matrix key]
  simp only [atFinite_mul, map_mul, Module.End.mul_apply, mul_smul]
  rw [integral_smul]
  apply congrArg (fun v : data.cusp.H => (character data (planeLevi matrix 1))⁻¹ • v)
  change (∫ binary, RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary •
    FiniteHilbertConvolution.action data.cusp (BinaryQuotientAverage.inclusion matrix)
      (data.cusp.π (atFinite binary) vector) ∂BinaryProductHaar.finiteMeasure) = _
  simp_rw [← (FiniteHilbertConvolution.action data.cusp (BinaryQuotientAverage.inclusion matrix)).map_smul]
  exact (FiniteHilbertConvolution.action data.cusp (BinaryQuotientAverage.inclusion matrix)).integral_comp_comm
    (FiniteHilbertConvolution.integrand_integrable data.cusp _
      (RecoveryCoefficients.coefficient_integrable data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨_, rfl⟩ key) vector)

theorem sectionRow_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (value : Space data) :
    sectionRow data parameter halfPlane (planeLevi matrix 1 * point) value =
      data.cusp.π (BinaryQuotientAverage.inclusion matrix) (sectionRow data parameter halfPlane point value) := by
  simp only [sectionRow, TupleRecoveryOperator.row_apply]
  simp_rw [operator_levi data parameter halfPlane point matrix]
  rw [← Finset.smul_sum, ← map_sum, map_smul]
  rw [character_mul, smul_smul]
  have scalar : (character data (planeLevi matrix 1) * character data point) *
      (character data (planeLevi matrix 1))⁻¹ = character data point := by
    rw [mul_right_comm, mul_inv_cancel₀ (character_nonzero data _), one_mul]
  rw [scalar]

def sectionAverage {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) : data.cusp.H :=
  (Fintype.card (levelImage data) : ℂ)⁻¹ •
    ∑ residue : levelImage data, sectionRow data parameter halfPlane (point * representative data residue) value

theorem sectionAverage_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point matrix : IntegralFiniteGL)
    (membership : matrix ∈ integralLevel) (value : Space data) :
    sectionAverage data parameter halfPlane (point * matrix) value = sectionAverage data parameter halfPlane point value := by
  let residue : levelImage data := ⟨QuotientGroup.mk' (normal data) matrix, ⟨matrix, membership, rfl⟩⟩
  unfold sectionAverage
  apply congrArg (fun v : data.cusp.H => (Fintype.card (levelImage data) : ℂ)⁻¹ • v)
  apply Finset.sum_equiv (Equiv.mulLeft residue) (fun _ => by simp)
  intro index _
  have equality : QuotientGroup.mk' (normal data) (matrix * representative data index) =
      QuotientGroup.mk' (normal data) (representative data (residue * index)) := by
    rw [map_mul, representative_image, representative_image]
    rfl
  have kernel : (matrix * representative data index)⁻¹ * representative data (residue * index) ∈ normal data :=
    QuotientGroup.eq.mp equality
  have result := sectionRow_right data parameter halfPlane (point * (matrix * representative data index))
    ((matrix * representative data index)⁻¹ * representative data (residue * index)) kernel value
  rw [mul_assoc, mul_inv_cancel_left] at result
  change sectionRow data parameter halfPlane ((point * matrix) * representative data index) value =
    sectionRow data parameter halfPlane (point * representative data (residue * index)) value
  simpa only [mul_assoc] using result.symm

theorem sectionAverage_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (value : Space data) :
    sectionAverage data parameter halfPlane (planeLevi matrix 1 * point) value =
      data.cusp.π (BinaryQuotientAverage.inclusion matrix) (sectionAverage data parameter halfPlane point value) := by
  simp only [sectionAverage, mul_assoc, sectionRow_levi, map_smul, map_sum]

theorem congruence_conjugate (point : IntegralFiniteGL) (matrix : IntegralBinaryGL)
    (membership : matrix ∈ integralCongruence) : point⁻¹ * planeLevi matrix 1 * point ∈ integralLevel := by
  have reduction : GeneralLinearGroup.map integralReduction (planeLevi matrix 1) = 1 := by
    rw [map_planeLevi, map_one, show GeneralLinearGroup.map integralReduction matrix = 1 from membership]
    exact (planeLeviHom (ZMod 3)).map_one
  change GeneralLinearGroup.map integralReduction (point⁻¹ * planeLevi matrix 1 * point) ∈ rowStabilizer
  rw [map_mul, map_mul, map_inv, reduction, mul_one, inv_mul_cancel]
  exact rowStabilizer.one_mem

theorem sectionAverage_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) :
    sectionAverage data parameter halfPlane point value ∈ fixedSubspace data.cusp finiteCongruence := by
  rintro ⟨_, matrix, membership, rfl⟩
  change data.cusp.π (BinaryQuotientAverage.inclusion matrix) (sectionAverage data parameter halfPlane point value) = _
  rw [← sectionAverage_levi]
  have equality : planeLevi matrix 1 * point = point * (point⁻¹ * planeLevi matrix 1 * point) := by group
  rw [equality, sectionAverage_right data parameter halfPlane point _ (congruence_conjugate point matrix membership)]

theorem averagedRow_eq {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) :
    averagedRow data parameter halfPlane point value =
      (character data point)⁻¹ • sectionAverage data parameter halfPlane point value := by
  have raw : (Fintype.card (levelImage data) : ℂ)⁻¹ •
      (∑ residue : levelImage data, character data (representative data residue) •
        row data parameter halfPlane (point * representative data residue) value) =
      (character data point)⁻¹ • sectionAverage data parameter halfPlane point value := by
    simp only [sectionAverage, sectionRow]
    rw [smul_comm (character data point)⁻¹]
    apply congrArg (fun v : data.cusp.H => (Fintype.card (levelImage data) : ℂ)⁻¹ • v)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro residue _
    rw [character_mul, ← smul_smul, inv_smul_smul₀ (character_nonzero data point)]
  simp only [averagedRow, _root_.smul_apply, _root_.sum_apply, projectedRow, ContinuousLinearMap.comp_apply]
  simp_rw [← (CompactAveraging.averagingOperator data.cusp finiteCongruence).map_smul]
  rw [← map_sum, ← map_smul, raw, map_smul, CompactAveraging.averagingOperator_of_fixed data.cusp finiteCongruence _
    (sectionAverage_fixed data parameter halfPlane point value)]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleFiniteAverage
