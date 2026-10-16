module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth.TupleOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleScalarAverage

def raw {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) : ℂ :=
  ∑ key, FiniteCoefficientEvaluation.integral data (value key) (UniversalFiniteProfiles.boxes data key)
    parameter (GeneralLinearGroup.map integralEmbedding point) evaluation

def sectionRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) : ℂ :=
  character data point * raw data parameter point value evaluation

theorem raw_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point matrix : IntegralFiniteGL)
    (membership : matrix ∈ normal data) (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    raw data parameter (point * matrix) value evaluation = raw data parameter point value evaluation := by
  unfold raw
  apply Finset.sum_congr rfl
  intro key _
  change (∫ binary, RecoveryCoefficients.coefficient data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding (point * matrix))) key binary *
      data.cusp.realize (value key) (evaluation * atFinite binary) ∂BinaryProductHaar.finiteMeasure) = _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  dsimp only
  rw [map_mul, atFinite_mul, RecoveryLevel.coefficient_right data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding point)) matrix membership key binary]
  rfl

theorem sectionRow_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point matrix : IntegralFiniteGL)
    (membership : matrix ∈ normal data) (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    sectionRow data parameter (point * matrix) value evaluation = sectionRow data parameter point value evaluation := by
  rw [sectionRow, TupleFiniteAverage.character_mul, raw_right data parameter point matrix membership,
    RecoveryLevel.subgroup_character data matrix membership, mul_one]
  rfl

theorem integral_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.smooth)
    (evaluation : BinaryAdelicGL) :
    FiniteCoefficientEvaluation.integral data vector (UniversalFiniteProfiles.boxes data key) parameter
      (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point)) evaluation =
        (character data (planeLevi matrix 1))⁻¹ *
          FiniteCoefficientEvaluation.integral data vector (UniversalFiniteProfiles.boxes data key) parameter
            (GeneralLinearGroup.map integralEmbedding point) (evaluation * BinaryQuotientAverage.inclusion matrix) := by
  change (∫ binary, RecoveryCoefficients.coefficient data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point))) key binary *
      data.cusp.realize vector (evaluation * atFinite binary) ∂BinaryProductHaar.finiteMeasure) = _
  rw [← integral_mul_left_eq_self (μ := BinaryProductHaar.finiteMeasure)
    (fun binary => RecoveryCoefficients.coefficient data parameter
      (atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi matrix 1 * point))) key binary *
        data.cusp.realize vector (evaluation * atFinite binary)) (GeneralLinearGroup.map integralEmbedding matrix)]
  simp_rw [TupleFiniteAverage.coefficient_levi data parameter point matrix key]
  simp only [atFinite_mul, ← mul_assoc evaluation, mul_assoc (character data (planeLevi matrix 1))⁻¹]
  rw [integral_const_mul]
  rfl

theorem sectionRow_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    sectionRow data parameter (planeLevi matrix 1 * point) value evaluation =
      sectionRow data parameter point value (evaluation * BinaryQuotientAverage.inclusion matrix) := by
  simp only [sectionRow, raw, integral_levi, ← Finset.mul_sum, TupleFiniteAverage.character_mul]
  rw [← mul_assoc, mul_right_comm (character data (planeLevi matrix 1)),
    mul_inv_cancel₀ (character_nonzero data _), one_mul]

def average {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) : ℂ :=
  (Fintype.card (levelImage data) : ℂ)⁻¹ *
    ∑ residue : levelImage data, sectionRow data parameter (point * representative data residue) value evaluation

theorem average_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point matrix : IntegralFiniteGL)
    (membership : matrix ∈ integralLevel) (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    average data parameter (point * matrix) value evaluation = average data parameter point value evaluation := by
  let residue : levelImage data := ⟨QuotientGroup.mk' (normal data) matrix, ⟨matrix, membership, rfl⟩⟩
  unfold average
  apply congrArg (fun scalar : ℂ => (Fintype.card (levelImage data) : ℂ)⁻¹ * scalar)
  apply Finset.sum_equiv (Equiv.mulLeft residue) (fun _ => by simp)
  intro index _
  have equality : QuotientGroup.mk' (normal data) (matrix * representative data index) =
      QuotientGroup.mk' (normal data) (representative data (residue * index)) := by
    rw [map_mul, representative_image, representative_image]
    rfl
  have kernel : (matrix * representative data index)⁻¹ * representative data (residue * index) ∈ normal data :=
    QuotientGroup.eq.mp equality
  have result := sectionRow_right data parameter (point * (matrix * representative data index))
    ((matrix * representative data index)⁻¹ * representative data (residue * index)) kernel value evaluation
  rw [mul_assoc, mul_inv_cancel_left] at result
  change sectionRow data parameter ((point * matrix) * representative data index) value evaluation =
    sectionRow data parameter (point * representative data (residue * index)) value evaluation
  simpa only [mul_assoc] using result.symm

theorem average_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    average data parameter (planeLevi matrix 1 * point) value evaluation =
      average data parameter point value (evaluation * BinaryQuotientAverage.inclusion matrix) := by
  simp only [average, mul_assoc, sectionRow_levi]

theorem average_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (matrix : IntegralBinaryGL) (membership : matrix ∈ integralCongruence)
    (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    average data parameter point value (evaluation * BinaryQuotientAverage.inclusion matrix) =
      average data parameter point value evaluation := by
  rw [← average_levi]
  have equality : planeLevi matrix 1 * point = point * (point⁻¹ * planeLevi matrix 1 * point) := by group
  rw [equality, average_right data parameter point _ (TupleFiniteAverage.congruence_conjugate point matrix membership)]

theorem average_fixed_finite {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : IntegralFiniteGL)
    (matrix : finiteCongruence) (value : SmoothTupleOperator.Space data) (evaluation : BinaryAdelicGL) :
    average data parameter point value (evaluation * atFinite matrix.val) = average data parameter point value evaluation := by
  obtain ⟨integer, membership, equality⟩ := matrix.property
  rw [← equality]
  exact average_fixed data parameter point integer membership value evaluation

theorem projectedRow_realize {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : SmoothTupleOperator.Space data)
    (fixed : ∀ key, (value key).val ∈ fixedSubspace data.cusp finiteCongruence) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (SmoothTupleOperator.projectedRow data parameter halfPlane point value) evaluation =
      (Fintype.card (BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data)) : ℂ)⁻¹ *
        ∑ residue : BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data),
          raw data parameter point value
            (evaluation * atFinite (FiniteQuotientIntegral.finiteRepresentative (RecoveryBinarySymmetry.quotient data) residue).val) := by
  simp only [SmoothTupleOperator.projectedRow_apply, map_sum, Finset.sum_apply,
    SmoothRecoveryEntries.realize_eq_sum data parameter halfPlane point _ _ (fixed _), raw, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem averagedRow_realize {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : SmoothTupleOperator.Space data)
    (fixed : ∀ key, (value key).val ∈ fixedSubspace data.cusp finiteCongruence) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (SmoothTupleOperator.averagedRow data parameter halfPlane point value) evaluation =
      (character data point)⁻¹ * average data parameter point value evaluation := by
  have expression : data.cusp.realize (SmoothTupleOperator.averagedRow data parameter halfPlane point value) evaluation =
      (Fintype.card (BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data)) : ℂ)⁻¹ *
        ∑ residue : BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data),
          (character data point)⁻¹ * average data parameter point value
            (evaluation * atFinite (FiniteQuotientIntegral.finiteRepresentative (RecoveryBinarySymmetry.quotient data) residue).val) := by
    simp only [SmoothTupleOperator.averagedRow, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      projectedRow_realize data parameter halfPlane _ value fixed, average, sectionRow, TupleFiniteAverage.character_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro residue _
    apply Finset.sum_congr rfl
    intro levelResidue _
    field_simp [character_nonzero data point]
  rw [expression]
  simp only [average_fixed_finite, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ (by exact_mod_cast Fintype.card_ne_zero) _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleScalarAverage
