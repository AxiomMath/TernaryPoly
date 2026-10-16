module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.CuspDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Admissibility
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspDecay

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

def realization {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) :
    Source →L[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  ⟨(boundedRealization data.cusp).comp ((fixedSmooth data.cusp finiteCongruence).subtype.comp family),
    FiniteRotationTypes.realization_continuous_of_finite_types data.cusp finiteCongruence
      finiteCongruence_isOpen finiteCongruence_isCompact (EndpointAdmissibility.all_finiteDimensional data)
      family continuous⟩

def evaluation {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) (point : BinaryAdelicGL) : Source →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ point).comp (realization data family continuous)

theorem evaluation_apply {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) (point : BinaryAdelicGL) (vector : Source) :
    evaluation data family continuous point vector = data.cusp.realize (family vector).val point := rfl

theorem evaluation_norm_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) (point : BinaryAdelicGL) :
    ‖evaluation data family continuous point‖ ≤ ‖realization data family continuous‖ := by
  apply (evaluation data family continuous point).opNorm_le_bound
    (norm_nonneg (realization data family continuous))
  intro vector
  exact (lp.norm_apply_le_norm (by simp) (realization data family continuous vector) point).trans
    ((realization data family continuous).le_opNorm vector)

theorem weighted_uniform_bound {Index : Type*} (operators : Index → Source →L[ℂ] ℂ)
    (weight : Index → ℝ) (nonnegative : ∀ index, 0 ≤ weight index)
    (pointwise : ∀ vector : Source, ∃ bound : ℝ, ∀ index, weight index * ‖operators index vector‖ ≤ bound) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index vector, weight index * ‖operators index vector‖ ≤ bound * ‖vector‖ := by
  let scaled : Index → Source →L[ℂ] ℂ := fun index => (weight index : ℂ) • operators index
  have normEquality (index : Index) (vector : Source) :
      ‖scaled index vector‖ = weight index * ‖operators index vector‖ := by
    simp only [scaled, _root_.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (nonnegative index)]
  have bounded (vector : Source) : ∃ bound : ℝ, ∀ index, ‖scaled index vector‖ ≤ bound := by
    simpa only [normEquality] using pointwise vector
  obtain ⟨bound, operatorBound⟩ := banach_steinhaus bounded
  refine ⟨max bound 0, le_max_right _ _, fun index vector => ?_⟩
  rw [← normEquality]
  exact ((scaled index).le_opNorm vector).trans
    (mul_le_mul_of_nonneg_right ((operatorBound index).trans (le_max_left bound 0)) (norm_nonneg vector))

theorem weight_cancellation (argument : UpperHalfPlane) (order : ℕ) :
    (argument.im / 3) ^ order * (3 / argument.im) ^ order = 1 := by
  rw [← mul_pow]
  have positive := argument.im_pos
  field_simp
  simp only [one_pow]

theorem weighted_rapid_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (compactSet : Set BinaryRealGL) (compact : IsCompact compactSet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ right ∈ compactSet, ∀ integral : IntegralBinaryGL,
      ∀ argument : UpperHalfPlane, ∀ vector : Source,
        (argument.im / 3) ^ order * ‖data.cusp.realize (family vector).val
          (atFinite (GeneralLinearGroup.map integralEmbedding integral) *
            atInfinity (UpperTriangularChart.unit argument argument.im_pos * right))‖ ≤
          bound * ‖vector‖ := by
  let Index := compactSet × IntegralBinaryGL × UpperHalfPlane
  let operators : Index → Source →L[ℂ] ℂ := fun index => evaluation data family continuous
      (atFinite (GeneralLinearGroup.map integralEmbedding index.2.1) *
        atInfinity (UpperTriangularChart.unit index.2.2 index.2.2.im_pos * index.1.val))
  let weight : Index → ℝ := fun index => (index.2.2.im / 3) ^ order
  have nonnegative (index : Index) : 0 ≤ weight index :=
    pow_nonneg (div_nonneg index.2.2.im_pos.le (by norm_num)) _
  have pointwise (vector : Source) : ∃ bound : ℝ, ∀ index : Index, weight index * ‖operators index vector‖ ≤ bound := by
    obtain ⟨bound, _, bounded⟩ := CompactCuspDecay.uniform_on_compact data (family vector).val
      (family vector).property compactSet compact order
    refine ⟨bound, fun index => ?_⟩
    calc
      _ ≤ (index.2.2.im / 3) ^ order * ((3 / index.2.2.im) ^ order * bound) :=
        mul_le_mul_of_nonneg_left
          (bounded index.1.val index.1.property index.2.1 index.2.2 index.2.2.im_pos)
          (nonnegative index)
      _ = bound := by rw [← mul_assoc, weight_cancellation, one_mul]
  obtain ⟨bound, boundNonnegative, bounded⟩ := weighted_uniform_bound operators weight nonnegative pointwise
  exact ⟨bound, boundNonnegative, fun right membership integral argument vector =>
    bounded (⟨right, membership⟩, integral, argument) vector⟩

theorem rapid_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (compactSet : Set BinaryRealGL) (compact : IsCompact compactSet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ right ∈ compactSet, ∀ integral : IntegralBinaryGL,
      ∀ argument : UpperHalfPlane, ∀ vector : Source,
        ‖data.cusp.realize (family vector).val
          (atFinite (GeneralLinearGroup.map integralEmbedding integral) *
            atInfinity (UpperTriangularChart.unit argument argument.im_pos * right))‖ ≤
          (3 / argument.im) ^ order * bound * ‖vector‖ := by
  obtain ⟨bound, nonnegative, bounded⟩ := weighted_rapid_bound data family continuous compactSet compact order
  refine ⟨bound, nonnegative, fun right membership integral argument vector => ?_⟩
  have scaled := mul_le_mul_of_nonneg_left (bounded right membership integral argument vector)
    (pow_nonneg (div_nonneg (show (0 : ℝ) ≤ 3 by norm_num) argument.im_pos.le) order)
  have reverseCancellation : (3 / argument.im) ^ order * (argument.im / 3) ^ order = 1 := by
    rw [mul_comm, weight_cancellation]
  simpa only [← mul_assoc, reverseCancellation, one_mul] using scaled

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspDecay
