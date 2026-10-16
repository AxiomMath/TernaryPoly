module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.Level
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.OperatorLimit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection

def integralLevel : Subgroup IntegralFiniteGL := rowStabilizer.comap (GeneralLinearGroup.map integralReduction)

def normal {degree : ℕ} (data : InducingData degree) : Subgroup IntegralFiniteGL :=
  (RecoveryLevel.subgroup data).toOpenSubgroup.toSubgroup

instance normal_isNormal {degree : ℕ} (data : InducingData degree) : (normal data).Normal :=
  (RecoveryLevel.subgroup data).isNormal'

abbrev Quotient {degree : ℕ} (data : InducingData degree) := IntegralFiniteGL ⧸ normal data

instance quotientDiscrete {degree : ℕ} (data : InducingData degree) : DiscreteTopology (Quotient data) :=
  QuotientGroup.discreteTopology (RecoveryLevel.subgroup data).toOpenSubgroup.isOpen

instance quotientFinite {degree : ℕ} (data : InducingData degree) : Finite (Quotient data) := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact finite_of_compact_of_discrete

def levelImage {degree : ℕ} (data : InducingData degree) : Subgroup (Quotient data) :=
  integralLevel.map (QuotientGroup.mk' (normal data))

instance levelImageFintype {degree : ℕ} (data : InducingData degree) : Fintype (levelImage data) :=
  Fintype.ofFinite _

def representative {degree : ℕ} (data : InducingData degree) (index : levelImage data) : IntegralFiniteGL :=
  index.property.choose

theorem representative_level {degree : ℕ} (data : InducingData degree) (index : levelImage data) :
    representative data index ∈ integralLevel := index.property.choose_spec.1

theorem representative_image {degree : ℕ} (data : InducingData degree) (index : levelImage data) :
    QuotientGroup.mk' (normal data) (representative data index) = index.val := index.property.choose_spec.2

def inclusion : IntegralFiniteGL →* AdelicGL where
  toFun matrix := atFinite (GeneralLinearGroup.map integralEmbedding matrix)
  map_one' := by rw [map_one, CompactAveraging.atFinite_one]
  map_mul' first second := by rw [map_mul, atFinite_mul]

def average {degree : ℕ} (data : InducingData degree) (function : AdelicGL → ℂ) (point : AdelicGL) : ℂ :=
  (Fintype.card (levelImage data) : ℂ)⁻¹ *
    ∑ index : levelImage data, function (point * inclusion (representative data index))

theorem quotient_eq_value {degree : ℕ} (data : InducingData degree) (function : AdelicGL → ℂ)
    (invariant : ∀ point matrix, matrix ∈ normal data → function (point * inclusion matrix) = function point)
    (point : AdelicGL) (first second : IntegralFiniteGL)
    (equality : QuotientGroup.mk' (normal data) first = QuotientGroup.mk' (normal data) second) :
    function (point * inclusion first) = function (point * inclusion second) := by
  have membership : first⁻¹ * second ∈ normal data := QuotientGroup.eq.mp equality
  have result := invariant (point * inclusion first) (first⁻¹ * second) membership
  rw [mul_assoc, ← map_mul, mul_inv_cancel_left] at result
  exact result.symm

theorem average_right {degree : ℕ} (data : InducingData degree) (function : AdelicGL → ℂ)
    (invariant : ∀ point matrix, matrix ∈ normal data → function (point * inclusion matrix) = function point)
    (point : AdelicGL) (matrix : IntegralFiniteGL) (membership : matrix ∈ integralLevel) :
    average data function (point * inclusion matrix) = average data function point := by
  let residue : levelImage data := ⟨QuotientGroup.mk' (normal data) matrix, ⟨matrix, membership, rfl⟩⟩
  unfold average
  congr 1
  apply Finset.sum_equiv (Equiv.mulLeft residue) (fun _ => by simp)
  intro index _
  rw [mul_assoc, ← map_mul]
  apply quotient_eq_value data function invariant point
  rw [map_mul, representative_image, representative_image]
  rfl

theorem average_fixed {degree : ℕ} (data : InducingData degree) (function : AdelicGL → ℂ)
    (invariant : ∀ point matrix, matrix ∈ integralLevel → function (point * inclusion matrix) = function point)
    (point : AdelicGL) : average data function point = function point := by
  have nonzero : (Fintype.card (levelImage data) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  simp only [invariant point _ (representative_level data _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ nonzero _

theorem right_continuation {function continuation : ℂ → AdelicGL → ℂ}
    (continues : IsEisensteinContinuation function continuation) (matrix : AdelicGL) :
    IsEisensteinContinuation (fun parameter point => function parameter (point * matrix))
      (fun parameter point => continuation parameter (point * matrix)) := by
  refine ⟨fun point parameter => continues.1 (point * matrix) parameter, ?_⟩
  obtain ⟨bound, equality⟩ := continues.2
  refine ⟨bound, fun parameter halfPlane point => ?_⟩
  apply (equality parameter halfPlane (point * matrix)).congr_fun
  intro flag
  simp only [eisensteinSummand, mul_assoc]

theorem average_continuation {degree : ℕ} (data : InducingData degree) {function continuation : ℂ → AdelicGL → ℂ}
    (continues : IsEisensteinContinuation function continuation) :
    IsEisensteinContinuation (fun parameter => average data (function parameter))
      (fun parameter => average data (continuation parameter)) := by
  exact ContinuationAlgebra.multiply
    (ContinuationAlgebra.finset_sum Finset.univ
      (fun index parameter point => function parameter (point * inclusion (representative data index)))
      (fun index parameter point => continuation parameter (point * inclusion (representative data index)))
      (fun index _ => right_continuation continues (inclusion (representative data index))))
    (fun _ => (Fintype.card (levelImage data) : ℂ)⁻¹) (fun _ => analyticAt_const.meromorphicAt)

def sectionFunction {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) : AdelicGL → ℂ :=
  average data (FiniteRecoveryIntegral.sectionFunction induced)

theorem section_level {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (matrix : finiteLevel) :
    sectionFunction induced (point * atFinite matrix.val) = sectionFunction induced point := by
  obtain ⟨integer, membership, equality⟩ := matrix.property
  rw [← equality]
  exact average_right data (FiniteRecoveryIntegral.sectionFunction induced)
    (RecoveryLevel.section_right induced) point integer membership

theorem exists_continuation {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation (fun parameter => sectionFunction (flat.1 parameter)) continuation := by
  obtain ⟨continuation, continues⟩ := FiniteRecoveryContinuation.exists_continuation flat
  exact ⟨fun parameter => average data (continuation parameter), average_continuation data continues⟩

theorem compact_right (point : AdelicGL) (compact : inMaximalCompact point) (matrix : IntegralFiniteGL) :
    inMaximalCompact (point * inclusion matrix) := by
  have realIdentity : realGroup (inclusion matrix) = 1 := by apply Units.ext; rfl
  refine ⟨?_, ?_⟩
  · simpa only [map_mul, realIdentity, mul_one] using compact.1
  · obtain ⟨integer, integerEquality⟩ := compact.2
    refine ⟨integer * matrix, ?_⟩
    rw [map_mul, integerEquality, map_mul]
    rfl

theorem induced_average {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) : average data function point = function point := by
  apply average_fixed
  intro point matrix membership
  exact induced.2.1 ⟨GeneralLinearGroup.map integralEmbedding matrix, ⟨matrix, membership, rfl⟩⟩ point

theorem section_tendsto {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (reference : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re)
    (point : AdelicGL) (compact : inMaximalCompact point) :
    Filter.Tendsto (fun index : ℕ => sectionFunction (flat.1 (reference + index)) point) Filter.atTop
      (nhds ((FinitePrimitiveRecovery.mass : ℂ) * function reference point)) := by
  have terms (key : levelImage data) := FiniteRecoveryAsymptotic.section_tendsto flat reference halfPlane
    (point * inclusion (representative data key)) (compact_right point compact (representative data key))
  have summed := (tendsto_finsetSum Finset.univ (fun key _ => terms key)).const_mul
    (Fintype.card (levelImage data) : ℂ)⁻¹
  have equality : (Fintype.card (levelImage data) : ℂ)⁻¹ *
      (∑ key : levelImage data, (FinitePrimitiveRecovery.mass : ℂ) * function reference
        (point * inclusion (representative data key))) = (FinitePrimitiveRecovery.mass : ℂ) * function reference point := by
    rw [← Finset.mul_sum, mul_left_comm]
    exact congrArg (fun value : ℂ => (FinitePrimitiveRecovery.mass : ℂ) * value)
      (induced_average (flat.1 reference) point)
  simpa only [sectionFunction, average, equality] using summed

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
