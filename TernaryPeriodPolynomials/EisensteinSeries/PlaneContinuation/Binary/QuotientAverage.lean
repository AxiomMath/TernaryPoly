module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.SectionProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryQuotientAverage

variable {Quotient : Type} [Group Quotient] [Finite Quotient]

def image (quotient : IntegralBinaryGL →* Quotient) : Subgroup Quotient := integralCongruence.map quotient

instance imageFintype (quotient : IntegralBinaryGL →* Quotient) : Fintype (image quotient) := Fintype.ofFinite _

def representative (quotient : IntegralBinaryGL →* Quotient) (index : image quotient) : IntegralBinaryGL :=
  index.property.choose

omit [Finite Quotient] in
theorem representative_level (quotient : IntegralBinaryGL →* Quotient) (index : image quotient) :
    representative quotient index ∈ integralCongruence := index.property.choose_spec.1

omit [Finite Quotient] in
theorem representative_image (quotient : IntegralBinaryGL →* Quotient) (index : image quotient) :
    quotient (representative quotient index) = index.val := index.property.choose_spec.2

def inclusion : IntegralBinaryGL →* BinaryAdelicGL where
  toFun matrix := atFinite (GeneralLinearGroup.map integralEmbedding matrix)
  map_one' := by rw [map_one, atFinite_one]
  map_mul' first second := by rw [map_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_mul]

def average (data : CuspidalRepresentation) (quotient : IntegralBinaryGL →* Quotient) (vector : data.H) : data.H :=
  (Fintype.card (image quotient) : ℂ)⁻¹ •
    ∑ index : image quotient, data.π (inclusion (representative quotient index)) vector

omit [Finite Quotient] in
theorem quotient_eq_value (data : CuspidalRepresentation) (quotient : IntegralBinaryGL →* Quotient)
    (vector : data.H) (invariant : ∀ matrix ∈ quotient.ker, data.π (inclusion matrix) vector = vector)
    (first second : IntegralBinaryGL) (equality : quotient first = quotient second) :
    data.π (inclusion first) vector = data.π (inclusion second) vector := by
  have membership : first⁻¹ * second ∈ quotient.ker := by
    change quotient (first⁻¹ * second) = 1
    rw [map_mul, map_inv, equality, inv_mul_cancel]
  have result := congrArg (fun value => data.π (inclusion first) value) (invariant _ membership)
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left] at result
  exact result.symm

theorem average_fixed (data : CuspidalRepresentation) (quotient : IntegralBinaryGL →* Quotient)
    (vector : data.H) (invariant : ∀ matrix ∈ quotient.ker, data.π (inclusion matrix) vector = vector) :
    average data quotient vector ∈ fixedSubspace data finiteCongruence := by
  intro element
  obtain ⟨matrix, membership, equality⟩ := element.property
  rw [← equality]
  let residue : image quotient := ⟨quotient matrix, ⟨matrix, membership, rfl⟩⟩
  unfold average
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_equiv (Equiv.mulLeft residue) (fun _ => by simp)
  intro index _
  change data.π (inclusion matrix) (data.π (inclusion (representative quotient index)) vector) = _
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
  apply quotient_eq_value data quotient vector invariant
  rw [map_mul, representative_image, representative_image]
  rfl

theorem average_inner (data : CuspidalRepresentation) (quotient : IntegralBinaryGL →* Quotient)
    (vector target : data.H) (fixed : target ∈ fixedSubspace data finiteCongruence) :
    inner ℂ target (average data quotient vector) = inner ℂ target vector := by
  have nonzero : (Fintype.card (image quotient) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have term (index : image quotient) :
      inner ℂ target (data.π (inclusion (representative quotient index)) vector) = inner ℂ target vector := by
    let element : finiteCongruence := ⟨GeneralLinearGroup.map integralEmbedding (representative quotient index),
      ⟨representative quotient index, representative_level quotient index, rfl⟩⟩
    let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π (atFinite element.val), data.unitary (atFinite element.val)⟩
    have preservation := isometry.inner_map_map target vector
    change inner ℂ (data.π (atFinite element.val) target) (data.π (atFinite element.val) vector) = _ at preservation
    rwa [fixed element] at preservation
  rw [average, inner_smul_right, inner_sum]
  simp only [term, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ nonzero _

theorem projection_eq (data : CuspidalRepresentation) (quotient : IntegralBinaryGL →* Quotient)
    (vector : data.H) (invariant : ∀ matrix ∈ quotient.ker, data.π (inclusion matrix) vector = vector) :
    averagingOperator data finiteCongruence vector = average data quotient vector := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (average_fixed data quotient vector invariant)
  intro target fixed
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right, average_inner data quotient vector target fixed, sub_self]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryQuotientAverage
