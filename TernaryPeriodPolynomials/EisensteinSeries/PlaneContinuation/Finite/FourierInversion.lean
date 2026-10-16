module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.LatticeMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourierInversion

open FiniteFourier

theorem dual_mem (scale : FiniteAdelesˣ) (frequency : FiniteAdeles) :
    frequency * scale.val ∈ Set.range integralEmbedding ↔ frequency ∈ lattice scale⁻¹ := by
  constructor
  · rintro ⟨integral, equality⟩
    refine ⟨integral, ?_⟩
    change scale.inv * integralEmbedding integral = frequency
    rw [equality, mul_comm frequency scale.val, ← mul_assoc, scale.inv_val, one_mul]
  · rintro ⟨integral, equality⟩
    refine ⟨integral, ?_⟩
    rw [← equality]
    change integralEmbedding integral = (scale.inv * integralEmbedding integral) * scale.val
    rw [mul_comm scale.inv, mul_assoc, scale.inv_val, mul_one]

theorem lattice_mem (scale : FiniteAdelesˣ) (value : FiniteAdeles) :
    value ∈ lattice scale ↔ value * scale.inv ∈ Set.range integralEmbedding := by
  change value ∈ lattice scale ↔ value * (scale⁻¹).val ∈ Set.range integralEmbedding
  simpa only [inv_inv] using (dual_mem scale⁻¹ value).symm

theorem coset_mem (scale : FiniteAdelesˣ) (offset value : FiniteAdeles) :
    value ∈ coset scale offset ↔ value - offset ∈ lattice scale := by
  constructor
  · rintro ⟨integral, membership, rfl⟩
    simpa only [add_sub_cancel_left] using membership
  · intro membership
    exact ⟨value - offset, membership, add_sub_cancel _ _⟩

theorem coset_open (scale : FiniteAdelesˣ) (offset : FiniteAdeles) : IsOpen (coset scale offset) :=
  (Homeomorph.addLeft offset).isOpenMap _ (lattice_open scale)

theorem indicator_continuous (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    Continuous ((coset scale offset).indicator (fun _ => (1 : ℂ))) :=
  (show IsClopen (coset scale offset) from
    ⟨(coset_compact scale offset).isClosed, coset_open scale offset⟩).continuous_indicator continuous_const

theorem indicator_compactSupport (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    HasCompactSupport ((coset scale offset).indicator (fun _ => (1 : ℂ))) :=
  HasCompactSupport.intro (coset_compact scale offset) (fun _ outside => Set.indicator_of_notMem outside _)

theorem indicator_integrable (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    Integrable ((coset scale offset).indicator (fun _ => (1 : ℂ))) finiteMeasure :=
  (indicator_continuous scale offset).integrable_of_hasCompactSupport (indicator_compactSupport scale offset)

theorem transform_indicator (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    transform ((coset scale offset).indicator (fun _ => (1 : ℂ))) =
      (lattice scale⁻¹).indicator (fun frequency =>
        FiniteCharacter.phase (-(frequency * offset)) * (finiteMeasure.real (lattice scale) : ℂ)) := by
  funext frequency
  rw [transform_coset, dual_mem]
  by_cases membership : frequency ∈ lattice scale⁻¹ <;> simp [membership]

theorem transform_continuous (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    Continuous (transform ((coset scale offset).indicator (fun _ => (1 : ℂ)))) := by
  rw [transform_indicator]
  exact (show IsClopen (lattice scale⁻¹) from
    ⟨(lattice_compact scale⁻¹).isClosed, lattice_open scale⁻¹⟩).continuous_indicator
    ((FiniteCharacter.phase_continuous.comp (continuous_id.mul continuous_const).neg).mul_const _)

theorem transform_compactSupport (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    HasCompactSupport (transform ((coset scale offset).indicator (fun _ => (1 : ℂ)))) := by
  rw [transform_indicator]
  exact HasCompactSupport.intro (lattice_compact scale⁻¹)
    (fun _ outside => Set.indicator_of_notMem outside _)

theorem transform_integrable (scale : FiniteAdelesˣ) (offset : FiniteAdeles) :
    Integrable (transform ((coset scale offset).indicator (fun _ => (1 : ℂ)))) finiteMeasure :=
  (transform_continuous scale offset).integrable_of_hasCompactSupport (transform_compactSupport scale offset)

theorem inversion_coset (scale : FiniteAdelesˣ) (offset frequency : FiniteAdeles) :
    transform (transform ((coset scale offset).indicator (fun _ => (1 : ℂ)))) frequency =
      (coset scale offset).indicator (fun _ => (1 : ℂ)) (-frequency) := by
  rw [transform_indicator]
  unfold transform
  have integrand : (fun value => FiniteCharacter.phase (-(frequency * value)) *
      (lattice scale⁻¹).indicator (fun value =>
        FiniteCharacter.phase (-(value * offset)) * (finiteMeasure.real (lattice scale) : ℂ)) value) =
      (lattice scale⁻¹).indicator (fun value =>
        FiniteCharacter.phase ((-(frequency + offset)) * value) * (finiteMeasure.real (lattice scale) : ℂ)) := by
    funext value
    by_cases membership : value ∈ lattice scale⁻¹
    · simp only [Set.indicator_of_mem membership, ← mul_assoc, ← FiniteCharacter.phase_add]
      congr 2
      ring
    · simp only [Set.indicator_of_notMem membership, mul_zero]
  rw [integrand, integral_indicator (lattice_compact scale⁻¹).measurableSet,
    integral_mul_const, lattice_integral]
  have membership : (-(frequency + offset)) * (scale⁻¹).val ∈ Set.range integralEmbedding ↔
      -frequency ∈ coset scale offset := by
    rw [dual_mem, inv_inv, coset_mem]
    simp only [neg_add, sub_eq_add_neg]
  rw [membership]
  by_cases belongs : -frequency ∈ coset scale offset
  · simp only [ite_eq_left belongs, Set.indicator_of_mem belongs]
    norm_cast
    rw [mul_comm]
    exact FiniteLatticeMeasure.lattice_real_measure_mul_inv scale
  · simp only [ite_eq_right belongs, Set.indicator_of_notMem belongs, zero_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourierInversion
