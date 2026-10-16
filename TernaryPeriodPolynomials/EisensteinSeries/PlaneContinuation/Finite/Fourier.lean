module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.Character

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourier

def lattice (scale : FiniteAdelesˣ) : Set FiniteAdeles :=
  Set.range (fun value : IntegralAdeles => scale.val * integralEmbedding value)

def coset (scale : FiniteAdelesˣ) (offset : FiniteAdeles) : Set FiniteAdeles :=
  (fun value => offset + value) '' lattice scale

theorem lattice_compact (scale : FiniteAdelesˣ) : IsCompact (lattice scale) :=
  isCompact_range (continuous_const.mul integralEmbedding_isOpenEmbedding.continuous)

theorem lattice_open (scale : FiniteAdelesˣ) : IsOpen (lattice scale) := by
  have equality : lattice scale = (ContinuousAddEquiv.mulLeft scale) '' Set.range integralEmbedding := by
    rw [lattice, ← Set.range_comp]
    rfl
  rw [equality]
  exact (ContinuousAddEquiv.mulLeft scale).toHomeomorph.isOpenMap _ integralLattice_isOpen

theorem coset_compact (scale : FiniteAdelesˣ) (offset : FiniteAdeles) : IsCompact (coset scale offset) :=
  (lattice_compact scale).image (continuous_const.add continuous_id)

theorem lattice_translate (scale : FiniteAdelesˣ) (translation : IntegralAdeles) :
    (fun value : FiniteAdeles => value + scale.val * integralEmbedding translation) '' lattice scale =
      lattice scale := by
  ext value
  constructor
  · rintro ⟨_, ⟨integral, rfl⟩, rfl⟩
    exact ⟨integral + translation, by simp only [map_add, mul_add]⟩
  · rintro ⟨integral, rfl⟩
    refine ⟨scale.val * integralEmbedding (integral - translation), ⟨integral - translation, rfl⟩, ?_⟩
    simp only [map_sub, mul_sub, sub_add_cancel]

theorem integral_translate (function : FiniteAdeles → ℂ) (scale : FiniteAdelesˣ)
    (translation : IntegralAdeles) :
    ∫ value in lattice scale, function (value + scale.val * integralEmbedding translation) ∂finiteMeasure =
      ∫ value in lattice scale, function value ∂finiteMeasure := by
  have equality := (measurePreserving_add_right finiteMeasure (scale.val * integralEmbedding translation)).setIntegral_image_emb
    (MeasurableEquiv.addRight (scale.val * integralEmbedding translation)).measurableEmbedding
    function (lattice scale)
  rw [lattice_translate] at equality
  exact equality.symm

theorem lattice_integrable (scale : FiniteAdelesˣ) (frequency : FiniteAdeles) :
    IntegrableOn (fun value => FiniteCharacter.phase (frequency * value)) (lattice scale) finiteMeasure :=
  ContinuousOn.integrableOn_compact (lattice_compact scale)
    (FiniteCharacter.phase_continuous.comp (continuous_const.mul continuous_id)).continuousOn

theorem lattice_integral (scale : FiniteAdelesˣ) (frequency : FiniteAdeles) :
    ∫ value in lattice scale, FiniteCharacter.phase (frequency * value) ∂finiteMeasure =
      if frequency * scale.val ∈ Set.range integralEmbedding then
        (finiteMeasure.real (lattice scale) : ℂ) else 0 := by
  split_ifs with integral
  · calc
      _ = ∫ _ in lattice scale, (1 : ℂ) ∂finiteMeasure := by
        apply setIntegral_congr_fun (lattice_compact scale).measurableSet
        rintro value ⟨integralValue, rfl⟩
        dsimp only
        rw [← mul_assoc]
        exact (FiniteCharacter.phase_kernel _).mpr
          (FiniteCharacter.lattice_mul _ _ integral ⟨integralValue, rfl⟩)
      _ = _ := by simp
  · have translated := integral_translate (fun value => FiniteCharacter.phase (frequency * value)) scale 1
    simp only [map_one, mul_one, mul_add, FiniteCharacter.phase_add, integral_mul_const] at translated
    have factor : FiniteCharacter.phase (frequency * scale.val) ≠ 1 :=
      fun equality => integral ((FiniteCharacter.phase_kernel _).mp equality)
    have zeroProduct : (∫ value in lattice scale, FiniteCharacter.phase (frequency * value) ∂finiteMeasure) *
        (FiniteCharacter.phase (frequency * scale.val) - 1) = 0 := by
      rw [mul_sub, mul_one, translated, sub_self]
    exact (mul_eq_zero.mp zeroProduct).resolve_right (sub_ne_zero.mpr factor)

theorem coset_integral (scale : FiniteAdelesˣ) (offset frequency : FiniteAdeles) :
    ∫ value in coset scale offset, FiniteCharacter.phase (frequency * value) ∂finiteMeasure =
      FiniteCharacter.phase (frequency * offset) *
        if frequency * scale.val ∈ Set.range integralEmbedding then
          (finiteMeasure.real (lattice scale) : ℂ) else 0 := by
  rw [coset, (measurePreserving_add_left finiteMeasure offset).setIntegral_image_emb
    (MeasurableEquiv.addLeft offset).measurableEmbedding]
  simp only [mul_add, FiniteCharacter.phase_add, integral_const_mul, lattice_integral]

def transform (function : FiniteAdeles → ℂ) (frequency : FiniteAdeles) : ℂ :=
  ∫ value, FiniteCharacter.phase (-(frequency * value)) * function value ∂finiteMeasure

theorem transform_coset (scale : FiniteAdelesˣ) (offset frequency : FiniteAdeles) :
    transform ((coset scale offset).indicator (fun _ => (1 : ℂ))) frequency =
      FiniteCharacter.phase (-(frequency * offset)) *
        if frequency * scale.val ∈ Set.range integralEmbedding then
          (finiteMeasure.real (lattice scale) : ℂ) else 0 := by
  have negIntegral : -(frequency * scale.val) ∈ Set.range integralEmbedding ↔
      frequency * scale.val ∈ Set.range integralEmbedding := by
    constructor <;> rintro ⟨integral, equality⟩ <;>
      exact ⟨-integral, by simpa only [map_neg, neg_neg] using congrArg Neg.neg equality⟩
  unfold transform
  have integrand : (fun value => FiniteCharacter.phase (-(frequency * value)) *
      (coset scale offset).indicator (fun _ => (1 : ℂ)) value) =
      (coset scale offset).indicator (fun value => FiniteCharacter.phase (-(frequency * value))) := by
    funext value
    by_cases membership : value ∈ coset scale offset <;> simp [membership]
  rw [integrand]
  rw [integral_indicator (coset_compact scale offset).measurableSet]
  simp only [← neg_mul]
  rw [coset_integral]
  simp only [neg_mul, negIntegral]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourier
