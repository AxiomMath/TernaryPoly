module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.AdditiveClass

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteCharacter

def character : AddChar FiniteAdeles Circle where
  toFun value := (-FiniteAdditiveClass.classHom value).toCircle
  map_zero_eq_one' := by simp only [map_zero, neg_zero, AddCircle.toCircle_zero]
  map_add_eq_mul' first second := by
    simp only [map_add, neg_add, AddCircle.toCircle_add]

theorem character_apply (value : FiniteAdeles) :
    character value = (-FiniteAdditiveClass.classHom value).toCircle := rfl

def phase (value : FiniteAdeles) : ℂ := character value

theorem character_locallyConstant : IsLocallyConstant character :=
  FiniteAdditiveClass.class_locallyConstant.comp (fun value => (-value).toCircle)

theorem character_continuous : Continuous character := character_locallyConstant.continuous

theorem phase_locallyConstant : IsLocallyConstant phase :=
  character_locallyConstant.comp (fun value => (value : ℂ))

theorem phase_continuous : Continuous phase := phase_locallyConstant.continuous

theorem phase_norm (value : FiniteAdeles) : ‖phase value‖ = 1 := Circle.norm_coe _

theorem phase_zero : phase 0 = 1 := by
  simp only [phase, AddChar.map_zero_eq_one, Circle.coe_one]

theorem phase_add (first second : FiniteAdeles) : phase (first + second) = phase first * phase second := by
  simp only [phase, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem phase_neg (value : FiniteAdeles) : phase (-value) = (phase value)⁻¹ := by
  simp only [phase, AddChar.map_neg_eq_inv, Circle.coe_inv]

theorem character_kernel (value : FiniteAdeles) :
    character value = 1 ↔ value ∈ Set.range integralEmbedding := by
  rw [character_apply, ← AddCircle.toCircle_zero (T := (1 : ℝ))]
  have injective : Function.Injective (AddCircle.toCircle (T := (1 : ℝ))) :=
    fun _ _ equality => (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).injective
      (by simpa only [AddCircle.homeomorphCircle_apply] using equality)
  rw [injective.eq_iff, neg_eq_zero, FiniteAdditiveClass.class_kernel]

theorem phase_kernel (value : FiniteAdeles) :
    phase value = 1 ↔ value ∈ Set.range integralEmbedding := by
  rw [phase, ← Circle.coe_one, Circle.coe_inj, character_kernel]

theorem phase_integral (value : IntegralAdeles) : phase (integralEmbedding value) = 1 :=
  (phase_kernel _).mpr ⟨value, rfl⟩

theorem phase_rational (value : ℚ) :
    phase (algebraMap ℚ FiniteAdeles value) =
      Complex.exp (-(2 * Real.pi * (value : ℝ)) * Complex.I) := by
  change ((-FiniteAdditiveClass.finiteClass (algebraMap ℚ FiniteAdeles value)).toCircle : ℂ) = _
  rw [FiniteAdditiveClass.class_rational, ← AddCircle.coe_neg, AddCircle.toCircle_apply_mk,
    Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem lattice_mul (first second : FiniteAdeles)
    (firstIntegral : first ∈ Set.range integralEmbedding)
    (secondIntegral : second ∈ Set.range integralEmbedding) :
    first * second ∈ Set.range integralEmbedding := by
  obtain ⟨first, rfl⟩ := firstIntegral
  obtain ⟨second, rfl⟩ := secondIntegral
  exact ⟨first * second, map_mul integralEmbedding first second⟩

theorem lattice_translate (translation : IntegralAdeles) :
    (fun value : FiniteAdeles => value + integralEmbedding translation) '' Set.range integralEmbedding =
      Set.range integralEmbedding := by
  ext value
  constructor
  · rintro ⟨_, ⟨integral, rfl⟩, rfl⟩
    exact ⟨integral + translation, map_add integralEmbedding integral translation⟩
  · rintro ⟨integral, rfl⟩
    refine ⟨integralEmbedding (integral - translation), ⟨integral - translation, rfl⟩, ?_⟩
    simp only [map_sub, sub_add_cancel]

theorem integral_translate (function : FiniteAdeles → ℂ) (translation : IntegralAdeles) :
    ∫ value in Set.range integralEmbedding, function (value + integralEmbedding translation) ∂finiteMeasure =
      ∫ value in Set.range integralEmbedding, function value ∂finiteMeasure := by
  have equality := (measurePreserving_add_right finiteMeasure (integralEmbedding translation)).setIntegral_image_emb
    (MeasurableEquiv.addRight (integralEmbedding translation)).measurableEmbedding
    function (Set.range integralEmbedding)
  rw [lattice_translate] at equality
  exact equality.symm

theorem lattice_integrable (frequency : FiniteAdeles) :
    IntegrableOn (fun value => phase (frequency * value)) (Set.range integralEmbedding) finiteMeasure :=
  ContinuousOn.integrableOn_compact integralLattice_isCompact
    (phase_continuous.comp (continuous_const.mul continuous_id)).continuousOn

theorem lattice_integral (frequency : FiniteAdeles) :
    ∫ value in Set.range integralEmbedding, phase (frequency * value) ∂finiteMeasure =
      if frequency ∈ Set.range integralEmbedding then 1 else 0 := by
  classical
  split_ifs with integral
  · calc
      _ = ∫ _ in Set.range integralEmbedding, (1 : ℂ) ∂finiteMeasure := by
        apply setIntegral_congr_fun integralLattice_isOpen.measurableSet
        intro value membership
        exact (phase_kernel _).mpr (lattice_mul _ _ integral membership)
      _ = 1 := by simp [Measure.real, finiteMeasure_integralLattice]
  · have translated := integral_translate (fun value => phase (frequency * value)) 1
    simp only [map_one, mul_add, mul_one, phase_add, integral_mul_const] at translated
    have factor : phase frequency ≠ 1 := fun equality => integral ((phase_kernel _).mp equality)
    have zeroProduct : (∫ value in Set.range integralEmbedding, phase (frequency * value) ∂finiteMeasure) *
        (phase frequency - 1) = 0 := by
      rw [mul_sub, mul_one, translated, sub_self]
    exact (mul_eq_zero.mp zeroProduct).resolve_right (sub_ne_zero.mpr factor)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteCharacter
