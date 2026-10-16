module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FundamentalDomain

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Pointwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PeriodicIntegral

open FundamentalDomain

theorem aestronglyMeasurable_of_periodic_on (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (measurable : AEStronglyMeasurable function (adeleMeasure.restrict additiveDomain)) :
    AEStronglyMeasurable function adeleMeasure := by
  have onImages : ∀ rational : ℚ,
      AEStronglyMeasurable function (adeleMeasure.restrict (rational +ᵥ additiveDomain)) := by
    intro rational
    exact ((additiveDomain_fundamental.vadd rational).aestronglyMeasurable_on_iff
      additiveDomain_fundamental periodic).mpr measurable
  have onUnion := AEStronglyMeasurable.iUnion onImages
  rw [Measure.restrict_congr_set additiveDomain_fundamental.iUnion_vadd_ae_eq,
    Measure.restrict_univ] at onUnion
  exact onUnion

theorem fundamental_image (equivalence : Adeles ≃ᵐ Adeles)
    (rationalEquivalence : ℚ ≃+ ℚ)
    (compatible : ∀ rational value, equivalence (rationalAdele rational + value) =
      rationalAdele (rationalEquivalence rational) + equivalence value) :
    IsAddFundamentalDomain ℚ (equivalence '' additiveDomain) adeleMeasure := by
  apply IsAddFundamentalDomain.mk'
    (equivalence.measurableEmbedding.measurableSet_image.mpr
      additiveDomain_measurable).nullMeasurableSet
  intro value
  obtain ⟨rational, membership, unique⟩ := translate_existsUnique (equivalence.symm value)
  refine ⟨rationalEquivalence rational, ?_, ?_⟩
  · refine ⟨rationalAdele rational + equivalence.symm value, membership, ?_⟩
    rw [compatible, equivalence.apply_symm_apply]
    rfl
  · intro other otherMembership
    obtain ⟨representative, membership', equality⟩ := otherMembership
    have representativeEquality :
        rationalAdele (rationalEquivalence.symm other) + equivalence.symm value =
          representative := by
      apply equivalence.injective
      rw [compatible, rationalEquivalence.apply_symm_apply, equivalence.apply_symm_apply]
      exact equality.symm
    have rationalEquality := unique (rationalEquivalence.symm other)
      (by
        change rationalAdele (rationalEquivalence.symm other) + equivalence.symm value ∈ _
        rw [representativeEquality]
        exact membership')
    exact (rationalEquivalence.apply_symm_apply other).symm.trans
      (congrArg rationalEquivalence rationalEquality)

theorem integral_equiv (equivalence : Adeles ≃ᵐ Adeles)
    (preserves : MeasurePreserving equivalence adeleMeasure adeleMeasure)
    (rationalEquivalence : ℚ ≃+ ℚ)
    (compatible : ∀ rational value, equivalence (rationalAdele rational + value) =
      rationalAdele (rationalEquivalence rational) + equivalence value)
    (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value) :
    (∫ value in additiveDomain, function (equivalence value) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
  rw [← preserves.setIntegral_image_emb equivalence.measurableEmbedding]
  exact (fundamental_image equivalence rationalEquivalence compatible).setIntegral_eq
    additiveDomain_fundamental periodic

theorem integrableOn_equiv (equivalence : Adeles ≃ᵐ Adeles)
    (preserves : MeasurePreserving equivalence adeleMeasure adeleMeasure)
    (rationalEquivalence : ℚ ≃+ ℚ)
    (compatible : ∀ rational value, equivalence (rationalAdele rational + value) =
      rationalAdele (rationalEquivalence rational) + equivalence value)
    (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value) :
    IntegrableOn (fun value => function (equivalence value)) additiveDomain adeleMeasure ↔
      IntegrableOn function additiveDomain adeleMeasure := by
  exact (preserves.integrableOn_image equivalence.measurableEmbedding
    (f := function) (s := additiveDomain)).symm.trans
      ((fundamental_image equivalence rationalEquivalence compatible).integrableOn_iff
        additiveDomain_fundamental periodic)

def translationEquiv (shift : Adeles) : Adeles ≃ᵐ Adeles :=
  (Homeomorph.addRight shift).toMeasurableEquiv

theorem integral_translate (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (shift : Adeles) :
    (∫ value in additiveDomain, function (value + shift) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
  apply integral_equiv (translationEquiv shift) (measurePreserving_add_right adeleMeasure shift)
    (AddEquiv.refl ℚ) _ function periodic
  intro rational value
  exact add_assoc _ _ _

def rationalScaling (unit : ℚˣ) : ℚ ≃+ ℚ where
  toFun value := unit.val * value
  invFun value := unit.inv * value
  left_inv value := by
    change unit.inv * (unit.val * value) = value
    rw [← mul_assoc, unit.inv_val, one_mul]
  right_inv value := by
    change unit.val * (unit.inv * value) = value
    rw [← mul_assoc, unit.val_inv, one_mul]
  map_add' := mul_add unit.val

def scalingEquiv (unit : ℚˣ) : Adeles ≃ᵐ Adeles :=
  (ContinuousAddEquiv.mulLeft (Units.map rationalAdele unit)).toHomeomorph.toMeasurableEquiv

theorem scalingEquiv_apply (unit : ℚˣ) (value : Adeles) :
    scalingEquiv unit value = rationalAdele unit.val * value := rfl

theorem scaling_preserves (unit : ℚˣ) :
    MeasurePreserving (scalingEquiv unit) adeleMeasure adeleMeasure := by
  refine ⟨(scalingEquiv unit).measurable, ?_⟩
  have scaled := addEquivAddHaarChar_smul_map adeleMeasure
    (ContinuousAddEquiv.mulLeft (Units.map rationalAdele unit))
  change adeleNorm (Units.map rationalAdele unit) •
    Measure.map (scalingEquiv unit) adeleMeasure = adeleMeasure at scaled
  rw [RationalNorm.rational_norm, one_smul] at scaled
  exact scaled

theorem scaling_compatible (unit : ℚˣ) (rational : ℚ) (value : Adeles) :
    scalingEquiv unit (rationalAdele rational + value) =
      rationalAdele (rationalScaling unit rational) + scalingEquiv unit value := by
  change rationalAdele unit.val * (rationalAdele rational + value) =
    rationalAdele (unit.val * rational) + rationalAdele unit.val * value
  rw [map_mul, mul_add]

theorem integral_rational_mul (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (unit : ℚˣ) :
    (∫ value in additiveDomain, function (rationalAdele unit.val * value) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure :=
  integral_equiv (scalingEquiv unit) (scaling_preserves unit)
    (rationalScaling unit) (scaling_compatible unit) function periodic

theorem integral_affine (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (unit : ℚˣ) (shift : Adeles) :
    (∫ value in additiveDomain,
      function (rationalAdele unit.val * value + shift) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
  rw [integral_rational_mul (fun value => function (value + shift))
    (fun rational value => by rw [add_assoc, periodic]), integral_translate function periodic]

theorem integrableOn_affine (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (unit : ℚˣ) (shift : Adeles) :
    IntegrableOn (fun value => function (rationalAdele unit.val * value + shift))
      additiveDomain adeleMeasure ↔ IntegrableOn function additiveDomain adeleMeasure := by
  change IntegrableOn
    (fun value => (fun x => function (x + shift)) (scalingEquiv unit value))
      additiveDomain adeleMeasure ↔ _
  rw [integrableOn_equiv (scalingEquiv unit) (scaling_preserves unit)
    (rationalScaling unit) (scaling_compatible unit) (fun value => function (value + shift))
    (fun rational value => by rw [add_assoc, periodic])]
  exact integrableOn_equiv (translationEquiv shift)
    (measurePreserving_add_right adeleMeasure shift) (AddEquiv.refl ℚ)
      (fun _ _ => add_assoc _ _ _) function periodic

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PeriodicIntegral
