module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem measurePreserving_prodLeftComm {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (first : Measure A) (second : Measure B) (third : Measure C)
    [SFinite first] [SFinite second] [SFinite third] :
    MeasurePreserving (fun pair : A × (B × C) => (pair.2.1, pair.1, pair.2.2))
      (first.prod (second.prod third)) (second.prod (first.prod third)) := by
  have associate := (measurePreserving_prodAssoc first second third).symm MeasurableEquiv.prodAssoc
  have swap := (Measure.measurePreserving_swap (μ := first) (ν := second)).prod
    (MeasurePreserving.id third)
  exact (measurePreserving_prodAssoc second first third).comp (swap.comp associate)

theorem measurePreserving_prodTranspose {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (first : Measure A) (second : Measure B) (third : Measure C) (fourth : Measure D)
    [SFinite first] [SFinite second] [SFinite third] [SFinite fourth] :
    MeasurePreserving (fun pair : (A × B) × (C × D) =>
      ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2)))
      ((first.prod second).prod (third.prod fourth))
      ((first.prod third).prod (second.prod fourth)) := by
  have start := measurePreserving_prodAssoc first second (third.prod fourth)
  have middle := (MeasurePreserving.id first).prod
    (measurePreserving_prodLeftComm second third fourth)
  have finish := (measurePreserving_prodAssoc first third (second.prod fourth)).symm
    MeasurableEquiv.prodAssoc
  exact finish.comp (middle.comp start)

abbrev AdelesAwayThree := ℝ × FiniteAwayThree

def adeleAwayThreeMeasure : Measure AdelesAwayThree :=
  (volume : Measure ℝ).prod finiteAwayThreeMeasure

instance adeleAwayThreeMeasure_sigmaFinite : SigmaFinite adeleAwayThreeMeasure :=
  inferInstanceAs (SigmaFinite ((volume : Measure ℝ).prod finiteAwayThreeMeasure))

def adeleThreeJoin : (ℚ_[3] × AdelesAwayThree) ≃ₜ Adeles :=
  ((Homeomorph.prodAssoc ℚ_[3] ℝ FiniteAwayThree).symm.trans
    ((Homeomorph.prodComm ℚ_[3] ℝ).prodCongr (Homeomorph.refl FiniteAwayThree))).trans
    ((Homeomorph.prodAssoc ℝ ℚ_[3] FiniteAwayThree).trans
      ((Homeomorph.refl ℝ).prodCongr finiteThreeSplit.symm.toHomeomorph))

theorem adeleThreeJoin_apply (pair : ℚ_[3] × AdelesAwayThree) :
    adeleThreeJoin pair = (pair.2.1, finiteAtThreeScalar pair.1 + pair.2.2.val) := rfl

local instance normalizedRadicalThreeHaar : normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

theorem adeleThreeJoin_measurePreserving :
    MeasurePreserving adeleThreeJoin
      (normalizedLocalThreeMeasure.prod adeleAwayThreeMeasure) adeleMeasure := by
  have rearrange := measurePreserving_prodLeftComm normalizedLocalThreeMeasure
    (volume : Measure ℝ) finiteAwayThreeMeasure
  have combine := (MeasurePreserving.id (volume : Measure ℝ)).prod
    finiteThreeSplit_symm_measurePreserving
  exact combine.comp rearrange

def radicalAwayThreeMeasure : Measure (AdelesAwayThree × AdelesAwayThree) :=
  adeleAwayThreeMeasure.prod adeleAwayThreeMeasure

instance radicalAwayThreeMeasure_sigmaFinite : SigmaFinite radicalAwayThreeMeasure :=
  inferInstanceAs (SigmaFinite (adeleAwayThreeMeasure.prod adeleAwayThreeMeasure))

def radicalThreeJoin : ((ℚ_[3] × ℚ_[3]) × (AdelesAwayThree × AdelesAwayThree)) ≃ₜ
    (Adeles × Adeles) :=
  (Homeomorph.prodProdProdComm ℚ_[3] ℚ_[3] AdelesAwayThree AdelesAwayThree).trans
    (adeleThreeJoin.prodCongr adeleThreeJoin)

theorem radicalThreeJoin_apply
    (pair : (ℚ_[3] × ℚ_[3]) × (AdelesAwayThree × AdelesAwayThree)) :
    radicalThreeJoin pair =
      ((pair.2.1.1, finiteAtThreeScalar pair.1.1 + pair.2.1.2.val),
       (pair.2.2.1, finiteAtThreeScalar pair.1.2 + pair.2.2.2.val)) := rfl

theorem radicalThreeJoin_measurePreserving :
    MeasurePreserving radicalThreeJoin
      ((normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure).prod radicalAwayThreeMeasure)
      radicalMeasure := by
  have rearrange := measurePreserving_prodTranspose normalizedLocalThreeMeasure
    normalizedLocalThreeMeasure adeleAwayThreeMeasure adeleAwayThreeMeasure
  exact (adeleThreeJoin_measurePreserving.prod adeleThreeJoin_measurePreserving).comp rearrange

theorem radicalIntegral_three_fubini {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (integrand : Adeles × Adeles → E) (integrable : Integrable integrand radicalMeasure) :
    (∫ parameter, integrand parameter ∂radicalMeasure) =
      ∫ away, ∫ localParameter,
        integrand (radicalThreeJoin (localParameter, away))
        ∂(normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure) ∂radicalAwayThreeMeasure := by
  have lifted := radicalThreeJoin_measurePreserving.integrable_comp_of_integrable integrable
  rw [← radicalThreeJoin_measurePreserving.integral_comp radicalThreeJoin.measurableEmbedding integrand]
  exact integral_prod_symm _ lifted

end TernaryPeriodPolynomials.SphericalDetection.Helpers
