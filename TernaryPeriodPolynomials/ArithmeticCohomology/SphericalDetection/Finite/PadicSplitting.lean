module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicMeasures

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finitePadicSplit (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    FiniteAdeles ≃ₜ+ (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayPlace place) where
  toAddEquiv := (finitePlaceSplit place).toAddEquiv.trans
    ((finiteCompletionPadicAddEquiv place).toAddEquiv.prodCongr (AddEquiv.refl _))
  continuous_toFun := ((finiteCompletionPadicAddEquiv place).continuous.prodMap continuous_id).comp
    (finitePlaceSplit place).continuous
  continuous_invFun := (finitePlaceSplit place).symm.continuous.comp
    ((finiteCompletionPadicAddEquiv place).symm.continuous.prodMap continuous_id)

theorem finitePadicSplit_fst (place : FinitePlace) (value : FiniteAdeles) :
    (finitePadicSplit place value).1 = finitePadicEvaluation place value := rfl

theorem finitePadicSplit_symm (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayPlace place,
      (finitePadicSplit place).symm pair =
        finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm pair.1) + pair.2.val := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  rfl

theorem finitePadicSplit_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finitePadicSplit place) finiteMeasure
      ((finitePadicMeasure place).prod (finiteAwayPlaceMeasure place)) :=
  ((finiteCompletionPadic_measurePreserving place).prod (MeasurePreserving.id _)).comp
    (finitePlaceSplit_measurePreserving place)

theorem finitePadicSplit_symm_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finitePadicSplit place).symm
      ((finitePadicMeasure place).prod (finiteAwayPlaceMeasure place)) finiteMeasure :=
  MeasurePreserving.symm (finitePadicSplit place).toHomeomorph.toMeasurableEquiv
    (finitePadicSplit_measurePreserving place)

theorem finitePadicSplit_integral_iff (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayPlace place,
      (finitePadicSplit place).symm pair ∈ Set.range integralEmbedding ↔
        ‖pair.1‖ ≤ 1 ∧ pair.2.val ∈ Set.range integralEmbedding := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  change (finitePlaceSplit place).symm ((finiteCompletionPadicEquiv place).symm pair.1, pair.2) ∈
    Set.range integralEmbedding ↔ _
  rw [finitePlaceSplit_integral_iff, ← finiteCompletionPadic_integral_iff, RingEquiv.apply_symm_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
