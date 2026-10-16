module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.AwayThreePlaceMeasures

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteAwayThreePadicSplit (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    FiniteAwayThree ≃ₜ+ (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayThreePlace place) where
  toAddEquiv := (finiteAwayThreePlaceSplit place distinct).toAddEquiv.trans
    ((finiteCompletionPadicAddEquiv place).toAddEquiv.prodCongr (AddEquiv.refl _))
  continuous_toFun := ((finiteCompletionPadicAddEquiv place).continuous.prodMap continuous_id).comp
    (finiteAwayThreePlaceSplit place distinct).continuous
  continuous_invFun := (finiteAwayThreePlaceSplit place distinct).symm.continuous.comp
    ((finiteCompletionPadicAddEquiv place).symm.continuous.prodMap continuous_id)

theorem finiteAwayThreePadicSplit_symm_val (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayThreePlace place,
      ((finiteAwayThreePadicSplit place distinct).symm pair).val =
        finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm pair.1) + pair.2.val.val := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  exact finiteAwayThreePlaceSplit_symm_val place distinct ((finiteCompletionPadicEquiv place).symm pair.1, pair.2)

theorem finiteAwayThreePadicSplit_measurePreserving (place : FinitePlace) (distinct : place ≠ placeThree) :
    MeasurePreserving (finiteAwayThreePadicSplit place distinct) finiteAwayThreeMeasure
      ((finitePadicMeasure place).prod (finiteAwayThreePlaceMeasure place)) :=
  ((finiteCompletionPadic_measurePreserving place).prod (MeasurePreserving.id _)).comp
    (finiteAwayThreePlaceSplit_measurePreserving place distinct)

theorem finiteAwayThreePadicSplit_symm_measurePreserving (place : FinitePlace) (distinct : place ≠ placeThree) :
    MeasurePreserving (finiteAwayThreePadicSplit place distinct).symm
      ((finitePadicMeasure place).prod (finiteAwayThreePlaceMeasure place)) finiteAwayThreeMeasure :=
  MeasurePreserving.symm (finiteAwayThreePadicSplit place distinct).toHomeomorph.toMeasurableEquiv
    (finiteAwayThreePadicSplit_measurePreserving place distinct)

def finiteAwayThreePadicRadicalJoin (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ((ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ×
      (FiniteAwayThreePlace place × FiniteAwayThreePlace place)) ≃ₜ (FiniteAwayThree × FiniteAwayThree) :=
  (Homeomorph.prodProdProdComm _ _ _ _).trans
    ((finiteAwayThreePadicSplit place distinct).symm.toHomeomorph.prodCongr
      (finiteAwayThreePadicSplit place distinct).symm.toHomeomorph)

theorem finiteAwayThreePadicRadicalJoin_apply (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ×
      (FiniteAwayThreePlace place × FiniteAwayThreePlace place),
      finiteAwayThreePadicRadicalJoin place distinct pair =
        ((finiteAwayThreePadicSplit place distinct).symm (pair.1.1, pair.2.1),
          (finiteAwayThreePadicSplit place distinct).symm (pair.1.2, pair.2.2)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  rfl

theorem finiteAwayThreePadicRadicalJoin_measurePreserving (place : FinitePlace) (distinct : place ≠ placeThree) :
    MeasurePreserving (finiteAwayThreePadicRadicalJoin place distinct)
      (((finitePadicMeasure place).prod (finitePadicMeasure place)).prod
        ((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
  ((finiteAwayThreePadicSplit_symm_measurePreserving place distinct).prod
    (finiteAwayThreePadicSplit_symm_measurePreserving place distinct)).comp
    (measurePreserving_prodTranspose (finitePadicMeasure place) (finitePadicMeasure place)
      (finiteAwayThreePlaceMeasure place) (finiteAwayThreePlaceMeasure place))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
