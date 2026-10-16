module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicIntegralSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteAwayThreeEvaluation (place : FinitePlace) : FiniteAwayThree →+ place.adicCompletion ℚ :=
  (finiteEvaluation place).toAddMonoidHom.comp finiteThree.toAddMonoidHom.ker.subtype

abbrev FiniteAwayThreePlace (place : FinitePlace) := (finiteAwayThreeEvaluation place).ker

theorem finiteAtPlaceScalar_three (place : FinitePlace) (distinct : place ≠ placeThree)
    (value : place.adicCompletion ℚ) : finiteThree (finiteAtPlaceScalar place value) = 0 := by
  change threeCompletionEquiv (finiteEvaluation placeThree (finiteAtPlaceScalar place value)) = 0
  rw [finiteAtPlaceScalar_away _ _ _ distinct.symm, map_zero]

def finiteAwayThreeAtPlace (place : FinitePlace) (distinct : place ≠ placeThree) :
    place.adicCompletion ℚ →+ FiniteAwayThree where
  toFun value := ⟨finiteAtPlaceScalar place value, finiteAtPlaceScalar_three place distinct value⟩
  map_zero' := Subtype.ext (finiteAtPlaceAdd place).map_zero
  map_add' first second := Subtype.ext ((finiteAtPlaceAdd place).map_add first second)

theorem finiteAwayThreeAtPlace_continuous (place : FinitePlace) (distinct : place ≠ placeThree) :
    Continuous (finiteAwayThreeAtPlace place distinct) :=
  (finiteAtPlaceScalar_continuous place).subtype_mk _

theorem finiteAwayThreeEvaluation_continuous (place : FinitePlace) : Continuous (finiteAwayThreeEvaluation place) :=
  (RestrictedProduct.continuous_eval place).comp continuous_subtype_val

theorem finiteAwayThreeEvaluation_atPlace (place : FinitePlace) (distinct : place ≠ placeThree)
    (value : place.adicCompletion ℚ) :
    finiteAwayThreeEvaluation place (finiteAwayThreeAtPlace place distinct value) = value :=
  finiteAtPlaceScalar_same place value

def finiteAwayThreeRemainder (place : FinitePlace) (distinct : place ≠ placeThree)
    (value : FiniteAwayThree) : FiniteAwayThreePlace place :=
  ⟨value - finiteAwayThreeAtPlace place distinct (finiteAwayThreeEvaluation place value), by
    change finiteAwayThreeEvaluation place (value - finiteAwayThreeAtPlace place distinct
      (finiteAwayThreeEvaluation place value)) = 0
    rw [map_sub, finiteAwayThreeEvaluation_atPlace, sub_self]⟩

def finiteAwayThreePlaceSplit (place : FinitePlace) (distinct : place ≠ placeThree) :
    FiniteAwayThree ≃ₜ+ (place.adicCompletion ℚ × FiniteAwayThreePlace place) where
  toFun value := (finiteAwayThreeEvaluation place value, finiteAwayThreeRemainder place distinct value)
  invFun pair := finiteAwayThreeAtPlace place distinct pair.1 + pair.2.val
  left_inv value := by
    change finiteAwayThreeAtPlace place distinct (finiteAwayThreeEvaluation place value) +
      (value - finiteAwayThreeAtPlace place distinct (finiteAwayThreeEvaluation place value)) = value
    abel
  right_inv pair := by
    obtain ⟨localValue, awayValue, awayZero⟩ := pair
    have away_eq : finiteAwayThreeEvaluation place awayValue = 0 := awayZero
    have local_eq : finiteAwayThreeEvaluation place (finiteAwayThreeAtPlace place distinct localValue + awayValue) =
        localValue := by
      rw [map_add, away_eq, add_zero, finiteAwayThreeEvaluation_atPlace]
    apply Prod.ext local_eq
    apply Subtype.ext
    change finiteAwayThreeAtPlace place distinct localValue + awayValue -
      finiteAwayThreeAtPlace place distinct
        (finiteAwayThreeEvaluation place (finiteAwayThreeAtPlace place distinct localValue + awayValue)) = awayValue
    rw [local_eq]
    abel
  map_add' first second := by
    apply Prod.ext (map_add (finiteAwayThreeEvaluation place) first second)
    apply Subtype.ext
    change first + second - finiteAwayThreeAtPlace place distinct (finiteAwayThreeEvaluation place (first + second)) =
      (first - finiteAwayThreeAtPlace place distinct (finiteAwayThreeEvaluation place first)) +
        (second - finiteAwayThreeAtPlace place distinct (finiteAwayThreeEvaluation place second))
    rw [map_add, map_add]
    abel
  continuous_toFun := (finiteAwayThreeEvaluation_continuous place).prodMk
    ((continuous_id.sub ((finiteAwayThreeAtPlace_continuous place distinct).comp
      (finiteAwayThreeEvaluation_continuous place))).subtype_mk _)
  continuous_invFun := ((finiteAwayThreeAtPlace_continuous place distinct).comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

theorem finiteAwayThreePlaceSplit_symm_val (place : FinitePlace) (distinct : place ≠ placeThree)
    (pair : place.adicCompletion ℚ × FiniteAwayThreePlace place) :
    ((finiteAwayThreePlaceSplit place distinct).symm pair).val =
      finiteAtPlaceScalar place pair.1 + pair.2.val.val := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
