module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceUnitEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finitePlaceSplitDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem finiteAtPlaceScalar_continuous (place : FinitePlace) : Continuous (finiteAtPlaceScalar place) :=
  restrictedProduct_continuous_single (fun place : FinitePlace => place.adicCompletionIntegers ℚ) place

def finiteAtPlaceAdd (place : FinitePlace) : place.adicCompletion ℚ →+ FiniteAdeles where
  toFun := finiteAtPlaceScalar place
  map_zero' := by
    unfold finiteAtPlaceScalar
    exact RestrictedProduct.single_zero _ _
  map_add' first second := by
    unfold finiteAtPlaceScalar
    exact RestrictedProduct.single_add _ _ first second

abbrev FiniteAwayPlace (place : FinitePlace) := (finiteEvaluation place).toAddMonoidHom.ker

def finiteAwayPlace (place : FinitePlace) (value : FiniteAdeles) : FiniteAwayPlace place :=
  ⟨value - finiteAtPlaceAdd place (finiteEvaluation place value), by
    change finiteEvaluation place (value - finiteAtPlaceScalar place (finiteEvaluation place value)) = 0
    rw [map_sub, finiteAtPlaceScalar_same, sub_self]⟩

def finitePlaceSplit (place : FinitePlace) : FiniteAdeles ≃ₜ+ (place.adicCompletion ℚ × FiniteAwayPlace place) where
  toFun value := (finiteEvaluation place value, finiteAwayPlace place value)
  invFun pair := finiteAtPlaceAdd place pair.1 + pair.2.val
  left_inv value := by
    change finiteAtPlaceAdd place (finiteEvaluation place value) +
      (value - finiteAtPlaceAdd place (finiteEvaluation place value)) = value
    abel
  right_inv pair := by
    obtain ⟨localValue, awayValue, awayZero⟩ := pair
    have away_eq : finiteEvaluation place awayValue = 0 := awayZero
    have local_eq : finiteEvaluation place (finiteAtPlaceAdd place localValue + awayValue) = localValue := by
      rw [map_add, away_eq, add_zero]
      exact finiteAtPlaceScalar_same _ _
    apply Prod.ext local_eq
    apply Subtype.ext
    change finiteAtPlaceAdd place localValue + awayValue -
      finiteAtPlaceAdd place (finiteEvaluation place (finiteAtPlaceAdd place localValue + awayValue)) = awayValue
    rw [local_eq]
    abel
  map_add' first second := by
    apply Prod.ext (map_add (finiteEvaluation place) first second)
    apply Subtype.ext
    change first + second - finiteAtPlaceAdd place (finiteEvaluation place (first + second)) =
      (first - finiteAtPlaceAdd place (finiteEvaluation place first)) +
        (second - finiteAtPlaceAdd place (finiteEvaluation place second))
    rw [map_add, map_add]
    abel
  continuous_toFun := (RestrictedProduct.continuous_eval place).prodMk
    ((continuous_id.sub ((finiteAtPlaceScalar_continuous place).comp
      (RestrictedProduct.continuous_eval place))).subtype_mk _)
  continuous_invFun := ((finiteAtPlaceScalar_continuous place).comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

theorem finitePlaceSplit_fst (place : FinitePlace) (value : FiniteAdeles) :
    (finitePlaceSplit place value).1 = finiteEvaluation place value := rfl

theorem finitePlaceSplit_symm (place : FinitePlace) (pair : place.adicCompletion ℚ × FiniteAwayPlace place) :
    (finitePlaceSplit place).symm pair = finiteAtPlaceScalar place pair.1 + pair.2.val := rfl

def finiteCompletionPadicAddEquiv (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    place.adicCompletion ℚ ≃ₜ+ ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] where
  toAddEquiv := (finiteCompletionPadicEquiv place).toAddEquiv
  continuous_toFun := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).continuous
  continuous_invFun := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).symm.continuous

end TernaryPeriodPolynomials.SphericalDetection.Helpers
