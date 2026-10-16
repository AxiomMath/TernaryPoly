module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteAtPlaceUnit_mul_scalar (place : FinitePlace) (unit : (place.adicCompletion ℚ)ˣ)
    (value : place.adicCompletion ℚ) :
    (finiteAtPlaceUnit place unit).val * finiteAtPlaceScalar place value =
      finiteAtPlaceScalar place (unit.val * value) := by
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro other
  change finiteEvaluation other ((finiteAtPlaceUnit place unit).val * finiteAtPlaceScalar place value) =
    finiteEvaluation other (finiteAtPlaceScalar place (unit.val * value))
  rw [map_mul]
  by_cases same : other = place
  · subst other
    rw [finiteAtPlaceScalar_same, finiteAtPlaceScalar_same]
    exact congrArg (fun unit : (place.adicCompletion ℚ)ˣ => unit.val * value) (finiteAtPlaceUnit_same place unit)
  · rw [finiteAtPlaceScalar_away _ _ other same, finiteAtPlaceScalar_away _ _ other same, mul_zero]

theorem finiteAtPlaceUnit_mul_away (place : FinitePlace) (unit : (place.adicCompletion ℚ)ˣ)
    (value : FiniteAwayPlace place) : (finiteAtPlaceUnit place unit).val * value.val = value.val := by
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro other
  change finiteEvaluation other (_ * _) = finiteEvaluation other _
  rw [map_mul]
  by_cases same : other = place
  · subst other
    have zero : finiteEvaluation place value.val = 0 := value.property
    rw [zero, mul_zero]
  · have one := congrArg Units.val (finiteAtPlaceUnit_away place unit other same)
    change finiteEvaluation other (finiteAtPlaceUnit place unit).val = 1 at one
    rw [one, one_mul]

theorem finiteAtPlaceUnit_mul_split (place : FinitePlace) (unit : (place.adicCompletion ℚ)ˣ)
    (pair : place.adicCompletion ℚ × FiniteAwayPlace place) :
    (finiteAtPlaceUnit place unit).val * (finitePlaceSplit place).symm pair =
      (finitePlaceSplit place).symm (unit.val * pair.1, pair.2) := by
  rw [finitePlaceSplit_symm, finitePlaceSplit_symm, mul_add,
    finiteAtPlaceUnit_mul_scalar, finiteAtPlaceUnit_mul_away]

theorem finiteAtPadicUnit_mul_split (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (unit : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ)
      (pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayPlace place),
      (finiteAtPadicUnit place unit).val * (finitePadicSplit place).symm pair =
        (finitePadicSplit place).symm (unit.val * pair.1, pair.2) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro unit pair
  rw [finitePadicSplit_symm, finitePadicSplit_symm, map_mul]
  change (finiteAtPlaceUnit place (Units.map (finiteCompletionPadicEquiv place).symm.toMonoidHom unit)).val * _ = _
  rw [mul_add, finiteAtPlaceUnit_mul_scalar, finiteAtPlaceUnit_mul_away]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
