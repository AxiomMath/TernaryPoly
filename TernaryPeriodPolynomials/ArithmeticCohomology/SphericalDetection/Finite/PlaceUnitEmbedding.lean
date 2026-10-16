module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.LocalPadicValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finiteUnitPlaceDecidableEq : DecidableEq FinitePlace := Classical.decEq _

def finiteAtPlaceMultiplicative (place : FinitePlace) : place.adicCompletion ℚ →* FiniteAdeles where
  toFun := RestrictedProduct.mulSingle (fun place : FinitePlace => place.adicCompletionIntegers ℚ) place
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' := RestrictedProduct.mulSingle_mul _ _

def finiteAtPlaceUnit (place : FinitePlace) : (place.adicCompletion ℚ)ˣ →* FiniteAdelesˣ :=
  Units.map (finiteAtPlaceMultiplicative place)

theorem finiteAtPlaceUnit_same (place : FinitePlace) (unit : (place.adicCompletion ℚ)ˣ) :
    Units.map (finiteEvaluation place).toMonoidHom (finiteAtPlaceUnit place unit) = unit := by
  apply Units.ext
  exact RestrictedProduct.mulSingle_eq_same (fun place : FinitePlace => place.adicCompletionIntegers ℚ) place unit.val

theorem finiteAtPlaceUnit_away (place : FinitePlace) (unit : (place.adicCompletion ℚ)ˣ)
    (other : FinitePlace) (away : other ≠ place) :
    Units.map (finiteEvaluation other).toMonoidHom (finiteAtPlaceUnit place unit) = 1 := by
  apply Units.ext
  exact RestrictedProduct.mulSingle_eq_of_ne (fun place : FinitePlace => place.adicCompletionIntegers ℚ) unit.val away

theorem finiteAtPlaceGL_det (dimension : ℕ) (place : FinitePlace)
    (matrix : GeneralLinearGroup (Fin dimension) (place.adicCompletion ℚ)) :
    GeneralLinearGroup.det (finiteAtPlaceGL dimension place matrix) =
      finiteAtPlaceUnit place (GeneralLinearGroup.det matrix) := by
  apply Units.ext
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro other
  by_cases same : other = place
  · subst other
    have equality := congrArg (fun matrix : GeneralLinearGroup (Fin dimension) (place.adicCompletion ℚ) =>
      (GeneralLinearGroup.det matrix).val) (finiteAtPlaceGL_same dimension place matrix)
    rw [generalLinearGroup_det_map] at equality
    exact equality.trans (congrArg Units.val (finiteAtPlaceUnit_same place (GeneralLinearGroup.det matrix))).symm
  · have equality := congrArg (fun matrix : GeneralLinearGroup (Fin dimension) (other.adicCompletion ℚ) =>
      (GeneralLinearGroup.det matrix).val) (finiteAtPlaceGL_away dimension place matrix other same)
    rw [generalLinearGroup_det_map, map_one] at equality
    exact equality.trans (congrArg Units.val (finiteAtPlaceUnit_away place (GeneralLinearGroup.det matrix) other same)).symm

theorem finiteAtPlaceGL_scalar (dimension : ℕ) (place : FinitePlace) (unit : (place.adicCompletion ℚ)ˣ) :
    finiteAtPlaceGL dimension place (GeneralLinearGroup.scalar (Fin dimension) unit) =
      GeneralLinearGroup.scalar (Fin dimension) (finiteAtPlaceUnit place unit) := by
  apply finiteGeneralLinearGroup_ext
  intro other
  rw [GeneralLinearGroup.map_scalar]
  by_cases same : other = place
  · subst other
    rw [finiteAtPlaceGL_same]
    exact (congrArg (GeneralLinearGroup.scalar (Fin dimension)) (finiteAtPlaceUnit_same place unit)).symm
  · rw [finiteAtPlaceGL_away _ _ _ other same]
    exact ((congrArg (GeneralLinearGroup.scalar (Fin dimension)) (finiteAtPlaceUnit_away place unit other same)).trans
      (GeneralLinearGroup.scalar (Fin dimension)).map_one).symm

def finiteAtPadicUnit (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ →* FiniteAdelesˣ :=
  (finiteAtPlaceUnit place).comp (Units.map (finiteCompletionPadicEquiv place).symm.toMonoidHom)

theorem finiteAtPadicGL_det (dimension : ℕ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ matrix : GeneralLinearGroup (Fin dimension) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      GeneralLinearGroup.det (finiteAtPadicGL dimension place matrix) =
        finiteAtPadicUnit place (GeneralLinearGroup.det matrix) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix
  change GeneralLinearGroup.det (finiteAtPlaceGL dimension place _) = _
  rw [finiteAtPlaceGL_det, generalLinearGroup_det_map]
  rfl

theorem finiteAtPadicGL_scalar (dimension : ℕ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ unit : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ,
      finiteAtPadicGL dimension place (GeneralLinearGroup.scalar (Fin dimension) unit) =
        GeneralLinearGroup.scalar (Fin dimension) (finiteAtPadicUnit place unit) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro unit
  change finiteAtPlaceGL dimension place (GeneralLinearGroup.map _ (GeneralLinearGroup.scalar (Fin dimension) unit)) = _
  rw [GeneralLinearGroup.map_scalar, finiteAtPlaceGL_scalar]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
