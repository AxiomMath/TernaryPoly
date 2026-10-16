module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.LocalPadicIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finitePadicGeneralLinearGroup_ext {dimension : ℕ}
    (first second : GeneralLinearGroup (Fin dimension) FiniteAdeles)
    (equal : ∀ place : FinitePlace,
      letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
      GeneralLinearGroup.map (finitePadicEvaluation place) first =
        GeneralLinearGroup.map (finitePadicEvaluation place) second) : first = second := by
  apply finiteGeneralLinearGroup_ext
  intro place
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  apply Units.ext
  funext row column
  apply (finiteCompletionPadicEquiv place).injective
  exact congrArg (fun matrix : GeneralLinearGroup (Fin dimension) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] =>
    matrix.val row column) (equal place)

theorem finitePadicEvaluation_kernel (place : FinitePlace) (value : FiniteAwayPlace place) :
    finitePadicEvaluation place value.val = 0 := by
  have zero : finiteEvaluation place value.val = 0 := value.property
  change finiteCompletionPadicEquiv place (finiteEvaluation place value.val) = 0
  rw [zero, map_zero]

theorem finitePadicSplit_symm_same (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayPlace place,
      finitePadicEvaluation place ((finitePadicSplit place).symm pair) = pair.1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  exact congrArg Prod.fst ((finitePadicSplit place).apply_symm_apply pair)

theorem finitePadicSplit_symm_away (place other : FinitePlace) (distinct : other ≠ place) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × FiniteAwayPlace place,
      finitePadicEvaluation other ((finitePadicSplit place).symm pair) = finitePadicEvaluation other pair.2.val := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  rw [finitePadicSplit_symm]
  change finiteCompletionPadicEquiv other (finiteEvaluation other (_ + _)) =
    finiteCompletionPadicEquiv other (finiteEvaluation other pair.2.val)
  rw [map_add, finiteAtPlaceScalar_away _ _ other distinct, zero_add]

theorem finiteAtPadicGL_padic_away (dimension : ℕ) (place other : FinitePlace) (distinct : other ≠ place) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv other).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv other).property⟩
    ∀ matrix : GeneralLinearGroup (Fin dimension) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      GeneralLinearGroup.map (finitePadicEvaluation other) (finiteAtPadicGL dimension place matrix) = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let : Fact (Rat.HeightOneSpectrum.primesEquiv other).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv other).property⟩
  intro matrix
  change GeneralLinearGroup.map (finiteCompletionPadicEquiv other).toRingHom
    (GeneralLinearGroup.map (finiteEvaluation other) (finiteAtPadicGL dimension place matrix)) = 1
  rw [finiteAtPadicGL_away _ _ _ distinct, map_one]

theorem finitePadicPlaneCoordinates_split_block (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      (finitePadicPlaneCoordinates ((finitePadicSplit place).symm (localPair.1, awayPair.1))
        ((finitePadicSplit place).symm (localPair.2, awayPair.2))).block =
        (finitePadicPlaneCoordinates awayPair.1.val awayPair.2.val).block *
          finiteAtPadicGL 2 place (padicPlanePivotCoordinates localPair.1 localPair.2).block := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  apply finitePadicGeneralLinearGroup_ext
  intro other
  let : Fact (Rat.HeightOneSpectrum.primesEquiv other).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv other).property⟩
  rw [map_mul, finitePadicPlaneCoordinates_block, finitePadicPlaneCoordinates_block]
  by_cases same : other = place
  · subst other
    rw [finitePadicSplit_symm_same, finitePadicSplit_symm_same, finitePadicEvaluation_kernel,
      finitePadicEvaluation_kernel, finiteAtPadicGL_same,
      padicPlanePivotCoordinates_integral 0 0 (by simp) (by simp), one_mul]
  · rw [finitePadicSplit_symm_away _ _ same, finitePadicSplit_symm_away _ _ same,
      finiteAtPadicGL_padic_away _ _ _ same, mul_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
