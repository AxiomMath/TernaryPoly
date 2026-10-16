module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceIntegralEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteAtPadicGL (dimension : ℕ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup (Fin dimension) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] →*
      GeneralLinearGroup (Fin dimension) FiniteAdeles :=
  (finiteAtPlaceGL dimension place).comp (GeneralLinearGroup.map (finiteCompletionPadicEquiv place).symm.toRingHom)

theorem finiteAtPadicGL_same (dimension : ℕ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ matrix : GeneralLinearGroup (Fin dimension) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      GeneralLinearGroup.map (finitePadicEvaluation place) (finiteAtPadicGL dimension place matrix) = matrix := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix
  change GeneralLinearGroup.map (finiteCompletionPadicEquiv place).toRingHom
    (GeneralLinearGroup.map (finiteEvaluation place) (finiteAtPlaceGL dimension place
      (GeneralLinearGroup.map (finiteCompletionPadicEquiv place).symm.toRingHom matrix))) = matrix
  rw [finiteAtPlaceGL_same]
  apply Units.ext
  funext row column
  exact (finiteCompletionPadicEquiv place).apply_symm_apply _

theorem finiteAtPadicGL_away (dimension : ℕ) (place other : FinitePlace) (away : other ≠ place) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ matrix : GeneralLinearGroup (Fin dimension) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      GeneralLinearGroup.map (finiteEvaluation other) (finiteAtPadicGL dimension place matrix) = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix
  exact finiteAtPlaceGL_away dimension place _ other away

theorem finiteAtPadicGL_integral (dimension : ℕ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ matrix : GeneralLinearGroup (Fin dimension) ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      finiteAtPadicGL dimension place (GeneralLinearGroup.map PadicInt.Coe.ringHom matrix) ∈
        finiteIntegralGLLevel dimension := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix
  have square : GeneralLinearGroup.map (finiteCompletionPadicEquiv place).symm.toRingHom
      (GeneralLinearGroup.map PadicInt.Coe.ringHom matrix) =
    GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).toSubring.subtype
      (GeneralLinearGroup.map (finiteIntegralPadicEquiv place).symm.toRingHom matrix) := by
    apply Units.ext
    funext row column
    exact finitePadicEquiv_inverse_compatible place (matrix.val row column)
  change finiteAtPlaceGL dimension place _ ∈ _
  rw [square]
  exact finiteAtPlaceGL_integral dimension place _

theorem finiteAtPadicGL_injective (dimension : ℕ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    Function.Injective (finiteAtPadicGL dimension place) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro first second equal
  have evaluated := congrArg (GeneralLinearGroup.map (finitePadicEvaluation place)) equal
  simpa only [finiteAtPadicGL_same] using evaluated

end TernaryPeriodPolynomials.SphericalDetection.Helpers
