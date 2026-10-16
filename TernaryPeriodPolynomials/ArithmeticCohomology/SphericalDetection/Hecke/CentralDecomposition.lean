module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.CentralRational

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicHeckeRepresentative_det {prime : ℕ} [Fact prime.Prime] (index : Option (Fin prime)) :
    GeneralLinearGroup.det (padicHeckeRepresentative index) = padicPrimePowerUnit 1 := by
  apply Units.ext
  cases index <;>
    simp [padicHeckeRepresentative, binaryHeckeRepresentative, binaryHeckeDilate, binaryHeckeTranslate,
      GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, padicPrimePowerUnit]

theorem binaryHeckeRepresentative_det_positive (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    0 < (GeneralLinearGroup.det (binaryHeckeRepresentative prime index)).val := by
  cases index <;>
    simpa [binaryHeckeRepresentative, binaryHeckeDilate, binaryHeckeTranslate,
      GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using
      (show (0 : ℚ) < prime.val from by exact_mod_cast prime.property.pos)

theorem binaryHeckeCentral_decomposition (place : FinitePlace)
    (index : Option (Fin (Rat.HeightOneSpectrum.primesEquiv place).val)) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    Units.map (algebraMap ℚ FiniteAdeles) (GeneralLinearGroup.det
        (binaryHeckeRepresentative (Rat.HeightOneSpectrum.primesEquiv place) index)) =
      Units.map integralEmbedding (GeneralLinearGroup.det
          (binaryHeckeOutsideCompact (Rat.HeightOneSpectrum.primesEquiv place) index)) *
        finiteAtPadicUnit place (padicPrimePowerUnit 1) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have factor :
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
          (binaryHeckeRepresentative (Rat.HeightOneSpectrum.primesEquiv place) index) =
        GeneralLinearGroup.map integralEmbedding
            (binaryHeckeOutsideCompact (Rat.HeightOneSpectrum.primesEquiv place) index) *
          finiteAtPadicGL 2 place (padicHeckeRepresentative index) := by
    rw [← binaryHeckeLocalized_eq_padicRepresentative, binaryHeckeLocalized, mul_inv_cancel_left]
  have determinant := congrArg (GeneralLinearGroup.det (n := Fin 2)) factor
  rw [map_mul, generalLinearGroup_det_map, generalLinearGroup_det_map,
    finiteAtPadicGL_det, padicHeckeRepresentative_det] at determinant
  exact determinant

end TernaryPeriodPolynomials.SphericalDetection.Helpers
