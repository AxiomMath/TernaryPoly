module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeTwo

@[expose] public section


/-!
# Explicit prime-power factors of the plane weights

For a prime `p ≠ 3`, the away-from-three idele `sAd p` has adelic norm `p⁻¹`. Hence the scalar
factor of the weight `W(B, p)` is `χ(sAd p) · p^{2 e}`, and the determinant factor of
`W(diag(p,1), s)` is `p^{-planeExp}`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

theorem Int3_prime (hp : p.Prime) : Int3 ((pUnit hp : ℚˣ) : ℚ) := by
  rw [pUnit_val]
  exact_mod_cast Int3_int (p : ℤ)

theorem Int3_prime_inv (hp : p.Prime) (h3 : p ≠ 3) : Int3 ((pUnit hp : ℚˣ) : ℚ)⁻¹ := by
  have hnd : ¬ 3 ∣ p := by
    intro h
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have h1 : ‖((p : ℚ) : ℚ_[3])‖ = 1 := by
    rw [Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff p).mpr hnd]
    simp
  unfold Int3
  rw [pUnit_val, Rat.cast_inv, norm_inv, h1, inv_one]

theorem adeleNorm_sAd_prime (hp : p.Prime) (h3 : p ≠ 3) :
    (adeleNorm (sAd (pUnit hp)) : ℝ) = (p : ℝ)⁻¹ := by
  rw [adeleNorm_sAd (Int3_prime hp) (Int3_prime_inv hp h3), pUnit_val]
  simp

theorem normPower_sAd_prime (hp : p.Prime) (h3 : p ≠ 3) (z : ℂ) :
    normPower (sAd (pUnit hp)) z = Complex.exp (-(z * (Real.log p : ℂ))) := by
  rw [normPower, adeleNorm_sAd_prime hp h3, Real.log_inv]
  push_cast
  ring_nf

theorem det_dP (hp : p.Prime) : GeneralLinearGroup.det (dP hp) = pUnit hp := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, pUnit_val]
  change (diagonal ![(p : ℚ), 1]).det = p
  rw [det_diagonal, Fin.prod_univ_two]
  simp

/-- **The scalar factor at `s = p`.** -/
theorem ratPlaneWeight_prime_scalar (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (B : GeneralLinearGroup (Fin 2) ℚ) :
    ratPlaneWeight D B (pUnit hp) =
      D.chi.toMonoidHom (sAd (pUnit hp)) *
        Complex.exp (2 * inductionExponent .plane cohomologicalPoint * (Real.log p : ℂ)) *
        (normPower (GeneralLinearGroup.det (atFinite (Bo B))) (planeExp n) * omega D.cusp (Bo B)) := by
  simp only [ratPlaneWeight, planeWeight]
  rw [normPower_sAd_prime hp h3]
  ring_nf

/-- **The determinant factor of `diag(p, 1)`.** -/
theorem ratPlaneWeight_dP (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3) (s : ℚˣ) :
    ratPlaneWeight D (dP hp) s =
      D.chi.toMonoidHom (sAd s) * normPower (sAd s) (-2 * inductionExponent .plane cohomologicalPoint) *
        (Complex.exp (-(planeExp n * (Real.log p : ℂ))) * omega D.cusp (Bo (dP hp))) := by
  simp only [ratPlaneWeight, planeWeight]
  rw [det_atFinite_Bo, det_dP, normPower_sAd_prime hp h3]
  ring

end TernaryPeriodPolynomials.HeckeEigen.Satake
