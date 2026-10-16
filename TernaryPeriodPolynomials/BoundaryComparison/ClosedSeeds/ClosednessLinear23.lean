module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.AffineDeriv
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessChainRule

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`): per-coordinate affine normal form of `seedLinear`
along coordinates `2` and `3` (the two coordinates `seedTau` does read), decomposing
`seedLinear q = M0 q + seedTau q • M1 q` with `M0 q, M1 q` depending only on `q 0, q 1`
respectively (hence constant under updates to coordinate `2` or `3`), and the resulting closed
form of `coordPartial (fun q => coeff m (seedLinear q ^ n)) k p` for `k = 2, 3`, composing the
Master Lemma `coeff_affine_pow_hasDerivAt` with the chain rule through `seedTau`
(`hasDerivAt_comp_seedTau_two/three`). Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `seedLinear` in `M0 + τ • M1` normal form, with `M0 q := -X 0 + C (q 0 : ℂ) * X 2` and
`M1 q := X 1 - (q 1 : ℂ) • X 2` depending only on `q 0` and `q 1` respectively. -/
theorem seedLinear_eq_M0_add_tau_smul_M1 (q : Fin 5 → ℝ) :
    seedLinear q =
      (-X 0 + C (q 0 : ℂ) * X 2) + seedTau q • (X 1 - (q 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) := by
  simp only [seedLinear, MvPolynomial.smul_eq_C_mul, map_sub, map_mul]
  ring

theorem seedLinear_update2 (p : Fin 5 → ℝ) (s : ℝ) :
    seedLinear (Function.update p 2 s) =
      (-X 0 + C (p 0 : ℂ) * X 2) +
        seedTau (Function.update p 2 s) • (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) := by
  have h0 : ((Function.update p 2 s) 0 : ℝ) = p 0 := by simp
  have h1 : ((Function.update p 2 s) 1 : ℝ) = p 1 := by simp
  rw [seedLinear_eq_M0_add_tau_smul_M1, h0, h1]

theorem seedLinear_update3 (p : Fin 5 → ℝ) (s : ℝ) :
    seedLinear (Function.update p 3 s) =
      (-X 0 + C (p 0 : ℂ) * X 2) +
        seedTau (Function.update p 3 s) • (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) := by
  have h0 : ((Function.update p 3 s) 0 : ℝ) = p 0 := by simp
  have h1 : ((Function.update p 3 s) 1 : ℝ) = p 1 := by simp
  rw [seedLinear_eq_M0_add_tau_smul_M1, h0, h1]

/-- Closed form for `coordPartial (fun q => coeff m (seedLinear q ^ n)) 2 p`. -/
theorem coordPartial_seedLinear_pow_two (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    coordPartial (fun q => (seedLinear q ^ n).coeff m) 2 p =
      (n : ℂ) * (seedLinear p ^ (n - 1) * (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m := by
  unfold coordPartial
  have hfun : (fun s : ℝ => (seedLinear (Function.update p 2 s) ^ n).coeff m) =
      (fun s : ℝ => (((-X 0 + C (p 0 : ℂ) * X 2) +
            seedTau (Function.update p 2 s) • (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))) ^ n).coeff m) := by
    funext s; rw [seedLinear_update2]
  rw [hfun]
  have hM := coeff_affine_pow_hasDerivAt (-X 0 + C (p 0 : ℂ) * X 2)
      (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) n (seedTau p) m
  have hcomp := hasDerivAt_comp_seedTau_two p _ _ hM
  have hL : (-X 0 + C (p 0 : ℂ) * X 2) +
      seedTau p • (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) = seedLinear p :=
    (seedLinear_eq_M0_add_tau_smul_M1 p).symm
  rw [hL] at hcomp
  exact hcomp.deriv

/-- Closed form for `coordPartial (fun q => coeff m (seedLinear q ^ n)) 3 p`. -/
theorem coordPartial_seedLinear_pow_three (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    coordPartial (fun q => (seedLinear q ^ n).coeff m) 3 p =
      (n : ℂ) * (seedLinear p ^ (n - 1) * (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m
        * Complex.I := by
  unfold coordPartial
  have hfun : (fun s : ℝ => (seedLinear (Function.update p 3 s) ^ n).coeff m) =
      (fun s : ℝ => (((-X 0 + C (p 0 : ℂ) * X 2) +
            seedTau (Function.update p 3 s) • (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))) ^ n).coeff m) := by
    funext s; rw [seedLinear_update3]
  rw [hfun]
  have hM := coeff_affine_pow_hasDerivAt (-X 0 + C (p 0 : ℂ) * X 2)
      (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) n (seedTau p) m
  have hcomp := hasDerivAt_comp_seedTau_three p _ _ hM
  have hL : (-X 0 + C (p 0 : ℂ) * X 2) +
      seedTau p • (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) = seedLinear p :=
    (seedLinear_eq_M0_add_tau_smul_M1 p).symm
  rw [hL] at hcomp
  exact hcomp.deriv

end TernaryPeriodPolynomials.Argument
