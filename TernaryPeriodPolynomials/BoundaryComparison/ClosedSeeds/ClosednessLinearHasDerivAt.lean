module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.AffineDeriv
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessChainRule
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessLinear01
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessLinear23
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`): `HasDerivAt`-level (not just `coordPartial`-level,
i.e. not yet post-composed with `.deriv`) versions of the four per-coordinate affine-derivative
facts for `seedLinear` from `ClosednessLinear01.lean`/`ClosednessLinear23.lean`. Exposing the raw
`HasDerivAt` lets it be combined via the product rule with another `HasDerivAt` fact along the
same real coordinate — needed for the "hard" nontrivial `Alt3` triples, where `seedForm`'s scalar
prefactor `h (seedTau q) * (seedBeta q i * seedDTau j - seedBeta q j * seedDTau i)` also varies
along the coordinate. Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

theorem hasDerivAt_seedLinear_pow_zero (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    HasDerivAt (fun s : ℝ => (seedLinear (Function.update p 0 s) ^ n).coeff m)
      ((n : ℂ) * (seedLinear p ^ (n - 1) * X 2).coeff m) (p 0) := by
  have hfun : (fun s : ℝ => (seedLinear (Function.update p 0 s) ^ n).coeff m) =
      (fun s : ℝ =>
        (((C (seedTau p) * X 1 - X 0 - C (seedTau p * (p 1 : ℂ)) * X 2) +
              (s : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ)) ^ n).coeff m) := by
    funext s; rw [seedLinear_update0]
  rw [hfun]
  have hL : (C (seedTau p) * X 1 - X 0 - C (seedTau p * (p 1 : ℂ)) * X 2) +
      (p 0 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ) = seedLinear p := by
    simp only [seedLinear, MvPolynomial.smul_eq_C_mul, map_sub, map_mul]
    ring
  have hmaster := (coeff_affine_pow_hasDerivAt
      (C (seedTau p) * X 1 - X 0 - C (seedTau p * (p 1 : ℂ)) * X 2) (X 2) n (p 0 : ℂ) m).comp_ofReal
  rw [hL] at hmaster
  exact hmaster

theorem hasDerivAt_seedLinear_pow_one (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    HasDerivAt (fun s : ℝ => (seedLinear (Function.update p 1 s) ^ n).coeff m)
      ((n : ℂ) * (seedLinear p ^ (n - 1) * (-(C (seedTau p) * X 2))).coeff m) (p 1) := by
  have hfun : (fun s : ℝ => (seedLinear (Function.update p 1 s) ^ n).coeff m) =
      (fun s : ℝ =>
        (((C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ)) * X 2) +
              (s : ℂ) • (-(C (seedTau p) * X 2) : MvPolynomial (Fin 3) ℂ)) ^ n).coeff m) := by
    funext s; rw [seedLinear_update1]
  rw [hfun]
  have hL : (C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ)) * X 2) +
      (p 1 : ℂ) • (-(C (seedTau p) * X 2) : MvPolynomial (Fin 3) ℂ) = seedLinear p := by
    simp only [seedLinear, MvPolynomial.smul_eq_C_mul, map_sub, map_mul, mul_neg]
    ring
  have hmaster := (coeff_affine_pow_hasDerivAt
      (C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ)) * X 2) (-(C (seedTau p) * X 2)) n
      (p 1 : ℂ) m).comp_ofReal
  rw [hL] at hmaster
  exact hmaster

theorem hasDerivAt_seedLinear_pow_two (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    HasDerivAt (fun s : ℝ => (seedLinear (Function.update p 2 s) ^ n).coeff m)
      ((n : ℂ) * (seedLinear p ^ (n - 1) * (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m)
      (p 2) := by
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
  exact hcomp

theorem hasDerivAt_seedLinear_pow_three (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    HasDerivAt (fun s : ℝ => (seedLinear (Function.update p 3 s) ^ n).coeff m)
      ((n : ℂ) * (seedLinear p ^ (n - 1) * (X 1 - (p 1 : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ))).coeff m
        * Complex.I) (p 3) := by
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
  exact hcomp

end TernaryPeriodPolynomials.Argument
