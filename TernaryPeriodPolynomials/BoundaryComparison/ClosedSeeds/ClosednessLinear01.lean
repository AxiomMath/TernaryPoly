module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.AffineDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`): per-coordinate affine normal form of `seedLinear`
along coordinates `0` and `1` (the two coordinates `seedTau` does not read), and the resulting
closed form of `coordPartial (fun q => coeff m (seedLinear q ^ n)) k p` for `k = 0, 1`, via direct
application of the Master Lemma `coeff_affine_pow_hasDerivAt`. Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `seedLinear` at a point whose coordinate `0` has been replaced by `s`, in `L0 + c • L1`
affine normal form (`c := s`, `L1 := X 2`). -/
theorem seedLinear_update0 (p : Fin 5 → ℝ) (s : ℝ) :
    seedLinear (Function.update p 0 s) =
      (C (seedTau p) * X 1 - X 0 - C (seedTau p * (p 1 : ℂ)) * X 2) +
        (s : ℂ) • (X 2 : MvPolynomial (Fin 3) ℂ) := by
  have hτ : seedTau (Function.update p 0 s) = seedTau p := by simp [seedTau]
  have h0 : ((Function.update p 0 s) 0 : ℝ) = s := by simp
  have h1 : ((Function.update p 0 s) 1 : ℝ) = p 1 := by simp
  simp only [seedLinear, hτ, h0, h1, MvPolynomial.smul_eq_C_mul, map_sub, map_mul]
  ring

/-- `seedLinear` at a point whose coordinate `1` has been replaced by `s`, in `L0 + c • L1`
affine normal form (`c := s`, `L1 := -(C (seedTau p) * X 2)`). -/
theorem seedLinear_update1 (p : Fin 5 → ℝ) (s : ℝ) :
    seedLinear (Function.update p 1 s) =
      (C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ)) * X 2) +
        (s : ℂ) • (-(C (seedTau p) * X 2) : MvPolynomial (Fin 3) ℂ) := by
  have hτ : seedTau (Function.update p 1 s) = seedTau p := by simp [seedTau]
  have h0 : ((Function.update p 1 s) 0 : ℝ) = p 0 := by simp
  have h1 : ((Function.update p 1 s) 1 : ℝ) = s := by simp
  simp only [seedLinear, hτ, h0, h1, MvPolynomial.smul_eq_C_mul, map_sub, map_mul, mul_neg]
  ring

/-- Closed form for `coordPartial (fun q => coeff m (seedLinear q ^ n)) 0 p`: coordinate `0`
enters `seedLinear` affinely with slope `X 2`. -/
theorem coordPartial_seedLinear_pow_zero (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    coordPartial (fun q => (seedLinear q ^ n).coeff m) 0 p =
      (n : ℂ) * (seedLinear p ^ (n - 1) * X 2).coeff m := by
  unfold coordPartial
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
  exact hmaster.deriv

/-- Closed form for `coordPartial (fun q => coeff m (seedLinear q ^ n)) 1 p`: coordinate `1`
enters `seedLinear` affinely with slope `-(C (seedTau p) * X 2)`. -/
theorem coordPartial_seedLinear_pow_one (n : ℕ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) :
    coordPartial (fun q => (seedLinear q ^ n).coeff m) 1 p =
      (n : ℂ) * (seedLinear p ^ (n - 1) * (-(C (seedTau p) * X 2))).coeff m := by
  unfold coordPartial
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
  exact hmaster.deriv

end TernaryPeriodPolynomials.Argument
