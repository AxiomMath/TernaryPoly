module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviIdentities

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): the Jacobian of `leviMap A t` at `p`, as explicit
numeric rows, extracted from `leviMap_fderiv_apply`. Each row `i` gives
`fderiv ℝ (leviMap A t) p (Pi.single i 1) a` for all five components `a`; `formPullback`'s double
sum needs exactly these. Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

theorem leviMap_fderiv_row0 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    fderiv ℝ (leviMap A t) p (Pi.single 0 1) = ![A 0 0 / t, A 1 0 / t, 0, 0, 0] := by
  funext a
  rw [leviMap_fderiv_apply A t p hden]
  fin_cases a <;> simp

theorem leviMap_fderiv_row1 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    fderiv ℝ (leviMap A t) p (Pi.single 1 1) = ![A 0 1 / t, A 1 1 / t, 0, 0, 0] := by
  funext a
  rw [leviMap_fderiv_apply A t p hden]
  fin_cases a <;> simp

theorem leviMap_fderiv_row4 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    fderiv ℝ (leviMap A t) p (Pi.single 4 1) = ![0, 0, 0, 0, t] := by
  funext a
  rw [leviMap_fderiv_apply A t p hden]
  fin_cases a <;> simp

theorem leviMap_fderiv_row2 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    fderiv ℝ (leviMap A t) p (Pi.single 2 1) =
      ![0, 0, ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2).re,
            ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2).im, 0] := by
  funext a
  rw [leviMap_fderiv_apply A t p hden]
  fin_cases a <;> simp

theorem leviMap_fderiv_row3 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    fderiv ℝ (leviMap A t) p (Pi.single 3 1) =
      ![0, 0, -((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2).im,
            ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2).re, 0] := by
  funext a
  rw [leviMap_fderiv_apply A t p hden]
  fin_cases a <;> simp

end TernaryPeriodPolynomials.Argument
