module

public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodAxis

@[expose] public section



/-!
# Scalar-multiplication linearity of the even period

`moment`, `periodCoefficient`, `period`, `evenPeriod` (Submission-side) and `evenPeriodPart`,
`normalizedEvenPeriodPart` (Revision-side, via the `evenPeriod_eq_evenPeriodPart` bridge) are all
ℂ-linear in the cusp form argument. This file records the scalar-multiplication half of that
linearity (the additive half is not needed), which is exactly what lets us transfer nonvanishing
of `normalizedEvenPeriodPart` from one explicit representative of a one-dimensional space of
forms to an arbitrary nonzero element of it.
-/

noncomputable section
open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CuspForms

open TernaryPoly.BinaryCuspPeriod

theorem moment_smul {d : ℕ} (f : Forms d) (c : ℂ) (s : ℂ) :
    moment (c • f) s = c * moment f s := by
  simp only [moment, smul_apply]
  rw [mellin_const_smul, smul_eq_mul]

theorem periodCoefficient_smul {d : ℕ} (f : Forms d) (c : ℂ) (j : ℕ) :
    periodCoefficient (c • f) j = c * periodCoefficient f j := by
  simp only [periodCoefficient]
  rw [moment_smul]
  ring

theorem period_smul {d : ℕ} (f : Forms d) (c : ℂ) :
    period (c • f) = C c * period f := by
  simp only [period, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [periodCoefficient_smul, C_mul_monomial]

theorem evenPeriod_smul {d : ℕ} (f : Forms d) (c : ℂ) :
    evenPeriod (c • f) = C c * evenPeriod f := by
  simp only [evenPeriod, period_smul, map_mul, bind₁_C_right,
    MvPolynomial.smul_eq_C_mul]
  ring

theorem evenPeriodPart_smul {d : ℕ} (f : Forms d) (c : ℂ) :
    TernaryPeriodPolynomials.Argument.evenPeriodPart d (c • f) =
      C c * TernaryPeriodPolynomials.Argument.evenPeriodPart d f := by
  rw [← evenPeriod_eq_evenPeriodPart, ← evenPeriod_eq_evenPeriodPart, evenPeriod_smul]

theorem normalizedEvenPeriodPart_smul {d : ℕ} (f : Forms d) (c : ℂ) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart d (c • f) =
      C c * TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart d f := by
  simp only [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart, evenPeriodPart_smul,
    eval_C, map_mul]
  ring

end TernaryPeriodPolynomials.Argument.CuspForms
