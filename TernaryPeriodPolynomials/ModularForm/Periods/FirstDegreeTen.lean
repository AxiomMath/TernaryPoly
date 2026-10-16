module

public import TernaryPeriodPolynomials.ModularForm.Corollary14General
public import TernaryPeriodPolynomials.ModularForm.Periods.SolutionTenDimension

@[expose] public section


/-!
# The first nonzero solutions occur in degree ten

Formalized by Claude Haiku 5.5.

The paper's Example says that the first nonzero solutions occur in degree ten. The solution
space in degree `d` is `solutionSpace F d` (the homogeneous ternary solutions of the definitions in `TernaryPeriodPolynomials/Polynomial/Definitions.lean`). The theorem below gives, for every field
`F` of characteristic zero, that this space is `0` in every degree `d < 10`, and that in degree ten
it is nonzero with dimension `2`.

Proof route: the Hilbert series of `corollary_1_4_general` (its fourth clause, the universe-general
form of `period_isomorphisms_and_finrank`) reads `(∑ dim W_n t^n)(1-t⁴)(1-t⁶) = 2t¹⁰`. Comparing coefficients below
degree ten gives `dim W_n = 0` for `n < 10`. Finite-dimensionality of `W_n` (it is a submodule of
the finitely generated `homogeneousSubmodule`) turns `dim = 0` into `W_n = ⊥`. The dimension `2` in
degree ten is `solutionSpace_ten_finrank_eq_two`.
-/

open MvPolynomial TernaryPoly.Paper

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

universe u

/-- A power series identity `a(t)(1-t⁴)(1-t⁶) = 2t¹⁰` over `ℤ` forces `a n = 0` for `n < 10`:
the coefficient of `tⁿ` gives `a n = a(n-4) + a(n-6) - a(n-10)` (plus `2` when `n = 10`). -/
theorem coeff_eq_zero_of_lt_ten (a : ℕ → ℤ)
    (h : PowerSeries.mk a * ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) =
      2 * PowerSeries.X ^ 10) :
    ∀ n : ℕ, n < 10 → a n = 0 := by
  have hc : ∀ n : ℕ, a n - (if 4 ≤ n then a (n - 4) else 0) -
      (if 6 ≤ n then a (n - 6) else 0) + (if 10 ≤ n then a (n - 10) else 0) =
        if n = 10 then 2 else 0 := by
    intro n
    have e : PowerSeries.mk a * ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) =
        PowerSeries.mk a - PowerSeries.mk a * PowerSeries.X ^ 4 -
          PowerSeries.mk a * PowerSeries.X ^ 6 + PowerSeries.mk a * PowerSeries.X ^ 10 := by
      ring
    have hn := congrArg (PowerSeries.coeff n) (e.symm.trans h)
    rw [map_add, map_sub, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk] at hn
    simp only [PowerSeries.coeff_mk] at hn
    have h2 : (PowerSeries.coeff n) (2 * PowerSeries.X ^ 10 : PowerSeries ℤ) =
        if n = 10 then 2 else 0 := by
      have e2 : (2 : PowerSeries ℤ) * PowerSeries.X ^ 10 =
          PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 10 := by simp
      rw [e2, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases hn10 : n = 10 <;> simp [hn10]
    rw [h2] at hn
    exact hn
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hcn := hc n
    have hz4 : (if 4 ≤ n then a (n - 4) else 0) = 0 := by
      split_ifs with h4
      · exact ih (n - 4) (by omega) (by omega)
      · rfl
    have hz6 : (if 6 ≤ n then a (n - 6) else 0) = 0 := by
      split_ifs with h6
      · exact ih (n - 6) (by omega) (by omega)
      · rfl
    have hz10 : (if 10 ≤ n then a (n - 10) else 0) = 0 := by
      split_ifs with h10
      · omega
      · rfl
    rw [hz4, hz6, hz10, ite_eq_right (by omega : n ≠ 10)] at hcn
    simpa using hcn

/-- Dimension of `W_n(F)` vanishes below degree ten: the Hilbert series of
`corollary_1_4_general` (`hilbertSeries`) and `coeff_eq_zero_of_lt_ten`. -/
theorem solutionSpace_eq_bot_of_lt_ten (F : Type u) [Field F] [CharZero F] {d : ℕ} (hd : d < 10) :
    solutionSpace F d = ⊥ := by
  obtain ⟨-, -, -, hD⟩ := TernaryPeriodPolynomials.Argument.Statements.corollary_1_4_general
  have hilb := coeff_eq_zero_of_lt_ten
    (fun n => (Module.finrank F (solutionSpace F n) : ℤ)) (hD F) d hd
  have hdim : Module.finrank F (solutionSpace F d) = 0 := by exact_mod_cast hilb
  have hfin : Module.Finite F (solutionSpace F d) := by
    have hH : Module.Finite F (homogeneousSubmodule (Fin 3) F d) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 3) F d)
    exact Submodule.finiteDimensional_of_le (inf_le_left : solutionSpace F d ≤
      homogeneousSubmodule (Fin 3) F d)
  exact (Submodule.finrank_eq_zero).mp hdim

/-- **First nonzero solutions in degree ten**. For every field `F` of
characteristic zero: the solution space `W_d(F)` is `0` for every `d < 10`; it is nonzero in degree
ten, and its dimension there is `2`. -/
theorem first_nonzero_solution_degree_ten (F : Type u) [Field F] [CharZero F] :
    (∀ d : ℕ, d < 10 → solutionSpace F d = ⊥) ∧ solutionSpace F 10 ≠ ⊥ ∧
      Module.finrank F (solutionSpace F 10) = 2 := by
  have hdim : Module.finrank F (solutionSpace F 10) = 2 :=
    TernaryPeriodPolynomials.Argument.solutionSpace_ten_finrank_eq_two F
  refine ⟨fun d hd => solutionSpace_eq_bot_of_lt_ten F hd, ?_, hdim⟩
  intro hbot
  rw [hbot, finrank_bot] at hdim
  exact absurd hdim (by norm_num)

end TernaryPeriodPolynomials.Argument.Identities
