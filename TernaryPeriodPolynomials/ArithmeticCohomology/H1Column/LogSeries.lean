module

public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# `log (exp a) = a` for a nilpotent element of a `ℚ`-algebra (MR-8)

Formalized by Claude Sonnet 5.5.

For `a` with `a^N = 0` in a `ℚ`-algebra, the logarithm series `∑_{k<N} (-1)^k/(k+1) (exp a - 1)^{k+1}` (a finite sum, since `exp a - 1` is nilpotent) returns `a` (`log_exp_nilpotent`).  It is proved in `ℚ[X]` by comparing derivatives
modulo `X^N`, then evaluated at `a`.
-/

open Polynomial Finset

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

/-- The truncated exponential `∑_{m<N} X^m/m!`. -/
def truncExp (N : ℕ) : ℚ[X] := ∑ m ∈ range N, C ((m.factorial : ℚ)⁻¹) * X ^ m

/-- The truncated logarithm series evaluated at the truncated exponential. -/
def truncLog (N : ℕ) : ℚ[X] := ∑ k ∈ range N, C ((-1 : ℚ) ^ k / (k + 1)) * (truncExp N - 1) ^ (k + 1)

theorem derivative_truncExp (N : ℕ) : derivative (truncExp (N + 1)) = truncExp N := by
  unfold truncExp
  rw [derivative_sum, Finset.sum_range_succ']
  simp only [derivative_C_mul_X_pow, Nat.cast_zero, mul_zero, C_0, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  congr 2
  push_cast
  field_simp

theorem truncExp_coeff_zero (N : ℕ) (hN : 1 ≤ N) : (truncExp N).coeff 0 = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  unfold truncExp
  rw [Polynomial.finsetSum_coeff, Finset.sum_range_succ']
  simp [coeff_X_pow]

theorem X_dvd_truncExp_sub_one (N : ℕ) (hN : 1 ≤ N) : (X : ℚ[X]) ∣ truncExp N - 1 := by
  rw [X_dvd_iff, coeff_sub, truncExp_coeff_zero N hN]
  simp

theorem X_dvd_truncLog (N : ℕ) (hN : 1 ≤ N) : (X : ℚ[X]) ∣ truncLog N := by
  unfold truncLog
  refine Finset.dvd_sum fun k _ => ?_
  exact Dvd.dvd.mul_left (dvd_pow (X_dvd_truncExp_sub_one N hN) (Nat.succ_ne_zero k)) _

theorem X_pow_dvd_truncLog_sub (N : ℕ) : (X : ℚ[X]) ^ N ∣ truncLog N - X := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set E := truncExp (M + 1) with hE
  have hX : (X : ℚ[X]) ∣ E - 1 := X_dvd_truncExp_sub_one (M + 1) (by omega)
  -- derivative of the logarithm series
  have hder : derivative (truncLog (M + 1)) = derivative E * ∑ k ∈ range (M + 1), (1 - E) ^ k := by
    unfold truncLog
    rw [← hE, derivative_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_C_mul, derivative_pow, derivative_sub, derivative_one, sub_zero]
    have hk : ((-1 : ℚ) ^ k / (k + 1)) * ((k + 1 : ℕ) : ℚ) = (-1) ^ k := by
      push_cast
      field_simp
    have e : (1 - E) ^ k = (-1) ^ k * (E - 1) ^ k := by
      rw [← neg_sub, neg_pow]
    rw [e]
    simp only [Nat.add_sub_cancel]
    calc C ((-1 : ℚ) ^ k / (k + 1)) * (C ((k + 1 : ℕ) : ℚ) * (E - 1) ^ k * derivative E)
        = C (((-1 : ℚ) ^ k / (k + 1)) * ((k + 1 : ℕ) : ℚ)) * ((E - 1) ^ k * derivative E) := by
          rw [C_mul]; ring
      _ = _ := by
          rw [hk]; simp [C_pow]; ring
  have hgeom : E * ∑ k ∈ range (M + 1), (1 - E) ^ k = 1 - (1 - E) ^ (M + 1) := by
    have := mul_neg_geom_sum (1 - E) (M + 1)
    simpa using this
  have hE' : derivative E = E - C ((M.factorial : ℚ)⁻¹) * X ^ M := by
    rw [hE, derivative_truncExp]
    unfold truncExp
    rw [Finset.sum_range_succ]
    ring
  have hg' : derivative (truncLog (M + 1) - X) =
      -(1 - E) ^ (M + 1) - C ((M.factorial : ℚ)⁻¹) * X ^ M * ∑ k ∈ range (M + 1), (1 - E) ^ k := by
    rw [derivative_sub, derivative_X, hder, hE']
    linear_combination hgeom
  have hdvd : (X : ℚ[X]) ^ M ∣ derivative (truncLog (M + 1) - X) := by
    rw [hg']
    refine dvd_sub ?_ ?_
    · refine dvd_neg.mpr ?_
      have h1 : (X : ℚ[X]) ∣ 1 - E := by
        have := dvd_neg.mpr hX
        simpa using this
      exact (pow_dvd_pow _ (Nat.le_succ M)).trans (pow_dvd_pow_of_dvd h1 (M + 1))
    · exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  rw [X_pow_dvd_iff]
  intro d hd
  rw [coeff_sub]
  rcases d with _ | d
  · have : (truncLog (M + 1)).coeff 0 = 0 := X_dvd_iff.mp (X_dvd_truncLog (M + 1) (by omega))
    simp [this]
  · have h1 := (X_pow_dvd_iff.mp hdvd) d (by omega)
    rw [coeff_derivative] at h1
    have h2 : ((truncLog (M + 1) - X).coeff (d + 1)) = 0 := by
      have hne : ((d : ℚ) + 1) ≠ 0 := by positivity
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hne
    rwa [coeff_sub] at h2

/-- **`log (exp a) = a`** for `a^N = 0` in a `ℚ`-algebra. -/
theorem log_exp_nilpotent {A : Type*} [Ring A] [Algebra ℚ A] (a : A) (N : ℕ) (hN : a ^ N = 0) :
    ∑ k ∈ range N, ((-1 : ℚ) ^ k / (k + 1)) • (IsNilpotent.exp a - 1) ^ (k + 1) = a := by
  obtain ⟨h, hh⟩ := X_pow_dvd_truncLog_sub N
  have h0 : aeval a (truncLog N - X) = 0 := by
    rw [hh, map_mul, map_pow, aeval_X, hN, zero_mul]
  have hexp : aeval a (truncExp N) = IsNilpotent.exp a := by
    rw [IsNilpotent.exp_eq_sum hN]
    simp [truncExp, Algebra.smul_def]
  rw [map_sub, aeval_X, sub_eq_zero] at h0
  have h1 : aeval a (truncLog N) =
      ∑ k ∈ range N, ((-1 : ℚ) ^ k / (k + 1)) • (IsNilpotent.exp a - 1) ^ (k + 1) := by
    simp [truncLog, hexp, Algebra.smul_def]
  rw [← h1]
  exact h0

end TernaryPeriodPolynomials.Argument.Identities
