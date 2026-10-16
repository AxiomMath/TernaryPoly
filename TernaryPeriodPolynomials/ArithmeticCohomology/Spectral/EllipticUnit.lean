module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# A unit complex number of trace `1/3` that is not a root of unity

`ellipticRoot = (1 + i√35)/6` and `ellipticConj = 1/3 - ellipticRoot = (1 - i√35)/6` are the two roots of
`x² - x/3 + 1`. Their power sums `t_N = x^N + x'^N` satisfy `3^N t_N ∈ ℤ` with `3^N t_N ≡ 1 (mod 3)` for
`N ≥ 1`, so `t_N ≠ 2`, and therefore no positive power of `ellipticRoot` is `1`. This is the arithmetic input
for the elliptic element `S T^{1/3}` (trace `1/3`) used in `LevelOneMultiplicityOne`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Spectral.EllipticUnit

/-- `(1 + i√35)/6`. -/
def ellipticRoot : ℂ := (1 + Complex.I * (Real.sqrt 35 : ℂ)) / 6

/-- The other root `(1 - i√35)/6 = 1/3 - ellipticRoot`. -/
def ellipticConj : ℂ := 1 / 3 - ellipticRoot

theorem sqrt35_sq : ((Real.sqrt 35 : ℝ) : ℂ) ^ 2 = 35 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem ellipticRoot_sq : ellipticRoot ^ 2 = ellipticRoot / 3 - 1 := by
  unfold ellipticRoot
  have h := sqrt35_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (Complex.I ^ 2 / 36) * h + (35 / 36 : ℂ) * hI

theorem ellipticRoot_mul_conj : ellipticRoot * ellipticConj = 1 := by
  unfold ellipticConj
  linear_combination -ellipticRoot_sq

theorem ellipticConj_sq : ellipticConj ^ 2 = ellipticConj / 3 - 1 := by
  unfold ellipticConj
  linear_combination ellipticRoot_sq

/-- The integer sequence `a_0 = 2`, `a_1 = 1`, `a_{N+2} = a_{N+1} - 9 a_N`. -/
def powerSum : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (N + 2) => powerSum (N + 1) - 9 * powerSum N

theorem powerSum_eq (N : ℕ) :
    (3 : ℂ) ^ N * (ellipticRoot ^ N + ellipticConj ^ N) = powerSum N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N, ih with
    | 0, _ => simp [powerSum]; norm_num
    | 1, _ => simp [powerSum, ellipticConj]
    | (N + 2), ih =>
      have h1 := ih (N + 1) (by omega)
      have h0 := ih N (by omega)
      simp only [powerSum]
      push_cast
      rw [← h1, ← h0]
      have hr : ellipticRoot ^ (N + 2) = ellipticRoot ^ N * (ellipticRoot / 3 - 1) := by
        rw [pow_add, ellipticRoot_sq]
      have hc : ellipticConj ^ (N + 2) = ellipticConj ^ N * (ellipticConj / 3 - 1) := by
        rw [pow_add, ellipticConj_sq]
      rw [hr, hc, pow_succ ellipticRoot N, pow_succ ellipticConj N]
      ring

theorem powerSum_mod (N : ℕ) (hN : 1 ≤ N) : powerSum N % 3 = 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N, ih with
    | 0, _ => omega
    | 1, _ => simp [powerSum]
    | (N + 2), ih =>
      simp only [powerSum]
      by_cases h : N = 0
      · subst h; simp [powerSum]
      · have h1 := ih (N + 1) (by omega) (by omega)
        omega

/-- **No positive power of `ellipticRoot` is `1`.** -/
theorem ellipticRoot_pow_ne_one (N : ℕ) (hN : 1 ≤ N) : ellipticRoot ^ N ≠ 1 := by
  intro h
  have hc : ellipticConj ^ N = 1 := by
    have := congrArg (· ^ N) ellipticRoot_mul_conj
    simp only [mul_pow, one_pow, h, one_mul] at this
    exact this
  have hsum := powerSum_eq N
  rw [h, hc] at hsum
  have hint : powerSum N = 2 * 3 ^ N := by
    have : ((powerSum N : ℤ) : ℂ) = ((2 * 3 ^ N : ℤ) : ℂ) := by
      rw [← hsum]; push_cast; ring
    exact_mod_cast this
  have hmod := powerSum_mod N hN
  rw [hint] at hmod
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [pow_succ] at hmod
  omega

theorem ellipticRoot_ne_zero : ellipticRoot ≠ 0 := by
  intro h
  have := ellipticRoot_mul_conj
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem ellipticConj_eq_inv : ellipticConj = ellipticRoot⁻¹ :=
  eq_inv_of_mul_eq_one_right ellipticRoot_mul_conj

theorem ellipticRoot_im_pos : 0 < ellipticRoot.im := by
  simp [ellipticRoot]

end TernaryPeriodPolynomials.Spectral.EllipticUnit
