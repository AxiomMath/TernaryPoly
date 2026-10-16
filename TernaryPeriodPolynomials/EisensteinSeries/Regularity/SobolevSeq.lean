module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Convex.Jensen
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
# A weighted Cauchy–Schwarz inequality for series

For positive weights `β`, `m` and nonnegative `γ`, `x`,
`Σ γ_n x_n ≤ (Σ γ_n² / (m_n² β_n))^(1/2) (Σ m_n² β_n x_n²)^(1/2)`.
This is the form in which the weighted `L¹` norm of a Bergman vector (`x_n` its coefficient
norms, `γ_n` the `L¹` moments) is controlled by the Bergman norm of its second rotation
derivative (`m_n = (k + 2n)²`, `β_n` the `L²` moments).
-/

namespace TernaryPeriodPolynomials.Regularity

/-- Weighted Cauchy–Schwarz inequality for nonnegative series. -/
theorem weighted_cauchy_schwarz {β γ m x : ℕ → ℝ} (hβ : ∀ n, 0 < β n) (hγ : ∀ n, 0 ≤ γ n)
    (hm : ∀ n, 0 < m n) (hx : ∀ n, 0 ≤ x n)
    (hS : Summable fun n => γ n ^ 2 / (m n ^ 2 * β n))
    (hT : Summable fun n => m n ^ 2 * β n * x n ^ 2) :
    (Summable fun n => γ n * x n) ∧
      ∑' n, γ n * x n ≤
        Real.sqrt (∑' n, γ n ^ 2 / (m n ^ 2 * β n)) *
          Real.sqrt (∑' n, m n ^ 2 * β n * x n ^ 2) := by
  have hpos : ∀ n, 0 < m n * Real.sqrt (β n) := fun n =>
    mul_pos (hm n) (Real.sqrt_pos.mpr (hβ n))
  have hfg : ∀ n, γ n / (m n * Real.sqrt (β n)) * (m n * Real.sqrt (β n) * x n) =
      γ n * x n := fun n => by
    rw [← mul_assoc, div_mul_cancel₀ _ (hpos n).ne']
  have hf2 : ∀ n, (γ n / (m n * Real.sqrt (β n))) ^ (2 : ℝ) = γ n ^ 2 / (m n ^ 2 * β n) :=
    fun n => by rw [Real.rpow_two, div_pow, mul_pow, Real.sq_sqrt (hβ n).le]
  have hg2 : ∀ n, (m n * Real.sqrt (β n) * x n) ^ (2 : ℝ) = m n ^ 2 * β n * x n ^ 2 :=
    fun n => by rw [Real.rpow_two, mul_pow, mul_pow, Real.sq_sqrt (hβ n).le]
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (f := fun n => γ n / (m n * Real.sqrt (β n)))
    (g := fun n => m n * Real.sqrt (β n) * x n)
    (fun n => div_nonneg (hγ n) (hpos n).le) (fun n => mul_nonneg (hpos n).le (hx n))
    (by simpa only [hf2] using hS) (by simpa only [hg2] using hT)
  simp only [hfg, hf2, hg2] at hsum hle
  refine ⟨hsum, ?_⟩
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hle

/-- The weighted `ℓ¹` sum `Σ γ_n (a_n + b_n)` is controlled by the weighted `ℓ²` sum
`V2 = Σ β_n ((m_n a_n)² + (m_n b_n)²)`. -/
theorem sobolev_seq {β γ m a b : ℕ → ℝ} (hβ : ∀ n, 0 < β n) (hγ : ∀ n, 0 ≤ γ n)
    (hm : ∀ n, 0 < m n) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hS : Summable fun n => γ n ^ 2 / (m n ^ 2 * β n)) {V2 : ℝ}
    (hV : HasSum (fun n => β n * ((m n * a n) ^ 2 + (m n * b n) ^ 2)) V2) :
    (Summable fun n => γ n * (a n + b n)) ∧
      ∑' n, γ n * (a n + b n) ≤
        Real.sqrt (∑' n, γ n ^ 2 / (m n ^ 2 * β n)) * Real.sqrt (2 * V2) := by
  have hle : ∀ n, m n ^ 2 * β n * (a n + b n) ^ 2 ≤
      2 * (β n * ((m n * a n) ^ 2 + (m n * b n) ^ 2)) := by
    intro n
    have h1 : (a n + b n) ^ 2 ≤ 2 * (a n ^ 2 + b n ^ 2) := by
      nlinarith [sq_nonneg (a n - b n)]
    have h2 : 0 ≤ m n ^ 2 * β n := mul_nonneg (sq_nonneg _) (hβ n).le
    calc m n ^ 2 * β n * (a n + b n) ^ 2 ≤ m n ^ 2 * β n * (2 * (a n ^ 2 + b n ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 2 * (β n * ((m n * a n) ^ 2 + (m n * b n) ^ 2)) := by ring
  have hnn : ∀ n, 0 ≤ m n ^ 2 * β n * (a n + b n) ^ 2 := fun n =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (hβ n).le) (sq_nonneg _)
  have h2V := hV.mul_left 2
  have hT : Summable fun n => m n ^ 2 * β n * (a n + b n) ^ 2 :=
    Summable.of_nonneg_of_le hnn hle h2V.summable
  have hTle : ∑' n, m n ^ 2 * β n * (a n + b n) ^ 2 ≤ 2 * V2 := by
    rw [← h2V.tsum_eq]
    exact hT.tsum_le_tsum hle h2V.summable
  obtain ⟨hsum, hcs⟩ := weighted_cauchy_schwarz hβ hγ hm
    (fun n => add_nonneg (ha n) (hb n)) hS hT
  exact ⟨hsum, hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTle)
    (Real.sqrt_nonneg _))⟩

end TernaryPeriodPolynomials.Regularity
