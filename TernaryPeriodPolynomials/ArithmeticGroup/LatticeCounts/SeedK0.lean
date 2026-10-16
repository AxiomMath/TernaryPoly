module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
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
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Peel
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# The k₀ lemma (part 2)

Formalized by Claude Haiku 5.5.

For `(s, t) ∈ ℚ_p²` with `max(‖s‖, ‖t‖) = p^r`, the matrix `L(s,t) = w₀⁻¹ u(s,t)`
admits `k ∈ SL₃(ℤ_p)` with `L(s,t) k = [[A, *], [0, p^{-r}]]`, where `A` has determinant
`p^r` and its columns `(u, v)` satisfy `su + tv ∈ ℤ_p`, i.e. lie in `Λ_{s,t}`.

The construction is explicit: with `α = p^r s` and `β = p^r t` integral, one of them is a unit.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0

variable {p : ℕ} [Fact p.Prime]

/-- `L(s,t) = w₀⁻¹ u(s,t)` (paper, the matrix after `w_0^{-1}u(s,t)`). -/
noncomputable def Lst (s t : ℚ_[p]) : Matrix (Fin 3) (Fin 3) ℚ_[p] :=
  !![0, 1, 0; 0, 0, 1; 1, s, t]

/-- An integral `3 × 3` matrix, viewed over `ℚ_[p]`. -/
noncomputable def toQ (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) : Matrix (Fin 3) (Fin 3) ℚ_[p] :=
  k.map (fun x => (x : ℚ_[p]))

/-- The conclusion of the k₀ lemma for given `k` and `A`. -/
noncomputable def K0Spec (r : ℕ) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) : Prop :=
  k.det = 1 ∧ A.det = (p : ℤ_[p]) ^ r ∧
    (∀ j : Fin 2, ‖s * (A 0 j : ℚ_[p]) + t * (A 1 j : ℚ_[p])‖ ≤ 1) ∧
    (∀ i j : Fin 2, (Lst s t * toQ k) (Fin.castSucc i) (Fin.castSucc j) = (A i j : ℚ_[p])) ∧
    (Lst s t * toQ k) 2 0 = 0 ∧ (Lst s t * toQ k) 2 1 = 0 ∧
    (Lst s t * toQ k) 2 2 = ((p : ℚ_[p]) ^ r)⁻¹

lemma Lk_row0 (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (j : Fin 3) :
    (Lst s t * toQ k) 0 j = (k 1 j : ℚ_[p]) := by
  simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three]

lemma Lk_row1 (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (j : Fin 3) :
    (Lst s t * toQ k) 1 j = (k 2 j : ℚ_[p]) := by
  simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three]

lemma Lk_row2 (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (j : Fin 3) :
    (Lst s t * toQ k) 2 j = (k 0 j : ℚ_[p]) + s * (k 1 j : ℚ_[p]) + t * (k 2 j : ℚ_[p]) := by
  simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three]

lemma hp_ne (p : ℕ) [Fact p.Prime] (r : ℕ) : ((p : ℚ_[p]) ^ r) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- Case `α` a unit (`α = p^r s`, `β = p^r t`, `α x = 1`). -/
theorem k0_of_unit_alpha (r : ℕ) {s t : ℚ_[p]} (α β x : ℤ_[p])
    (hα : (α : ℚ_[p]) = (p : ℚ_[p]) ^ r * s) (hβ : (β : ℚ_[p]) = (p : ℚ_[p]) ^ r * t)
    (hx : α * x = 1) :
    K0Spec r s t !![-α, 0, 0; (p : ℤ_[p]) ^ r, -(β * x), x; 0, 1, 0]
      !![(p : ℤ_[p]) ^ r, -(β * x); 0, 1] := by
  have hαq : (p : ℚ_[p]) ^ r * s * (x : ℚ_[p]) = 1 := by
    rw [← hα]
    exact_mod_cast congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hx
  have hpr := hp_ne (p := p) r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.tail_cons, Fin.isValue]
    linear_combination hx
  · rw [Matrix.det_fin_two]
    simp
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · show ‖s * (((p : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p]) + t * ((0 : ℤ_[p]) : ℚ_[p])‖ ≤ 1
      have : s * (((p : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p]) + t * ((0 : ℤ_[p]) : ℚ_[p]) = (α : ℚ_[p]) := by
        push_cast
        rw [hα]
        ring
      rw [this]
      exact PadicInt.norm_le_one α
    · show ‖s * ((-(β * x) : ℤ_[p]) : ℚ_[p]) + t * ((1 : ℤ_[p]) : ℚ_[p])‖ ≤ 1
      have : s * ((-(β * x) : ℤ_[p]) : ℚ_[p]) + t * ((1 : ℤ_[p]) : ℚ_[p]) = 0 := by
        push_cast
        linear_combination (-(s * (x : ℚ_[p]))) * hβ + (-t) * hαq
      rw [this, norm_zero]
      exact zero_le_one
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Fin.castSucc, Lk_row0, Lk_row1]
  · rw [Lk_row2]
    show ((-α : ℤ_[p]) : ℚ_[p]) + s * (((p : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p]) +
      t * ((0 : ℤ_[p]) : ℚ_[p]) = 0
    push_cast
    linear_combination (-1 : ℚ_[p]) * hα
  · rw [Lk_row2]
    show ((0 : ℤ_[p]) : ℚ_[p]) + s * ((-(β * x) : ℤ_[p]) : ℚ_[p]) + t * ((1 : ℤ_[p]) : ℚ_[p]) = 0
    push_cast
    linear_combination (-(s * (x : ℚ_[p]))) * hβ + (-t) * hαq
  · rw [Lk_row2]
    show ((0 : ℤ_[p]) : ℚ_[p]) + s * ((x : ℤ_[p]) : ℚ_[p]) + t * ((0 : ℤ_[p]) : ℚ_[p]) =
      ((p : ℚ_[p]) ^ r)⁻¹
    rw [inv_eq_of_mul_eq_one_right (by linear_combination hαq :
      (p : ℚ_[p]) ^ r * (s * (x : ℚ_[p])) = 1)]
    push_cast
    ring

/-- Case `β` a unit (`α = p^r s`, `β = p^r t`, `β y = 1`). -/
theorem k0_of_unit_beta (r : ℕ) {s t : ℚ_[p]} (α β y : ℤ_[p])
    (hα : (α : ℚ_[p]) = (p : ℚ_[p]) ^ r * s) (hβ : (β : ℚ_[p]) = (p : ℚ_[p]) ^ r * t)
    (hy : β * y = 1) :
    K0Spec r s t !![0, -β, 0; 1, 0, 0; -(α * y), (p : ℤ_[p]) ^ r, y]
      !![1, 0; -(α * y), (p : ℤ_[p]) ^ r] := by
  have hy' : (p : ℚ_[p]) ^ r * t * (y : ℚ_[p]) = 1 := by
    rw [← hβ]
    exact_mod_cast congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hy
  have hpr := hp_ne (p := p) r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.tail_cons, Fin.isValue]
    linear_combination hy
  · rw [Matrix.det_fin_two]
    simp
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · show ‖s * ((1 : ℤ_[p]) : ℚ_[p]) + t * ((-(α * y) : ℤ_[p]) : ℚ_[p])‖ ≤ 1
      have : s * ((1 : ℤ_[p]) : ℚ_[p]) + t * ((-(α * y) : ℤ_[p]) : ℚ_[p]) = 0 := by
        push_cast
        linear_combination (-(t * (y : ℚ_[p]))) * hα + (-s) * hy'
      rw [this, norm_zero]
      exact zero_le_one
    · show ‖s * ((0 : ℤ_[p]) : ℚ_[p]) + t * (((p : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p])‖ ≤ 1
      have : s * ((0 : ℤ_[p]) : ℚ_[p]) + t * (((p : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p]) = (β : ℚ_[p]) := by
        push_cast
        rw [hβ]
        ring
      rw [this]
      exact PadicInt.norm_le_one β
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Fin.castSucc, Lk_row0, Lk_row1]
  · rw [Lk_row2]
    show ((0 : ℤ_[p]) : ℚ_[p]) + s * ((1 : ℤ_[p]) : ℚ_[p]) + t * ((-(α * y) : ℤ_[p]) : ℚ_[p]) = 0
    push_cast
    linear_combination (-(t * (y : ℚ_[p]))) * hα + (-s) * hy'
  · rw [Lk_row2]
    show ((-β : ℤ_[p]) : ℚ_[p]) + s * ((0 : ℤ_[p]) : ℚ_[p]) +
      t * (((p : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p]) = 0
    push_cast
    linear_combination (-1 : ℚ_[p]) * hβ
  · rw [Lk_row2]
    show ((0 : ℤ_[p]) : ℚ_[p]) + s * ((0 : ℤ_[p]) : ℚ_[p]) + t * ((y : ℤ_[p]) : ℚ_[p]) =
      ((p : ℚ_[p]) ^ r)⁻¹
    rw [inv_eq_of_mul_eq_one_right (by linear_combination hy' :
      (p : ℚ_[p]) ^ r * (t * (y : ℚ_[p])) = 1)]
    push_cast
    ring

lemma norm_pr (r : ℕ) : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
  rw [Padic.norm_p_pow, zpow_neg, zpow_natCast]

lemma norm_pr_mul_le (r : ℕ) {s : ℚ_[p]} (hs : ‖s‖ ≤ (p : ℝ) ^ r) :
    ‖(p : ℚ_[p]) ^ r * s‖ ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, norm_pr]
  calc ((p : ℝ) ^ r)⁻¹ * ‖s‖ ≤ ((p : ℝ) ^ r)⁻¹ * (p : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 := inv_mul_cancel₀ (pow_pos hp r).ne'

lemma norm_pr_mul_eq_one (r : ℕ) {s : ℚ_[p]} (hs : ‖s‖ = (p : ℝ) ^ r) :
    ‖(p : ℚ_[p]) ^ r * s‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, norm_pr, hs]
  exact inv_mul_cancel₀ (pow_pos hp r).ne'

/-- **The k₀ lemma.** For `max(‖s‖, ‖t‖) = p^r`, there is `k ∈ SL₃(ℤ_p)` and a matrix `A`
with `det A = p^r`, columns in `Λ_{s,t}`, and `L(s,t) k = [[A, *], [0, p^{-r}]]`. -/
theorem exists_k0 (r : ℕ) {s t : ℚ_[p]} (hmax : max ‖s‖ ‖t‖ = (p : ℝ) ^ r) :
    ∃ k : Matrix (Fin 3) (Fin 3) ℤ_[p], ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
      K0Spec r s t k A := by
  have hs : ‖s‖ ≤ (p : ℝ) ^ r := by rw [← hmax]; exact le_max_left _ _
  have ht : ‖t‖ ≤ (p : ℝ) ^ r := by rw [← hmax]; exact le_max_right _ _
  obtain ⟨α, hα⟩ : ∃ α : ℤ_[p], (α : ℚ_[p]) = (p : ℚ_[p]) ^ r * s :=
    ⟨⟨_, norm_pr_mul_le r hs⟩, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ_[p], (β : ℚ_[p]) = (p : ℚ_[p]) ^ r * t :=
    ⟨⟨_, norm_pr_mul_le r ht⟩, rfl⟩
  rcases max_choice ‖s‖ ‖t‖ with h | h
  · have hs1 : ‖s‖ = (p : ℝ) ^ r := h.symm.trans hmax
    have hunit : IsUnit α := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_def, hα, norm_pr_mul_eq_one r hs1]
    obtain ⟨x, hx⟩ := hunit.exists_right_inv
    exact ⟨_, _, k0_of_unit_alpha r α β x hα hβ hx⟩
  · have ht1 : ‖t‖ = (p : ℝ) ^ r := h.symm.trans hmax
    have hunit : IsUnit β := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_def, hβ, norm_pr_mul_eq_one r ht1]
    obtain ⟨y, hy⟩ := hunit.exists_right_inv
    exact ⟨_, _, k0_of_unit_beta r α β y hα hβ hy⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0
