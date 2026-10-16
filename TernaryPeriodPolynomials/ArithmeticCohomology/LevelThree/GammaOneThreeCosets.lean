module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.Modular
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Convex.Contractible
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Generators and cusp representatives for `Γ₁(3) ⊆ SL₂(ℤ)`

* `lowerL = [[1, 0], [3, 1]] = S T⁻³ S⁻¹`;
* **`gammaOneThree_le_closure`**: `Γ₁(3) ≤ ⟨T, L⟩` (Euclidean algorithm on the lower-left entry:
  left multiplication by powers of `T` and of `L` keeps the congruence conditions and, for a
  balanced choice of the exponents, strictly decreases `|c|`);
* **`exists_decomposition`**: every `γ ∈ SL₂(ℤ)` is `ε h` or `ε h S Tᵐ` with `ε = ±1` and
  `h ∈ Γ₁(3)` (if `3 ∣ c` then `±γ ∈ Γ₁(3)`; otherwise `m = d c` makes `±γ T⁻ᵐ S⁻¹ ∈ Γ₁(3)`).
  So the cusps of `Γ₁(3)` are represented by `∞ = 1 • ∞` and `S Tᵐ • ∞`, and a slash-invariant
  function is controlled at every cusp by its behaviour at `∞` and that of its `S`-transform.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.LevelThree.GammaOneThreeCosets

open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup
open scoped MatrixGroups

/-- `L = [[1, 0], [3, 1]]`. -/
def lowerL : SL(2, ℤ) := ⟨!![1, 0; 3, 1], by simp [Matrix.det_fin_two_of]⟩

/-- `m ↦ Lᵐ = [[1, 0], [3m, 1]]`. -/
def lowerHom : Multiplicative ℤ →* SL(2, ℤ) where
  toFun m := ⟨!![1, 0; 3 * m.toAdd, 1], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' a b := by
    apply Subtype.ext
    change (!![1, 0; 3 * (a * b).toAdd, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, 0; 3 * a.toAdd, 1] * !![1, 0; 3 * b.toAdd, 1]
    rw [Matrix.mul_fin_two]
    simp [toAdd_mul, mul_add, add_comm]

theorem coe_lowerL_zpow (m : ℤ) :
    ((lowerL ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 3 * m, 1] := by
  have base : lowerL = lowerHom (Multiplicative.ofAdd 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have power : lowerL ^ m = lowerHom (Multiplicative.ofAdd m) := by
    rw [base, ← map_zpow]
    congr 1
    exact Multiplicative.toAdd.injective (by simp)
  rw [power]
  rfl

theorem lowerL_mul_S : lowerL * S = S * T ^ (-3 : ℤ) := by
  ext i j
  rw [coe_mul, coe_mul, coe_T_zpow]
  fin_cases i <;> fin_cases j <;>
    simp [lowerL, coe_S, Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerL_eq : lowerL = S * T ^ (-3 : ℤ) * S⁻¹ := by
  rw [← lowerL_mul_S, mul_inv_cancel_right]

theorem T_mem : T ∈ Gamma1 3 := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem lowerL_mem : lowerL ∈ Gamma1 3 := by
  rw [Gamma1_mem]
  refine ⟨by simp [lowerL], by simp [lowerL], ?_⟩
  simp only [lowerL, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  decide

/-- Balanced division with remainder: some `v + q M` has absolute value at most `|M| / 2`. -/
theorem balanced_remainder (v M : ℤ) (hM : M ≠ 0) : ∃ q : ℤ, 2 * |v + q * M| ≤ |M| := by
  have h1 := Int.mul_ediv_add_emod v M
  have h2 := Int.emod_nonneg v hM
  have h3 := Int.emod_lt_abs v hM
  generalize v % M = r at h1 h2 h3
  generalize v / M = s at h1
  by_cases h : 2 * r ≤ |M|
  · refine ⟨-s, ?_⟩
    rw [show v + -s * M = r by linear_combination -h1, abs_of_nonneg h2]
    exact h
  · rcases lt_or_gt_of_ne hM with hneg | hpos
    · refine ⟨-s + 1, ?_⟩
      rw [abs_of_neg hneg] at h h3 ⊢
      rw [show v + (-s + 1) * M = r + M by linear_combination -h1]
      rw [abs_of_nonpos (by omega)]
      omega
    · refine ⟨-s - 1, ?_⟩
      rw [abs_of_pos hpos] at h h3 ⊢
      rw [show v + (-s - 1) * M = r - M by linear_combination -h1]
      rw [abs_of_nonpos (by omega)]
      omega

theorem det_entries (γ : SL(2, ℤ)) :
    γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
  have h := γ.2
  rw [Matrix.det_fin_two] at h
  exact h

theorem T_zpow_mul_entries (n : ℤ) (γ : SL(2, ℤ)) :
    (T ^ n * γ).1 0 0 = γ.1 0 0 + n * γ.1 1 0 ∧ (T ^ n * γ).1 0 1 = γ.1 0 1 + n * γ.1 1 1 ∧
      (T ^ n * γ).1 1 0 = γ.1 1 0 ∧ (T ^ n * γ).1 1 1 = γ.1 1 1 := by
  have e : (T ^ n * γ).1 = (T ^ n).1 * γ.1 := rfl
  rw [e]
  have eT : (T ^ n).1 = !![1, n; 0, 1] := coe_T_zpow n
  rw [eT]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerL_zpow_mul_entries (m : ℤ) (γ : SL(2, ℤ)) :
    (lowerL ^ m * γ).1 0 0 = γ.1 0 0 ∧ (lowerL ^ m * γ).1 0 1 = γ.1 0 1 ∧
      (lowerL ^ m * γ).1 1 0 = γ.1 1 0 + 3 * m * γ.1 0 0 ∧
      (lowerL ^ m * γ).1 1 1 = γ.1 1 1 + 3 * m * γ.1 0 1 := by
  have e : (lowerL ^ m * γ).1 = (lowerL ^ m).1 * γ.1 := rfl
  rw [e]
  have eL : (lowerL ^ m).1 = !![1, 0; 3 * m, 1] := coe_lowerL_zpow m
  rw [eL]
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem mem_closure_aux (N : ℕ) : ∀ γ : SL(2, ℤ), (γ.1 1 0).natAbs = N → γ ∈ Gamma1 3 →
    γ ∈ Subgroup.closure ({T, lowerL} : Set SL(2, ℤ)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro γ hN hγ
  set H := Subgroup.closure ({T, lowerL} : Set SL(2, ℤ))
  have hT : T ∈ H := Subgroup.subset_closure (by simp)
  have hL : lowerL ∈ H := Subgroup.subset_closure (by simp)
  have hmem := (Gamma1_mem 3 γ).mp hγ
  have hdet := det_entries γ
  have hc3 : (3 : ℤ) ∣ γ.1 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hmem.2.2
  by_cases hc : γ.1 1 0 = 0
  · -- upper triangular: `γ = T ^ b`
    rw [hc, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with ha | ha
    · have hd : γ.1 1 1 = 1 := by rw [ha, one_mul] at hdet; exact hdet
      have e : γ = T ^ (γ.1 0 1) := by
        ext i j
        rw [coe_T_zpow]
        fin_cases i <;> fin_cases j
        · exact ha
        · rfl
        · exact hc
        · exact hd
      rw [e]
      exact H.zpow_mem hT _
    · exfalso
      have h1 := hmem.1
      rw [ha] at h1
      revert h1
      decide
  · obtain ⟨n, hn⟩ := balanced_remainder (γ.1 0 0) (γ.1 1 0) hc
    set γ₁ := T ^ n * γ with hγ₁
    obtain ⟨e00, e01, e10, e11⟩ := T_zpow_mul_entries n γ
    rw [← hγ₁] at e00 e01 e10 e11
    have ha₁ : γ₁.1 0 0 ≠ 0 := by
      intro h0
      have hdet₁ := det_entries γ₁
      rw [h0, zero_mul, zero_sub, e10] at hdet₁
      obtain ⟨t, ht⟩ := hc3
      rw [ht] at hdet₁
      have : (3 : ℤ) ∣ 1 := ⟨-(γ₁.1 0 1 * t), by linear_combination -hdet₁⟩
      omega
    obtain ⟨m, hm⟩ := balanced_remainder (γ.1 1 0) (3 * γ₁.1 0 0) (by positivity)
    set γ₂ := lowerL ^ m * γ₁ with hγ₂
    obtain ⟨f00, -, f10, -⟩ := lowerL_zpow_mul_entries m γ₁
    rw [← hγ₂] at f00 f10
    have hsmall : (γ₂.1 1 0).natAbs < N := by
      rw [← hN]
      have hb : 2 * |γ.1 1 0 + m * (3 * γ₁.1 0 0)| ≤ 3 * |γ₁.1 0 0| := by
        simpa [abs_mul] using hm
      have hn' : 2 * |γ₁.1 0 0| ≤ |γ.1 1 0| := by rw [e00]; exact hn
      have hpos : 0 < |γ.1 1 0| := abs_pos.mpr hc
      have hlt : |γ₂.1 1 0| < |γ.1 1 0| := by
        rw [f10, e10, show γ.1 1 0 + 3 * m * γ₁.1 0 0 = γ.1 1 0 + m * (3 * γ₁.1 0 0) by ring]
        linarith
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hlt
      exact_mod_cast hlt
    have hγ₂mem : γ₂ ∈ Gamma1 3 :=
      (Gamma1 3).mul_mem ((Gamma1 3).zpow_mem lowerL_mem m)
        ((Gamma1 3).mul_mem ((Gamma1 3).zpow_mem T_mem n) hγ)
    have h₂ := ih _ hsmall γ₂ rfl hγ₂mem
    have e : γ = (T ^ n)⁻¹ * (lowerL ^ m)⁻¹ * γ₂ := by
      rw [hγ₂, hγ₁]
      group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem (H.zpow_mem hT n)) (H.inv_mem (H.zpow_mem hL m))) h₂

/-- **`Γ₁(3) ≤ ⟨T, L⟩`.** -/
theorem gammaOneThree_le_closure :
    Gamma1 3 ≤ Subgroup.closure ({T, lowerL} : Set SL(2, ℤ)) :=
  fun γ hγ => mem_closure_aux _ γ rfl hγ

theorem cast_det (γ : SL(2, ℤ)) :
    ((γ.1 0 0 : ℤ) : ZMod 3) * (γ.1 1 1 : ZMod 3) - (γ.1 0 1 : ZMod 3) * (γ.1 1 0 : ZMod 3) =
      1 := by
  have h := congrArg (Int.cast : ℤ → ZMod 3) (det_entries γ)
  push_cast at h
  exact h

theorem zmod_d (a b c d : ZMod 3) (h : a * d - b * c = 1) (hc : c = 0) (ha : a = 1) : d = 1 := by
  revert a b c d; decide

theorem zmod_neg_a (a b c d : ZMod 3) (h : a * d - b * c = 1) (hc : c = 0) (ha : a ≠ 1) :
    -a = 1 := by
  revert a b c d; decide

theorem zmod_neg_d (a b c d : ZMod 3) (h : a * d - b * c = 1) (hc : c = 0) (ha : a ≠ 1) :
    -d = 1 := by
  revert a b c d; decide

theorem zmod_top (a b c d : ZMod 3) (h : a * d - b * c = 1) (hc : c = 1) :
    d * c * a - b = 1 := by
  revert a b c d; decide

theorem zmod_bottom (c d : ZMod 3) (hc : c ≠ 0) : d * c * c - d = 0 := by
  revert c d; decide

theorem zmod_neg_top (a b c d : ZMod 3) (h : a * d - b * c = 1) (hc : c ≠ 0) (hc1 : c ≠ 1) :
    -(d * c * a - b) = 1 := by
  revert a b c d; decide

theorem zmod_neg_c (c : ZMod 3) (hc : c ≠ 0) (hc1 : c ≠ 1) : -c = 1 := by
  revert c; decide

/-- **Cusp representatives.** Every `γ ∈ SL₂(ℤ)` is `ε h` or `ε h S Tᵐ` with `ε = ±1` and
`h ∈ Γ₁(3)`. -/
theorem exists_decomposition (γ : SL(2, ℤ)) :
    ∃ ε h : SL(2, ℤ), (ε = 1 ∨ ε = -1) ∧ h ∈ Gamma1 3 ∧
      (γ = ε * h ∨ ∃ m : ℤ, γ = ε * h * S * T ^ m) := by
  have hdet := cast_det γ
  by_cases hc : ((γ.1 1 0 : ℤ) : ZMod 3) = 0
  · by_cases ha : ((γ.1 0 0 : ℤ) : ZMod 3) = 1
    · refine ⟨1, γ, Or.inl rfl, ?_, Or.inl (one_mul γ).symm⟩
      rw [Gamma1_mem]
      exact ⟨ha, zmod_d _ _ _ _ hdet hc ha, hc⟩
    · refine ⟨-1, -γ, Or.inr rfl, ?_, Or.inl (by simp)⟩
      rw [Gamma1_mem]
      simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
      exact ⟨zmod_neg_a _ _ _ _ hdet hc ha, zmod_neg_d _ _ _ _ hdet hc ha, by rw [hc, neg_zero]⟩
  · have hdetZ := det_entries γ
    let h : SL(2, ℤ) := ⟨!![γ.1 1 1 * γ.1 1 0 * γ.1 0 0 - γ.1 0 1, γ.1 0 0;
      γ.1 1 1 * γ.1 1 0 * γ.1 1 0 - γ.1 1 1, γ.1 1 0], by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetZ⟩
    have e00 : h.1 0 0 = γ.1 1 1 * γ.1 1 0 * γ.1 0 0 - γ.1 0 1 := rfl
    have e10 : h.1 1 0 = γ.1 1 1 * γ.1 1 0 * γ.1 1 0 - γ.1 1 1 := rfl
    have e11 : h.1 1 1 = γ.1 1 0 := rfl
    have hγ : γ = h * S * T ^ (γ.1 1 1 * γ.1 1 0) := by
      ext i j
      rw [coe_mul, coe_mul, coe_T_zpow]
      fin_cases i <;> fin_cases j <;>
        simp [h, coe_S, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    by_cases hc1 : ((γ.1 1 0 : ℤ) : ZMod 3) = 1
    · refine ⟨1, h, Or.inl rfl, ?_, Or.inr ⟨_, by rw [one_mul]; exact hγ⟩⟩
      rw [Gamma1_mem, e00, e10, e11]
      push_cast
      exact ⟨zmod_top _ _ _ _ hdet hc1, hc1, zmod_bottom _ _ hc⟩
    · refine ⟨-1, -h, Or.inr rfl, ?_, Or.inr ⟨_, by simpa using hγ⟩⟩
      rw [Gamma1_mem]
      simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
      rw [e00, e10, e11]
      push_cast
      refine ⟨zmod_neg_top _ _ _ _ hdet hc hc1, zmod_neg_c _ hc hc1, ?_⟩
      rw [zmod_bottom _ _ hc, neg_zero]

end TernaryPeriodPolynomials.LevelThree.GammaOneThreeCosets
