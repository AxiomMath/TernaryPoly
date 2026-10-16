module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Gamma2Defs
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# The Bass-Serre/Schreier argument for `Γ₂`

Paper: "To verify
completeness, the determinant-one subgroup maps injectively to an index-four subgroup of
`PSL₂(ℤ) = SL₂(ℤ)/{±I₂} ≅ C₂*C₃`. On its four cosets the two generators act with cycle types
`(2,2)` and `(3,1)`. The Bass-Serre quotient has four edges and four vertices, one `C₃` vertex
stabilizer, and all other stabilizers trivial. Schreier reduction uses the standard matrices `S` and
`T`. The representatives `1, S, ST, ST²` give `⟨A₀, U₀ | A₀³ = 1⟩`, where `U₀ = (1 0; 3 1)` and
`A₀ = U₀T⁻¹`. Matrix multiplication gives `R₀U₀R₀ = U₀⁻¹` and `R₀A₀R₀ = U₀⁻¹A₀⁻¹U₀`. Set
`B₀ = U₀R₀` to obtain `eq:Gamma-presentation`, with no extra mixed relation."

Proved here (Mathlib's `Gamma0 3 = ±Γ₁(3)`, Schreier's lemma and `SL₂(ℤ) = ⟨S, T⟩`):

* `-1 ∉ Γ₁(3)` (`neg_one_mem_Gamma1_iff`): `Γ₁(3)` injects into `PSL₂(ℤ)` with image `Γ₀(3)/±1`, and
  `Γ₀(3) = Γ₁(3) ∪ -Γ₁(3)` (`Gamma0_eq_pm_Gamma1`);
* `isComplement`: `{1, S, ST, ST²}` is a right transversal of `Γ₀(3)` in `SL₂(ℤ)` (index four);
* `actS`, `actST`, `actT`, `cycle_types`: the action on the four cosets, `S` has cycle type `(2,2)`,
  `ST` has cycle type `(3,1)`;
* `schreier_values`: the eight Schreier generators `r_i x r_{σ_x(i)}⁻¹` are `1, -1, U₀⁻¹A₀U₀,
  -U₀⁻¹A₀⁻¹U₀, A₀⁻¹U₀ (= T), 1, 1, U₀⁻¹`;
* `gamma0_three_eq_closure` and `gamma1_three_eq_closure`: `Γ₀(3) = ⟨-1, A₀, U₀⟩`, `Γ₁(3) = ⟨A₀, U₀⟩`.

Not formalized here: the Bass-Serre structure theorem (that the quotient graph of groups makes
`Γ₁(3)` the free product `⟨A₀⟩ * ⟨U₀⟩ ≅ C₃ * ℤ`) and `PSL₂(ℤ) ≅ C₂*C₃`.  The conclusion
`eq:Gamma-presentation` itself, i.e. that `Γ₂ = ⟨A₀,B₀⟩ * ⟨R₀⟩ ≅ 𝔖₃ * C₂` with no further relation, is
proved independently by the ping-pong argument of `Gamma2Presentation`
(`Exports/FiberModel.gamma2_free_product`).  The relations `R₀U₀R₀ = U₀⁻¹`, `R₀A₀R₀ = U₀⁻¹A₀⁻¹U₀`
are `Gamma2Defs.R0_U0`, `R0_A0`.

Formalized by Claude Sonnet 5.5.
-/
open Matrix MatrixGroups CongruenceSubgroup Subgroup ModularGroup
open scoped Pointwise

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FiberModel.BassSerre

def rep : Fin 4 → SL(2, ℤ) := ![1, S, S * T, S * T * T]

theorem rep_entries (i : Fin 4) : ((rep i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    ![!![1, 0; 0, 1], !![0, -1; 1, 0], !![0, -1; 1, 1], !![0, -1; 1, 2]] i := by
  fin_cases i
  · simp [rep, Matrix.one_fin_two]
  · simp [rep]
  · simp only [rep, Fin.reduceFinMk, Matrix.cons_val, Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T]
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [rep, Fin.reduceFinMk, Matrix.cons_val, Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T]
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def condB (i : Fin 4) (c d : ZMod 3) : Bool :=
  match i with
  | 0 => c == 0
  | 1 => d == 0
  | 2 => c == d
  | 3 => d == 2 * c

def cond (i : Fin 4) (c d : ZMod 3) : Prop := condB i c d = true

instance (i : Fin 4) (c d : ZMod 3) : Decidable (cond i c d) := by
  unfold cond; infer_instance

theorem cond_unique : ∀ c d : ZMod 3, (c ≠ 0 ∨ d ≠ 0) →
    ∃ i : Fin 4, cond i c d ∧ ∀ j : Fin 4, cond j c d → j = i := by decide

theorem mem_Gamma0_mul_inv (g : SL(2, ℤ)) (i : Fin 4) :
    g * (rep i)⁻¹ ∈ Gamma0 3 ↔ cond i (g 1 0 : ZMod 3) (g 1 1 : ZMod 3) := by
  rw [Gamma0_mem]
  have h : (((g * (rep i)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) =
      (g 1 0) * ((rep i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (g 1 1) * ((rep i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h2 : (((g * (rep i)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 3) = 
      (g 1 0 : ZMod 3) * (((rep i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3) -
        (g 1 1 : ZMod 3) * (((rep i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 3) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h
  rw [h2, rep_entries]
  generalize (g 1 0 : ZMod 3) = c
  generalize (g 1 1 : ZMod 3) = d
  revert c d
  fin_cases i <;> decide

theorem bottom_row_ne_zero (g : SL(2, ℤ)) : (g 1 0 : ZMod 3) ≠ 0 ∨ (g 1 1 : ZMod 3) ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (Int.cast : ℤ → ZMod 3) hdet
  push_cast at this
  rw [h.1, h.2] at this
  simp at this

/-- **The representatives `1, S, ST, ST²` form a right transversal of `Γ₀(3) = ±Γ₁(3)` in
`SL₂(ℤ)`** (index four). -/
theorem isComplement : Subgroup.IsComplement (Gamma0 3 : Set SL(2, ℤ)) (Set.range rep) := by
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro g
  obtain ⟨i, hi, huniq⟩ := cond_unique _ _ (bottom_row_ne_zero g)
  refine ⟨⟨rep i, ⟨i, rfl⟩⟩, ?_, ?_⟩
  · exact (mem_Gamma0_mul_inv g i).mpr hi
  · rintro ⟨_, j, rfl⟩ hj
    have := huniq j ((mem_Gamma0_mul_inv g j).mp hj)
    subst this
    rfl

/-- The right action of `x` on the four cosets: `r_i x r_j⁻¹ ∈ Γ₀(3)` iff `j = σ_x(i)`. -/
theorem action_iff (x : SL(2, ℤ)) (σ : Fin 4 → Fin 4)
    (h : ∀ i, cond (σ i) (((rep i * x : SL(2, ℤ)) 1 0 : ℤ) : ZMod 3) (((rep i * x : SL(2, ℤ)) 1 1 : ℤ) : ZMod 3)) (i j : Fin 4) :
    rep i * x * (rep j)⁻¹ ∈ Gamma0 3 ↔ j = σ i := by
  rw [mem_Gamma0_mul_inv]
  obtain ⟨k, hk, hu⟩ := cond_unique _ _ (bottom_row_ne_zero (rep i * x))
  constructor
  · intro hj
    rw [hu j hj, ← hu (σ i) (h i)]
  · rintro rfl; exact h i

theorem actS : ∀ i j, rep i * S * (rep j)⁻¹ ∈ Gamma0 3 ↔ j = ![1, 0, 3, 2] i := by
  apply action_iff
  intro i
  fin_cases i <;> simp [rep_entries, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> decide

theorem actT : ∀ i j, rep i * T * (rep j)⁻¹ ∈ Gamma0 3 ↔ j = ![0, 2, 3, 1] i := by
  apply action_iff
  intro i
  fin_cases i <;> simp [rep_entries, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> decide

theorem actST : ∀ i j, rep i * (S * T) * (rep j)⁻¹ ∈ Gamma0 3 ↔ j = ![2, 0, 1, 3] i := by
  apply action_iff
  intro i
  fin_cases i <;> simp [rep_entries, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> decide

/-- **Cycle types on the four cosets** ("On its four cosets the two generators act
with cycle types `(2,2)` and `(3,1)`"): `S` acts as `(0 1)(2 3)`, and `ST` as the three-cycle
`0 → 2 → 1 → 0` fixing `3`; (and `T` acts as the three-cycle `1 → 2 → 3 → 1` fixing `0`). -/
theorem cycle_types :
    (∀ i : Fin 4, (![1, 0, 3, 2] : Fin 4 → Fin 4) ((![1, 0, 3, 2] : Fin 4 → Fin 4) i) = i ∧
      (![1, 0, 3, 2] : Fin 4 → Fin 4) i ≠ i) ∧
    (∀ i : Fin 4, (![2, 0, 1, 3] : Fin 4 → Fin 4) ((![2, 0, 1, 3] : Fin 4 → Fin 4)
        ((![2, 0, 1, 3] : Fin 4 → Fin 4) i)) = i ∧
      ((![2, 0, 1, 3] : Fin 4 → Fin 4) i = i ↔ i = 3)) := by decide

/-- `A₀ = (1 -1; 3 -2)` as an element of `SL₂(ℤ)`. -/
def A : SL(2, ℤ) := ⟨!![1, -1; 3, -2], by simp [Matrix.det_fin_two_of]⟩
/-- `U₀ = (1 0; 3 1)` as an element of `SL₂(ℤ)`. -/
def U : SL(2, ℤ) := ⟨!![1, 0; 3, 1], by simp [Matrix.det_fin_two_of]⟩

theorem toRightFun_eq (x : SL(2, ℤ)) (σ : Fin 4 → Fin 4) (i : Fin 4)
    (h : ∀ j, rep i * x * (rep j)⁻¹ ∈ Gamma0 3 ↔ j = σ i) :
    (isComplement.toRightFun (rep i * x) : SL(2, ℤ)) = rep (σ i) := by
  obtain ⟨j, hj⟩ := (isComplement.toRightFun (rep i * x)).2
  have hmem := isComplement.mul_inv_toRightFun_mem (rep i * x)
  have e : (isComplement.toRightFun (rep i * x) : SL(2, ℤ)) = rep j := hj.symm
  rw [e] at hmem ⊢
  rw [(h j).mp hmem]

@[simp] theorem coe_A : (A : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 3, -2] := rfl
@[simp] theorem coe_U : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 3, 1] := rfl

/-- Reidemeister-Schreier generators for the transversal `{1, S, ST, ST²}` and the generators
`S, T` of `SL₂(ℤ)`: in `SL₂(ℤ)` they are `1, -1, U₀⁻¹ A₀ U₀, -U₀⁻¹ A₀⁻¹ U₀`
(for `S`) and `A₀⁻¹ U₀ (= T), 1, 1, U₀⁻¹` (for `T`). -/
theorem schreier_values :
    rep 0 * S * (rep 1)⁻¹ = 1 ∧ rep 1 * S * (rep 0)⁻¹ = -1 ∧
    rep 2 * S * (rep 3)⁻¹ = U⁻¹ * A * U ∧ rep 3 * S * (rep 2)⁻¹ = (-1) * (U⁻¹ * A⁻¹ * U) ∧
    rep 0 * T * (rep 0)⁻¹ = A⁻¹ * U ∧ rep 1 * T * (rep 2)⁻¹ = 1 ∧
    rep 2 * T * (rep 3)⁻¹ = 1 ∧ rep 3 * T * (rep 1)⁻¹ = U⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [rep_entries, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, coe_A, coe_U, Matrix.mul_apply, Fin.sum_univ_two, coe_S, coe_T]

theorem A_mem : A ∈ Gamma0 3 := by rw [Gamma0_mem]; simp [coe_A]; decide
theorem U_mem : U ∈ Gamma0 3 := by rw [Gamma0_mem]; simp [coe_U]; decide
theorem negOne_mem : (-1 : SL(2, ℤ)) ∈ Gamma0 3 := by rw [Gamma0_mem]; simp

/-- **Schreier reduction**: with the transversal `1, S, ST, ST²` and the generators
`S, T` of `SL₂(ℤ)`, Schreier's lemma shows that `Γ₀(3) = ±Γ₁(3)` is generated by `-1, A₀, U₀`
(`U₀ = (1 0; 3 1)`, `A₀ = U₀ T⁻¹ = (1 -1; 3 -2)`). -/
theorem gamma0_three_eq_closure :
    Gamma0 3 = Subgroup.closure ({-1, A, U} : Set SL(2, ℤ)) := by
  apply le_antisymm
  · have hS := Subgroup.closure_mul_image_eq isComplement (Set.mem_range_self (0 : Fin 4))
      (SpecialLinearGroup.SL2Z_generators)
    rw [← hS, Subgroup.closure_le]
    obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := schreier_values
    have hA : A ∈ Subgroup.closure ({-1, A, U} : Set SL(2, ℤ)) :=
      Subgroup.subset_closure (by simp)
    have hU : U ∈ Subgroup.closure ({-1, A, U} : Set SL(2, ℤ)) :=
      Subgroup.subset_closure (by simp)
    have hm : (-1 : SL(2, ℤ)) ∈ Subgroup.closure ({-1, A, U} : Set SL(2, ℤ)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, b, hb, rfl⟩, rfl⟩
    beta_reduce
    rcases hb with rfl | rfl
    · rw [toRightFun_eq S _ i (actS i)]
      fin_cases i
      · show rep 0 * S * (rep 1)⁻¹ ∈ _
        rw [v1]; exact one_mem _
      · show rep 1 * S * (rep 0)⁻¹ ∈ _
        rw [v2]; exact hm
      · show rep 2 * S * (rep 3)⁻¹ ∈ _
        rw [v3]; exact mul_mem (mul_mem (inv_mem hU) hA) hU
      · show rep 3 * S * (rep 2)⁻¹ ∈ _
        rw [v4]; exact mul_mem hm (mul_mem (mul_mem (inv_mem hU) (inv_mem hA)) hU)
    · rw [toRightFun_eq T _ i (actT i)]
      fin_cases i
      · show rep 0 * T * (rep 0)⁻¹ ∈ _
        rw [v5]; exact mul_mem (inv_mem hA) hU
      · show rep 1 * T * (rep 2)⁻¹ ∈ _
        rw [v6]; exact one_mem _
      · show rep 2 * T * (rep 3)⁻¹ ∈ _
        rw [v7]; exact one_mem _
      · show rep 3 * T * (rep 1)⁻¹ ∈ _
        rw [v8]; exact inv_mem hU
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact negOne_mem
    · exact A_mem
    · exact U_mem

theorem neg_one_mem_Gamma1_iff : (-1 : SL(2, ℤ)) ∉ Gamma1 3 := by
  rw [Gamma1_mem]
  simp
  decide

/-- `Γ₀(3) = Γ₁(3) ∪ (-1) Γ₁(3)`. -/
theorem Gamma0_eq_pm_Gamma1 (g : SL(2, ℤ)) (hg : g ∈ Gamma0 3) :
    g ∈ Gamma1 3 ∨ (-1 : SL(2, ℤ)) * g ∈ Gamma1 3 := by
  rw [Gamma0_mem] at hg
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (Int.cast : ℤ → ZMod 3) hdet
  push_cast at h
  erw [hg, mul_zero, sub_zero] at h
  have hd : (g 1 1 : ZMod 3) = 1 ∨ (g 1 1 : ZMod 3) = 2 := by
    generalize (g 0 0 : ZMod 3) = a at h
    generalize (g 1 1 : ZMod 3) = d at h ⊢
    revert a d; decide
  have ha : (g 0 0 : ZMod 3) = (g 1 1 : ZMod 3) := by
    generalize (g 0 0 : ZMod 3) = a at h
    generalize (g 1 1 : ZMod 3) = d at h hd ⊢
    revert a d; decide
  rcases hd with hd | hd
  · left; rw [Gamma1_mem]; exact ⟨by rw [ha, hd], hd, hg⟩
  · right
    rw [Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_apply]
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> simp [hg, ha, hd] <;> decide

theorem negOne_comm (g : SL(2, ℤ)) : (-1 : SL(2, ℤ)) * g = g * (-1) := by
  apply Subtype.ext
  simp

theorem negOne_mul_negOne : (-1 : SL(2, ℤ)) * (-1) = 1 := by
  apply Subtype.ext
  simp

theorem A_mem_Gamma1 : A ∈ Gamma1 3 := by rw [Gamma1_mem]; simp [coe_A]; decide
theorem U_mem_Gamma1 : U ∈ Gamma1 3 := by rw [Gamma1_mem]; simp [coe_U]; decide

/-- **`Γ₁(3) = ⟨A₀, U₀⟩`**: the Schreier generators of `±Γ₁(3)` are `±1`, `A₀`,
`U₀`; since `-1 ∉ Γ₁(3)` and `-1` is central, the signs drop out. -/
theorem gamma1_three_eq_closure :
    Gamma1 3 = Subgroup.closure ({A, U} : Set SL(2, ℤ)) := by
  apply le_antisymm
  · intro g hg
    have hg0 : g ∈ Gamma0 3 := by
      have := (Gamma1_mem 3 g).mp hg
      rw [Gamma0_mem]; exact this.2.2
    rw [gamma0_three_eq_closure] at hg0
    set K := Subgroup.closure ({A, U} : Set SL(2, ℤ)) with hK
    have hKG : K ≤ Gamma1 3 := by
      rw [hK, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact A_mem_Gamma1
      · exact U_mem_Gamma1
    have key : ∀ x ∈ Subgroup.closure ({-1, A, U} : Set SL(2, ℤ)), x ∈ K ∨ (-1 : SL(2, ℤ)) * x ∈ K := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with rfl | rfl | rfl
        · right; rw [negOne_mul_negOne]; exact one_mem _
        · left; exact Subgroup.subset_closure (by simp)
        · left; exact Subgroup.subset_closure (by simp)
      | one => left; exact one_mem _
      | mul y z _ _ hy hz =>
        rcases hy with hy | hy <;> rcases hz with hz | hz
        · left; exact mul_mem hy hz
        · right; rw [← mul_assoc, negOne_comm y, mul_assoc]; exact mul_mem hy hz
        · right; rw [← mul_assoc]; exact mul_mem hy hz
        · left
          have : y * z = ((-1 : SL(2, ℤ)) * y) * ((-1) * z) := by
            rw [mul_assoc, ← mul_assoc y, ← negOne_comm y, mul_assoc, ← mul_assoc (-1), negOne_mul_negOne,
              one_mul]
          rw [this]; exact mul_mem hy hz
      | inv y _ hy =>
        rcases hy with hy | hy
        · left; exact inv_mem hy
        · right
          have hinv : ((-1 : SL(2, ℤ)))⁻¹ = -1 := inv_eq_of_mul_eq_one_right negOne_mul_negOne
          have : (-1 : SL(2, ℤ)) * y⁻¹ = (((-1) * y))⁻¹ := by
            rw [_root_.mul_inv_rev, hinv, negOne_comm]
          rw [this]; exact inv_mem hy
    rcases key g hg0 with h | h
    · exact h
    · exfalso
      apply neg_one_mem_Gamma1_iff
      have : (-1 : SL(2, ℤ)) = ((-1) * g) * g⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact mul_mem (hKG h) (inv_mem hg)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact A_mem_Gamma1
    · exact U_mem_Gamma1

/-- `A₀` and `U₀` of `Gamma2Defs` are the `SL₂(ℤ)` matrices `A`, `U`. -/
theorem A_val : (A : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.TernaryPeriodPolynomials.Argument.FiberModel.A0 : GL2Z).val := rfl
theorem U_val : (U : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.TernaryPeriodPolynomials.Argument.FiberModel.U0 : GL2Z).val := rfl

/-- `A₀` has order three in `SL₂(ℤ)`. -/
theorem A_cube : A ^ 3 = 1 := by
  apply Subtype.ext
  simp [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.one_fin_two]

end TernaryPeriodPolynomials.Argument.FiberModel.BassSerre
