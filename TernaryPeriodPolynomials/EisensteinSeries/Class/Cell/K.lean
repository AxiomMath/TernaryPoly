module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Slash

@[expose] public section


/-!
# The cell of the series at the cusp `k⁻¹ P k` (structure)

The cosets of the cusp `k⁻¹Pk` in `Γ(N)` whose bottom row `r_k γ` has vanishing first two entries
(`IsCellK`) are the cosets with `k γ ∈ P^±(ℤ)`; for `N ≥ 3` there is at most one
(`IsCellK_unique`: `k b (k a)⁻¹ ∈ Γ(N)` has bottom row `(0, 0, ±1)` hence `+1`). The cell sum is
the term of that coset (`cellCoeffK_eq`), or zero when there is none (`cellCoeffK_eq_zero`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section CellStructure

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem cuspRow_mk_eq (a : ↥(gammaN N)) (j : Fin 3) :
    cuspRow (gammaN N) (CuspData.ofSL k).r (Quotient.mk _ a) j =
      ((k * a.1 : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
  rw [cuspRow_mk]
  simp [CuspData.ofSL, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three]

theorem inv_row_zero {u : SL(3, ℤ)} (h0 : (u : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0)
    (h1 : (u : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0) :
    ((u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
  have hdet : (u : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := u.2
  rw [Matrix.det_fin_three, h0, h1] at hdet
  have hu22 : (u : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ≠ 0 := by
    intro h; rw [h] at hdet; simp at hdet
  have hmul : ((u * u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [mul_inv_cancel]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul] at hmul
  have e0 := congrFun (congrFun hmul 2) 0
  have e1 := congrFun (congrFun hmul 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1] at e0 e1
  exact ⟨by rcases e0 with e | e <;> simp_all, by rcases e1 with e | e <;> simp_all⟩

theorem mul_row_zero {w u : SL(3, ℤ)} (hw0 : (w : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0)
    (hw1 : (w : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0)
    (hi0 : ((u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0)
    (hi1 : ((u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0) :
    ((w * u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((w * u⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  constructor
  · rw [Matrix.mul_apply, Fin.sum_univ_three, hw0, hw1, hi0]; ring
  · rw [Matrix.mul_apply, Fin.sum_univ_three, hw0, hw1, hi1]; ring

omit [NeZero N] in
theorem IsCellK_unique (hN : 3 ≤ N) {c c' : Ck N k} (h : IsCellK N k c) (h' : IsCellK N k c') :
    c = c' := by
  induction c using Quotient.inductionOn with | _ a => ?_
  induction c' using Quotient.inductionOn with | _ b => ?_
  obtain ⟨ha0, ha1⟩ := h
  obtain ⟨hb0, hb1⟩ := h'
  rw [cuspRow_mk_eq] at ha0 ha1 hb0 hb1
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
  show (b * a⁻¹ : ↥(gammaN N)).1 ∈ stabRow (CuspData.ofSL k).r
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, mem_stabRow_ofSL]
  have hΓ : k * (b.1 * a.1⁻¹) * k⁻¹ ∈ gammaN N := by
    have hm : b.1 * a.1⁻¹ ∈ gammaN N := (gammaN N).mul_mem b.2 ((gammaN N).inv_mem a.2)
    have := (gammaN_normal N).conj_mem _ hm k
    simpa [mul_assoc] using this
  have e : k * (b.1 * a.1⁻¹) * k⁻¹ = (k * b.1) * (k * a.1)⁻¹ := by group
  rw [e] at hΓ ⊢
  obtain ⟨hi0, hi1⟩ := inv_row_zero ha0 ha1
  refine mem_planeStab_of_gammaN hN hΓ ?_ ?_
  · exact (mul_row_zero hb0 hb1 hi0 hi1).1
  · exact (mul_row_zero hb0 hb1 hi0 hi1).2

omit [NeZero N] in
theorem cellCoeffK_eq_zero (hnone : ∀ c : Ck N k, ¬ IsCellK N k c) (y : Fin 5 → ℝ) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) : cellCoeffK N k n f y i j m = 0 := by
  classical
  unfold cellCoeffK
  simp [hnone]

omit [NeZero N] in
theorem cellCoeffK_eq (hN : 3 ≤ N) {c₀ : Ck N k} (hc : IsCellK N k c₀) (y : Fin 5 → ℝ)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    cellCoeffK N k n f y i j m =
      (summandPoly n (hfun f) (realMat (k * (Quotient.out c₀).1)) y i j).coeff m := by
  classical
  unfold cellCoeffK
  rw [tsum_eq_single c₀]
  · rw [ite_eq_left hc]
    unfold termFunK
    rw [summandK_false, realMat_mul]
    rfl
  · intro c hne
    rw [ite_eq_right (fun hc' => hne (IsCellK_unique N k hN hc' hc))]

end CellStructure

end TernaryPeriodPolynomials.Argument.EisensteinClass
