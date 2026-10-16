module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionComposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.QExpansion

@[expose] public section


/-!
# Hecke recursion: eigenvalues

Formalized by Claude Sonnet 5.5.

`heckeC`, `latticeOp_eigen`: `λ h = T_p h` and `z ↦ z+1`-invariance give `T_{p^r} h = c_r h` with `c_0 = 1`, `c_1 = λ`, `c_{r+2} = λ c_{r+1} - p^{k-1} c_r`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion

open Finset Matrix TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

variable {p : ℕ}

/-! ### Eigenvalues -/

/-- The sequence `c_0 = 1`, `c_1 = λ`, `c_{r+2} = λ c_{r+1} - p^{k-1} c_r`. -/
def heckeC (k : ℤ) (p : ℕ) (lam : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam
  | (r + 2) => lam * heckeC k p lam (r + 1) - (p : ℂ) ^ (k - 1) * heckeC k p lam r

theorem hnfData_one : hnfData (p ^ 0) = {(1, 0, 1)} := by
  ext ⟨a, b, d⟩
  rw [pow_zero, mem_hnfData one_pos, mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have ha : a = 1 := Nat.eq_one_of_mul_eq_one_right h2
    have hd : d = 1 := Nat.eq_one_of_mul_eq_one_left h2
    subst ha hd
    simp only at h3
    have : b = 0 := by omega
    subst this
    rfl
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨one_pos, rfl, one_pos⟩

theorem latticeOp_pow_zero (k : ℤ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    latticeOp k (p ^ 0) F z = F z := by
  unfold latticeOp
  rw [hnfData_one, sum_singleton, hnfAct_zero]
  simp [hnfWeight]

theorem latticeOp_const_mul (k : ℤ) (n : ℕ) (c : ℂ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    latticeOp k n (fun w => c * F w) z = c * latticeOp k n F z := by
  unfold latticeOp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **The eigenvalue recursion**: if `λ h = T_p h` and `h` is invariant under `z ↦ z + 1`, then `T_{p^r} h = c_r h`. -/
theorem latticeOp_eigen (hp : p.Prime) (k : ℤ) {h : UpperHalfPlane → ℂ} (hper : PerInv h) (lam : ℂ)
    (hrel : ∀ z, lam * h z = latticeOp k (p ^ 1) h z) :
    ∀ r z, latticeOp k (p ^ r) h z = heckeC k p lam r * h z := by
  have key : ∀ r, (∀ z, latticeOp k (p ^ r) h z = heckeC k p lam r * h z) ∧
      (∀ z, latticeOp k (p ^ (r + 1)) h z = heckeC k p lam (r + 1) * h z) := by
    intro r
    induction r with
    | zero =>
      refine ⟨fun z => by rw [latticeOp_pow_zero]; simp [heckeC], fun z => ?_⟩
      rw [zero_add, ← hrel z]; simp [heckeC]
    | succ r ih =>
      refine ⟨ih.2, fun z => ?_⟩
      have hc := latticeOp_comp hp k hper r z
      have h1 : latticeOp k (p ^ (r + 1)) h = fun w => heckeC k p lam (r + 1) * h w := funext ih.2
      rw [h1, latticeOp_const_mul, ← hrel z, ih.1 z] at hc
      have : heckeC k p lam (r + 2) = lam * heckeC k p lam (r + 1) - (p : ℂ) ^ (k - 1) * heckeC k p lam r := rfl
      rw [this]
      linear_combination -hc
  exact fun r z => (key r).1 z

/-- `1`-periodicity of a slash-invariant form. -/
theorem perInv_of_period {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [SlashInvariantFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) : PerInv f := by
  intro z
  have : hnfAct (1, 1, 1) z = (1 : ℝ) +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [coe_hnfAct (by norm_num) (by norm_num), UpperHalfPlane.coe_vadd]
    simp [add_comm]
  rw [this]
  exact SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f z hΓ

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
