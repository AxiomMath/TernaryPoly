module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSFlagPrimitive

@[expose] public section


/-!
# The flag primitive for a cyclic cusp stabilizer

Formalized by Claude Sonnet 5.5.

`cycSum T T⁻¹ v k` is the crossed homomorphism of `ℤ` with `cycSum 1 = v`: `v + T v + ⋯ + T^{k-1} v` for `k ≥ 0` and the inverse recursion for `k < 0`.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Cyc

variable {X : Type*} [AddCommGroup X] [Module ℂ X] (T Tinv : X →ₗ[ℂ] X) (v : X)

/-- `k ≥ 0`: `S₀ = 0`, `S_{k+1} = v + T S_k`. -/
def natSumAux : ℕ → X
  | 0 => 0
  | k + 1 => v + T (natSumAux k)

/-- `k ≥ 0`: `S'₀ = 0`, `S'_{k+1} = T⁻¹ (S'_k - v)`. -/
def negSumAux : ℕ → X
  | 0 => 0
  | k + 1 => Tinv (negSumAux k - v)

/-- The crossed homomorphism of `ℤ` determined by its value `v` at `1`. -/
def cycSum : ℤ → X
  | Int.ofNat k => natSumAux T v k
  | Int.negSucc k => negSumAux Tinv v (k + 1)

variable {T Tinv v}

theorem cycSum_zero : cycSum T Tinv v 0 = 0 := rfl

theorem cycSum_succ (hT : ∀ x, T (Tinv x) = x) (k : ℤ) :
    cycSum T Tinv v (k + 1) = v + T (cycSum T Tinv v k) := by
  cases k with
  | ofNat m => rfl
  | negSucc m =>
    cases m with
    | zero => simp [cycSum, natSumAux, negSumAux, hT]
    | succ m' =>
      have e : (Int.negSucc (m' + 1)) + 1 = Int.negSucc m' := rfl
      rw [e]
      simp [cycSum, negSumAux, hT]

theorem zpow_vanish (S : X →ₗ[ℂ] X) (hS : Function.Injective S) (D : ℤ → X) (h0 : D 0 = 0)
    (hD : ∀ k, D (k + 1) = S (D k)) : ∀ k, D k = 0 := by
  intro k
  induction k using Int.induction_on with
  | zero => exact h0
  | succ i ih => rw [hD, ih, map_zero]
  | pred i ih =>
    have h := hD (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih] at h
    exact hS (by rw [map_zero]; exact h.symm)

end Cyc

section Crossed

variable {N E L : Type} [Group N] [Group E] [Group L] {extension : GroupExtension N E L}
  (splitting : extension.Splitting) (W : Rep ℂ E) (σ : L) (v : W)

/-- `cycSum` for `T = ρ(s σ)`. -/
abbrev cycW (k : ℤ) : W :=
  cycSum (W.ρ (splitting σ)) (W.ρ (splitting σ⁻¹)) v k

theorem rho_s_inv_left (x : W) : W.ρ (splitting σ) (W.ρ (splitting σ⁻¹) x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]

theorem rho_s_inv_right (x : W) : W.ρ (splitting σ⁻¹) (W.ρ (splitting σ) x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

/-- **`cycW` is a crossed homomorphism on the powers of `σ`.** -/
theorem cycW_crossed (j k : ℤ) :
    cycW splitting W σ v (j + k) = W.ρ (splitting (σ ^ j)) (cycW splitting W σ v k) + cycW splitting W σ v j := by
  induction j using Int.induction_on with
  | zero => simp [cycW, cycSum_zero]
  | succ i ih =>
    have e1 : (i : ℤ) + 1 + k = (i + k) + 1 := by ring
    simp only [cycW] at ih ⊢
    rw [e1, cycSum_succ (rho_s_inv_left splitting W σ), cycSum_succ (rho_s_inv_left splitting W σ) (i : ℤ)]
    rw [ih, add_comm (i : ℤ) 1, zpow_add, zpow_one, map_mul, map_mul, Module.End.mul_apply, map_add]
    abel
  | pred i ih =>
    have e1 : -(i : ℤ) - 1 + k + 1 = -(i : ℤ) + k := by ring
    have h1 := cycSum_succ (T := W.ρ (splitting σ)) (Tinv := W.ρ (splitting σ⁻¹)) (v := v)
      (rho_s_inv_left splitting W σ) (-(i : ℤ) - 1 + k)
    have h2 := cycSum_succ (T := W.ρ (splitting σ)) (Tinv := W.ρ (splitting σ⁻¹)) (v := v)
      (rho_s_inv_left splitting W σ) (-(i : ℤ) - 1)
    rw [e1] at h1
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h2
    have h3 : cycSum (W.ρ (splitting σ)) (W.ρ (splitting σ⁻¹)) v (-(i : ℤ) - 1 + k) =
        W.ρ (splitting σ⁻¹) (cycSum (W.ρ (splitting σ)) (W.ρ (splitting σ⁻¹)) v (-(i : ℤ) + k) - v) := by
      rw [h1, add_sub_cancel_left, rho_s_inv_right]
    have h4 : cycSum (W.ρ (splitting σ)) (W.ρ (splitting σ⁻¹)) v (-(i : ℤ) - 1) =
        W.ρ (splitting σ⁻¹) (cycSum (W.ρ (splitting σ)) (W.ρ (splitting σ⁻¹)) v (-(i : ℤ)) - v) := by
      rw [h2, add_sub_cancel_left, rho_s_inv_right]
    have e2 : -(i : ℤ) - 1 + k = -(i : ℤ) - 1 + k := rfl
    simp only [cycW] at ih ⊢
    rw [h3, h4, ih, sub_eq_add_neg (-(i : ℤ)) 1, show σ ^ (-(i : ℤ) + -1) = σ⁻¹ * σ ^ (-(i : ℤ)) by
      rw [add_comm, zpow_add, zpow_neg_one], map_mul, map_mul, Module.End.mul_apply]
    simp only [map_sub, map_add]
    abel

end Crossed

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
