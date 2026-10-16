module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.CupEval

@[expose] public section



/-!
# M3c(iii): the seven-term sum of the flag cup cochains in Hochschild-Serre normal form

Formalized by Claude Sonnet 5.5.

`sum7 X Y c` is the value of a `3`-cochain on the Heisenberg bar cycle (`FlagH3.lam_eval`: `λ[c] = sum7 X Y c` for cocycles `c`; `FlagCohomDatum.lam_eval_sub`: `λ[c₁ - c₂] = Σ7 c₁ - Σ7 c₂` when the difference is a cocycle).
For the normal form `z(g₁, g₂) = ρ(r₁)[c̃(σ₁)(σ₁·r₂)]` (`g = r σ`, `c̃` a crossed homomorphism into `Z¹(R, -)`, so `z(r, ·) = 0` for `r` in the radical and `z(Y, r) = κ(σ·r)` with `κ = c̃(σ)`):
* `sum7_cup12_flag`: `Σ7(cup12 u β) = e(u X, X W⁻¹ · κ'(W)) - e(u W, κ'(X))`, independent of `u(Y)` (`u` need not be a cocycle: it is the flag primitive `w̄`);
* `sum7_cup21_flag`: `Σ7(cup21 α w) = e(κ(W), Y W · w(X)) - e(κ(W⁻¹X), Y X · w(W))`.
Here `X` is a radical element, `Y` the lift of the cusp generator `σ`, `W = [X,Y]` (the `σ`-fixed radical element).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {B : Type} [Group B]

/-- The seven-term sum of a `3`-cochain on the pair `(X, Y)`: the value on the Heisenberg bar cycle. -/
def sum7 (X Y : B) (c : B → B → B → ℚ) : ℚ :=
  c X (X⁻¹ * Y * X) (comm X Y) - c Y X (comm X Y) + c Y (comm X Y) X - c X (comm X Y) (X⁻¹ * Y * X) +
    c (comm X Y) X (X⁻¹ * Y * X) - c (comm X Y) Y X - c (comm X Y) (X⁻¹ * Y * X) (comm X Y)

theorem chainEval_heisCycle (X Y : B) (c : B → B → B → ℚ) :
    chainEval (heisCycle X Y) (fun g : Fin 3 → B => c (g 0) (g 1) (g 2)) = sum7 X Y c :=
  heisCycle_eval X Y c

/-- **M3c(iii): the seven-term sum of `cup12 u β` for a Hochschild-Serre normal-form `β`.**
Parameters: `W = [X,Y]` commutes with `X` and `Y`; `β(r, g) = 0` for the radical elements `r = X, W` (`c̃'(1) = 0`);
`κ' = c̃'(σ)` restricted to the radical is a cocycle (`κ'(ab) = κ'(a) + a·κ'(b)`) and
`β(Y, X) = κ'(σ·X)`, `β(Y', W) = W⁻¹·κ'(σ·W)` (with `σ·r = Y r Y⁻¹`, `Y' = W⁻¹ Y`).  Then
`Σ7(cup12 u β) = e(u X, X W⁻¹ · κ'(W)) - e(u W, κ'(X))`, independent of `u(Y)`. -/
theorem sum7_cup12_flag {V W' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W'] [Module ℚ W']
    (ρ' : Representation ℚ B W') (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ) (X Y : B) (u : B → V) (β : B → B → W') (κ' : B → W')
    (hβX : ∀ g, β X g = 0) (hβW : ∀ g, β (comm X Y) g = 0)
    (hκ : ∀ a b, κ' (a * b) = κ' a + ρ' a (κ' b))
    (hβYX : β Y X = κ' ((comm X Y)⁻¹ * X))
    (hβY'W : β (X⁻¹ * Y * X) (comm X Y) = ρ' (comm X Y)⁻¹ (κ' (comm X Y))) :
    sum7 X Y (cup12 ρ' e u β) =
      e (u X) (ρ' (X * (comm X Y)⁻¹) (κ' (comm X Y))) - e (u (comm X Y)) (κ' X) := by
  have k1 : κ' 1 = 0 := by
    have := hκ 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.mp this
  have kinv : ρ' (comm X Y) (κ' (comm X Y)⁻¹) = - κ' (comm X Y) := by
    have := hκ (comm X Y) (comm X Y)⁻¹
    rw [mul_inv_cancel, k1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have kXW : ρ' (comm X Y) (κ' ((comm X Y)⁻¹ * X)) = κ' X - κ' (comm X Y) := by
    rw [hκ, map_add, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, kinv]
    abel
  have kXW' : ρ' (comm X Y) (ρ' (comm X Y)⁻¹ (κ' (comm X Y))) = κ' (comm X Y) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  unfold sum7 cup12
  rw [hβX, hβX, hβW, hβW, hβY'W, hβYX]
  simp only [map_zero, kXW, kXW', map_sub, map_mul, Module.End.mul_apply]
  abel

/-- **The plane analogue**: `Σ7(cup21 α w)` for a normal-form `α` (`α(X, g) = α(W, g) = 0`, `α(Y, X) = κ(σ·X)`, `α(Y, W) = κ(W)`). -/
theorem sum7_cup21_flag {V W' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W'] [Module ℚ W']
    (ρ' : Representation ℚ B W') (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ) (X Y : B) (α : B → B → V) (w : B → W')
    (κ : B → V) (hαX : ∀ g, α X g = 0) (hαW : ∀ g, α (comm X Y) g = 0)
    (hαYX : α Y X = κ ((comm X Y)⁻¹ * X)) (hαYW : α Y (comm X Y) = κ (comm X Y)) :
    sum7 X Y (cup21 ρ' e α w) =
      e (κ (comm X Y)) (ρ' (Y * comm X Y) (w X)) - e (κ ((comm X Y)⁻¹ * X)) (ρ' (Y * X) (w (comm X Y))) := by
  unfold sum7 cup21
  rw [hαX, hαX, hαW, hαW, hαW, hαYX, hαYW]
  simp only [map_zero, LinearMap.zero_apply]
  abel

/-- `λ` of a difference of two cochains whose difference is a cocycle: `Σ7 c₁ - Σ7 c₂`. -/
theorem FlagCohomDatum.lam_eval_sub (D : FlagCohomDatum B) (X Y : B) (hz : D.z = heisCycle X Y)
    (c₁ c₂ : B → B → B → ℚ) (hc : ∀ g1 g2 g3 g4, dd3T (fun a b c => c₁ a b c - c₂ a b c) g1 g2 g3 g4 = 0) :
    D.lam (cocycleClass (fun g : Fin 3 → B => c₁ (g 0) (g 1) (g 2) - c₂ (g 0) (g 1) (g 2))
      (by rw [dThree_eq_dd3T (fun a b c => c₁ a b c - c₂ a b c)]; funext g; exact hc _ _ _ _)) =
      sum7 X Y c₁ - sum7 X Y c₂ := by
  rw [D.lam_eval X Y hz (fun a b c => c₁ a b c - c₂ a b c) hc]
  unfold sum7
  ring

end TernaryPeriodPolynomials.Argument.FlagH3
