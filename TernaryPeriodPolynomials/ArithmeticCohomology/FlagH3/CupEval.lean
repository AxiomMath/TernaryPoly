module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Data
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section



/-!
# `λ_F` on cup products: the seven-term formula

Formalized by Claude Sonnet 5.5.

For the flag datum with cycle `heisCycle X Y` (`Y' = X⁻¹ Y X`, `W = [X,Y]`), the value of `λ` on a class represented by a `3`-cochain `c` is
`c(X,Y',W) - c(Y,X,W) + c(Y,W,X) - c(X,W,Y') + c(W,X,Y') - c(W,Y,X) - c(W,Y',W)` (`heisCycle_eval`, `lam_eval`).  `lam_cup12` specializes `c` to the `cup12` with an invariant pairing `e` into `ℚ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {B : Type} [Group B]

/-- **The seven-term formula**: the value of a `3`-cochain `Θ` on the Heisenberg bar cycle of `X`, `Y`
(`Y' = X⁻¹ Y X`, `W = [X,Y]`). -/
theorem heisCycle_eval (X Y : B) (Θ : B → B → B → ℚ) :
    chainEval (heisCycle X Y) (fun g : Fin 3 → B => Θ (g 0) (g 1) (g 2)) =
      Θ X (X⁻¹ * Y * X) (comm X Y) - Θ Y X (comm X Y) + Θ Y (comm X Y) X - Θ X (comm X Y) (X⁻¹ * Y * X) +
        Θ (comm X Y) X (X⁻¹ * Y * X) - Θ (comm X Y) Y X - Θ (comm X Y) (X⁻¹ * Y * X) (comm X Y) := by
  simp only [heisCycle, chainEval_add, chainEval_sub, chainEval_single, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  ring

theorem dThree_eq_dd3T (c : B → B → B → ℚ) :
    dThree (fun g : Fin 3 → B => c (g 0) (g 1) (g 2)) = fun g : Fin 4 → B => dd3T c (g 0) (g 1) (g 2) (g 3) := by
  funext g
  rw [dThree_apply]
  simp [dd3T]

namespace FlagCohomDatum

/-- **`λ` of a class represented by a `3`-cocycle `c` in the notation of `CupProduct` (`dd3T c = 0`)**, as the seven-term sum over the cycle `heisCycle X Y`. -/
theorem lam_eval (D : FlagCohomDatum B) (X Y : B) (hz : D.z = heisCycle X Y) (c : B → B → B → ℚ)
    (hc : ∀ g1 g2 g3 g4, dd3T c g1 g2 g3 g4 = 0) :
    D.lam (cocycleClass (fun g : Fin 3 → B => c (g 0) (g 1) (g 2))
      (by rw [dThree_eq_dd3T]; funext g; exact hc _ _ _ _)) =
      c X (X⁻¹ * Y * X) (comm X Y) - c Y X (comm X Y) + c Y (comm X Y) X - c X (comm X Y) (X⁻¹ * Y * X) +
        c (comm X Y) X (X⁻¹ * Y * X) - c (comm X Y) Y X - c (comm X Y) (X⁻¹ * Y * X) (comm X Y) := by
  rw [D.lam_cocycle, hz]
  exact heisCycle_eval X Y c

/-- **`λ` on a cup product of a `1`-cocycle and a `2`-cocycle with an invariant pairing into `ℚ`** (S2's `cup12`). -/
theorem lam_cup12 (D : FlagCohomDatum B) (X Y : B) (hz : D.z = heisCycle X Y) {V W : Type}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W] (ρ : Representation ℚ B V)
    (ρ' : Representation ℚ B W) (e : V →ₗ[ℚ] W →ₗ[ℚ] ℚ)
    (he : ∀ (g : B) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w) (u : B → V) (β : B → B → W)
    (hu : dd1 ρ u = 0) (hβ : dd2 ρ' β = 0) :
    D.lam (cocycleClass (fun g : Fin 3 → B => cup12 ρ' e u β (g 0) (g 1) (g 2))
      (by rw [dThree_eq_dd3T, cup12_cocycle he u β hu hβ]; rfl)) =
      cup12 ρ' e u β X (X⁻¹ * Y * X) (comm X Y) - cup12 ρ' e u β Y X (comm X Y) +
        cup12 ρ' e u β Y (comm X Y) X - cup12 ρ' e u β X (comm X Y) (X⁻¹ * Y * X) +
        cup12 ρ' e u β (comm X Y) X (X⁻¹ * Y * X) - cup12 ρ' e u β (comm X Y) Y X -
        cup12 ρ' e u β (comm X Y) (X⁻¹ * Y * X) (comm X Y) :=
  D.lam_eval X Y hz _ (fun g1 g2 g3 g4 => by rw [cup12_cocycle he u β hu hβ]; rfl)

end FlagCohomDatum

end TernaryPeriodPolynomials.Argument.FlagH3
