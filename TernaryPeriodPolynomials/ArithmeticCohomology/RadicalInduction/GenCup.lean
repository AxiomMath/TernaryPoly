module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.GLQuot
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.CupInd

@[expose] public section


/-!
# The cup form for a pairing which is a sum of pulled-back pairings

Formalized by Claude Sonnet 5.5.

Generalisation of `CuspidalInduction.cupForm_ind` to an arbitrary comparison `φ : E₁ → V` of a `Γ(N)`-module with a `Γ(M)`-module (`φ(ρ₁(δ) a) = ρ_V(δ) φ(a)` for `δ ∈ Γ(M)`) and a pairing
`e₁(a, b) = ∑_x e(φ(ρ₁(u_x)⁻¹ a), φ'(ρ₁'(u_x)⁻¹ b))`: `cupForm_phi`: the sum of the integrands of the twisted cusp functions `Φ, Φ'` for `e₁` is the sum of the integrands of `φ ∘ Φ`,
`φ' ∘ Φ'` for `e` over the representatives of the triangles of `Γ(M)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open scoped Classical

variable {N M : ℕ} {E₁ E₁' V V' : Type} [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₁'] [Module ℂ E₁']
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {Q : Type} [Fintype Q] [MulAction (gammaNGL N) Q]

theorem cupForm_phi (hN : 3 ≤ N) (hM : 3 ≤ M) (hle : gammaNGL M ≤ gammaNGL N)
    (ρ₁ : Representation ℂ (gammaNGL N) E₁) (ρ₁' : Representation ℂ (gammaNGL N) E₁')
    (ρV : Representation ℂ (gammaNGL M) V) (ρV' : Representation ℂ (gammaNGL M) V')
    (e₁ : E₁ →ₗ[ℂ] E₁' →ₗ[ℂ] ℂ) (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (φ : E₁ →ₗ[ℂ] V) (φ' : E₁' →ₗ[ℂ] V')
    (hφ : ∀ (g : gammaNGL M) a, φ (ρ₁ (Subgroup.inclusion hle g) a) = ρV g (φ a))
    (hφ' : ∀ (g : gammaNGL M) a, φ' (ρ₁' (Subgroup.inclusion hle g) a) = ρV' g (φ' a))
    (hinv : ∀ (γ : gammaNGL M) v w, e (ρV γ v) (ρV' γ w) = e v w)
    (q0 : Q) (u : Q → gammaNGL N) (hu : ∀ x, u x • q0 = x)
    (hstab : ∀ g : gammaNGL N, g • q0 = q0 ↔ (g : IntegralGL) ∈ gammaNGL M)
    (hE : ∀ a b, e₁ a b = ∑ x : Q, e (φ (ρ₁ (u x)⁻¹ a)) (φ' (ρ₁' (u x)⁻¹ b)))
    (Φ : RationalLine2 → E₁) (Φ' : RationalLine2 → E₁') (f : gammaNGL N → E₁) (f' : gammaNGL N → E₁')
    (hΦ : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ ((γ : IntegralGL) • x) = ρ₁ γ (Φ x) + f γ)
    (hΦ' : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ' ((γ : IntegralGL) • x) = ρ₁' γ (Φ' x) + f' γ) :
    ∑ y ∈ (gammaNFareyData hN).RT.R, integ e₁ Φ Φ' y =
      ∑ r ∈ (gammaNFareyData hM).RT.R, integ e (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) r := by
  have hSL : ∀ g ∈ gammaNGL N, IsSL g := fun g hg => gammaN_isSL hN hg
  have step1 : ∀ y : Tri, integ e₁ Φ Φ' y =
      ∑ x : Q, integ e (fun c => φ (ρ₁ (u x)⁻¹ (Φ c))) (fun c => φ' (ρ₁' (u x)⁻¹ (Φ' c))) y := by
    intro y
    unfold integ
    simp only [hE]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  have step2 : ∀ (y : Tri) (x : Q), integ e (fun c => φ (ρ₁ (u x)⁻¹ (Φ c))) (fun c => φ' (ρ₁' (u x)⁻¹ (Φ' c))) y =
      integ e (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • y) := by
    intro y x
    have e1 : (fun c => φ (ρ₁ (u x)⁻¹ (Φ c))) =
        fun c => φ (Φ ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c)) + (-(φ (f (u x)⁻¹))) := by
      funext c
      have := hΦ (u x)⁻¹ c
      rw [this, map_add]
      abel
    have e2 : (fun c => φ' (ρ₁' (u x)⁻¹ (Φ' c))) =
        fun c => φ' (Φ' ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c)) + (-(φ' (f' (u x)⁻¹))) := by
      funext c
      have := hΦ' (u x)⁻¹ c
      rw [this, map_add]
      abel
    rw [e1, e2, integ_add_const]
    exact integ_comp e (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) (hSL _ ((u x)⁻¹).2) y
  have step3 : ∀ (δ : gammaNGL M) (y : Tri),
      integ e (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) ((δ : IntegralGL) • y) =
        integ e (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) y := by
    intro δ y
    refine integ_invariant (Γ := gammaNGL M) (fun g hg => hSL g (hle hg)) (ρ := ρV) (ρ' := ρV') e hinv
      (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) (fun δ => φ (f (Subgroup.inclusion hle δ)))
      (fun δ => φ' (f' (Subgroup.inclusion hle δ))) (fun γ x => ?_) (fun γ x => ?_) δ y
    · have := hΦ (Subgroup.inclusion hle γ) x
      change φ (Φ ((γ : IntegralGL) • x)) = _
      rw [show ((γ : IntegralGL) • x) = (((Subgroup.inclusion hle γ : gammaNGL N) : IntegralGL) • x) from rfl, this,
        map_add, hφ]
    · have := hΦ' (Subgroup.inclusion hle γ) x
      change φ' (Φ' ((γ : IntegralGL) • x)) = _
      rw [show ((γ : IntegralGL) • x) = (((Subgroup.inclusion hle γ : gammaNGL N) : IntegralGL) • x) from rfl, this,
        map_add, hφ']
  calc ∑ y ∈ (gammaNFareyData hN).RT.R, integ e₁ Φ Φ' y
      = ∑ y ∈ (gammaNFareyData hN).RT.R, ∑ x : Q,
          integ e (fun c => φ (Φ c)) (fun c => φ' (Φ' c)) ((u x)⁻¹ • y) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [step1]
        exact Finset.sum_congr rfl (fun x _ => step2 y x)
    _ = _ := sum_reindex hN hM hle q0 u hu hstab _ step3

end TernaryPeriodPolynomials.Argument.RadicalInduction
