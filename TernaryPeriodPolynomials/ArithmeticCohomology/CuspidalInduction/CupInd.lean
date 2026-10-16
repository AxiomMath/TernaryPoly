module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Induction

@[expose] public section


/-!
# `cupForm` of an induced module

Formalized by Claude Sonnet 5.5.

`cupForm_ind`: for twisted cusp functions `Φ`, `Φ'` of `Γ(N)` with values in `Fun(Q, E)`, `Fun(Q, E')` (`Q` a transitive `Γ(N)`-set with stabilizer `Γ(M)` of the base point `q₀`),
the cup form of the summed pairing equals the cup form at level `M` of the evaluations at `q₀`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

variable {N M : ℕ} {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  {Q : Type} [Fintype Q] [MulAction (gammaNGL N) Q]

omit [Fintype Q] in
/-- Evaluating a twisted `Fun(Q, E)`-valued cusp function at the base point of `Q`. -/
theorem eval_base (ρ : Representation ℂ (gammaNGL N) E) (q0 : Q) (u : Q → gammaNGL N) (hu : ∀ x, u x • q0 = x)
    (Φ : RationalLine2 → (Q → E)) (f : gammaNGL N → (Q → E))
    (hΦ : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ ((γ : IntegralGL) • x) = indRepQ ρ γ (Φ x) + f γ)
    (x : Q) (c : RationalLine2) :
    Φ c x = ρ (u x) (Φ (((u x)⁻¹ : gammaNGL N) • c) q0 - f (u x)⁻¹ q0) := by
  have h := congrFun (hΦ (u x)⁻¹ c) q0
  simp only [Pi.add_apply, indRepQ_apply, inv_inv, hu] at h
  change Φ (((u x)⁻¹ : gammaNGL N) • c) q0 = _ at h
  rw [h, add_sub_cancel_right, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem cupForm_ind (hN : 3 ≤ N) (hM : 3 ≤ M) (hle : gammaNGL M ≤ gammaNGL N)
    (ρ : Representation ℂ (gammaNGL N) E) (ρ' : Representation ℂ (gammaNGL N) E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ)
    (hinv : ∀ (γ : gammaNGL N) v w, e (ρ γ v) (ρ' γ w) = e v w)
    (q0 : Q) (u : Q → gammaNGL N) (hu : ∀ x, u x • q0 = x)
    (hstab : ∀ g : gammaNGL N, g • q0 = q0 ↔ (g : IntegralGL) ∈ gammaNGL M)
    (Φ : RationalLine2 → (Q → E)) (Φ' : RationalLine2 → (Q → E')) (f : gammaNGL N → (Q → E)) (f' : gammaNGL N → (Q → E'))
    (hΦ : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ ((γ : IntegralGL) • x) = indRepQ ρ γ (Φ x) + f γ)
    (hΦ' : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ' ((γ : IntegralGL) • x) = indRepQ ρ' γ (Φ' x) + f' γ) :
    ∑ y ∈ (gammaNFareyData hN).RT.R, integ (eindQ e) Φ Φ' y =
      ∑ r ∈ (gammaNFareyData hM).RT.R, integ e (fun c => Φ c q0) (fun c => Φ' c q0) r := by
  have hSL : ∀ g ∈ gammaNGL N, IsSL g := fun g hg => gammaN_isSL hN hg
  -- Step 1: split the summed pairing
  have step1 : ∀ y : Tri, integ (eindQ e) Φ Φ' y = ∑ x : Q, integ e (fun c => Φ c x) (fun c => Φ' c x) y := by
    intro y
    unfold integ
    simp only [eindQ_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  -- Step 2: each fibre is the level-`M` integrand at the translated triangle
  have step2 : ∀ (y : Tri) (x : Q), integ e (fun c => Φ c x) (fun c => Φ' c x) y =
      integ e (fun c => Φ c q0) (fun c => Φ' c q0) ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • y) := by
    intro y x
    have e1 : (fun c => Φ c x) = fun c => ρ (u x) ((Φ ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c) q0) + (-(f (u x)⁻¹ q0))) := by
      funext c
      rw [eval_base ρ q0 u hu Φ f hΦ x c, sub_eq_add_neg]
      rfl
    have e2 : (fun c => Φ' c x) = fun c => ρ' (u x) ((Φ' ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c) q0) + (-(f' (u x)⁻¹ q0))) := by
      funext c
      rw [eval_base ρ' q0 u hu Φ' f' hΦ' x c, sub_eq_add_neg]
      rfl
    rw [e1, e2]
    have e3 : integ e (fun c => ρ (u x) (Φ ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c) q0 + -(f (u x)⁻¹ q0)))
        (fun c => ρ' (u x) (Φ' ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c) q0 + -(f' (u x)⁻¹ q0))) y =
        integ e (fun c => Φ ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c) q0 + -(f (u x)⁻¹ q0))
          (fun c => Φ' ((((u x)⁻¹ : gammaNGL N) : IntegralGL) • c) q0 + -(f' (u x)⁻¹ q0)) y := by
      unfold integ
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [hinv, hinv]
    rw [e3, integ_add_const]
    exact integ_comp e (fun c => Φ c q0) (fun c => Φ' c q0) (hSL _ ((u x)⁻¹).2) y
  -- Step 3: invariance of the level-`M` integrand under `Γ(M)`
  have step3 : ∀ (δ : gammaNGL M) (y : Tri),
      integ e (fun c => Φ c q0) (fun c => Φ' c q0) ((δ : IntegralGL) • y) =
        integ e (fun c => Φ c q0) (fun c => Φ' c q0) y := by
    intro δ y
    let ι : gammaNGL M →* gammaNGL N := Subgroup.inclusion hle
    have hδ : ∀ δ : gammaNGL M, ((ι δ)⁻¹ : gammaNGL N) • q0 = q0 := by
      intro δ
      have : (ι δ) • q0 = q0 := (hstab _).mpr δ.2
      rw [inv_smul_eq_iff]
      exact this.symm
    refine integ_invariant (Γ := gammaNGL M) (fun g hg => hSL g (hle hg)) (ρ := ρ.comp ι) (ρ' := ρ'.comp ι) e
      (fun γ v w => hinv (ι γ) v w) (fun c => Φ c q0) (fun c => Φ' c q0) (fun δ => f (ι δ) q0) (fun δ => f' (ι δ) q0)
      (fun γ x => ?_) (fun γ x => ?_) δ y
    · have := congrFun (hΦ (ι γ) x) q0
      simp only [Pi.add_apply, indRepQ_apply, hδ] at this
      exact this
    · have := congrFun (hΦ' (ι γ) x) q0
      simp only [Pi.add_apply, indRepQ_apply, hδ] at this
      exact this
  -- Step 4: reindex
  calc ∑ y ∈ (gammaNFareyData hN).RT.R, integ (eindQ e) Φ Φ' y
      = ∑ y ∈ (gammaNFareyData hN).RT.R, ∑ x : Q,
          integ e (fun c => Φ c q0) (fun c => Φ' c q0) ((u x)⁻¹ • y) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [step1]
        exact Finset.sum_congr rfl (fun x _ => step2 y x)
    _ = _ := sum_reindex hN hM hle q0 u hu hstab _ step3

end TernaryPeriodPolynomials.Argument.CuspidalInduction
