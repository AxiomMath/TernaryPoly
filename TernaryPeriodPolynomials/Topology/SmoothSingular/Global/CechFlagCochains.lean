module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechFlags
public import Mathlib.Tactic.Abel

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal.InvariantSetCover
open CategoryTheory

variable {G S ι F : Type} [Group G] [MulAction G S] [AddCommGroup F] [Module ℝ F]
  (U : InvariantSetCover G S ι) (ρ : Representation ℝ G F)

/-- Genuine equivariant coefficient functions on the actual Čech flags. -/
def flagCochains (k : ℕ) : Submodule ℝ (U.Flag k → F) where
  carrier := {w | ∀ g x, w (g • x) = ρ g (w x)}
  zero_mem' := by simp
  add_mem' := by intro w z hw hz g x; simp only [Pi.add_apply,hw g x,hz g x,map_add]
  smul_mem' := by intro c w hw g x; simp only [Pi.smul_apply,hw g x,map_smul]

/-- Pullback along literal flag selection. -/
def flagSelect {p q : ℕ} (f : Fin p → Fin q) :
    U.flagCochains ρ p →ₗ[ℝ] U.flagCochains ρ q where
  toFun w := ⟨fun x => w.val (U.select f x),fun g x =>
    (congrArg w.val (U.select_smul f g x)).trans (w.property g _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual alternating Čech differential on equivariant flag functions. -/
def flagD (k : ℕ) : U.flagCochains ρ k →ₗ[ℝ] U.flagCochains ρ (k+1) :=
  ∑ i : Fin (k+1), (-1 : ℤ)^i.val • U.flagSelect ρ i.succAbove

/-- Evaluation of the genuine alternating restriction sum. -/
theorem flagD_apply (k : ℕ) (w : U.flagCochains ρ k) (x : U.Flag (k+1)) :
    (U.flagD ρ k w).val x = ∑ i : Fin (k+1), (-1 : ℤ)^i.val • w.val (U.select i.succAbove x) := by
  simp only [flagD,LinearMap.sum_apply,LinearMap.smul_apply,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply]
  rfl

/-- The actual invariant prepend operation induces an equivariant Čech homotopy. -/
def flagH (k : ℕ) : U.flagCochains ρ (k+1) →ₗ[ℝ] U.flagCochains ρ k where
  toFun w := ⟨fun x => w.val (U.prepend x),fun g x =>
    (congrArg w.val (U.prepend_smul g x)).trans (w.property g _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The prepended differential splits off the identity face with the correct alternating signs. -/
theorem flagD_prepend (k : ℕ) (w : U.flagCochains ρ (k+1)) (x : U.Flag (k+1)) :
    (U.flagD ρ (k+1) w).val (U.prepend x) = w.val x -
      ∑ i : Fin (k+1), (-1 : ℤ)^i.val • w.val (U.prepend (U.select i.succAbove x)) := by
  rw [U.flagD_apply,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,U.select_zero_prepend,
    Fin.val_succ,pow_succ,mul_neg_one,neg_smul,Finset.sum_neg_distrib,
    U.select_succ_prepend,sub_eq_add_neg]

/-- The genuine equivariant flag homotopy satisfies δh+hδ=id in every positive tuple length. -/
theorem flag_contracting (k : ℕ) (w : U.flagCochains ρ (k+1)) :
    U.flagD ρ k (U.flagH ρ k w) + U.flagH ρ (k+1) (U.flagD ρ (k+1) w) = w := by
  apply Subtype.ext
  funext x
  change (U.flagD ρ k (U.flagH ρ k w)).val x +
    (U.flagD ρ (k+1) w).val (U.prepend x) = w.val x
  rw [U.flagD_apply,U.flagD_prepend]
  change (∑ i : Fin (k+1), (-1 : ℤ)^i.val • w.val (U.prepend (U.select i.succAbove x))) +
    (w.val x - ∑ i : Fin (k+1), (-1 : ℤ)^i.val • w.val (U.prepend (U.select i.succAbove x))) = w.val x
  abel

/-- The actual augmented degree-zero flag differential has a genuine left inverse. -/
theorem flagH_D_zero (w : U.flagCochains ρ 0) : U.flagH ρ 0 (U.flagD ρ 0 w) = w := by
  apply Subtype.ext
  funext x
  change (U.flagD ρ 0 w).val (U.prepend x) = w.val x
  rw [U.flagD_apply,Fin.sum_univ_one]
  simp only [Fin.val_zero,pow_zero,one_smul,U.select_zero_prepend]

/-- Every closed actual equivariant flag cochain has the displayed actual Čech primitive. -/
theorem flag_primitive (k : ℕ) (w : U.flagCochains ρ (k+1)) (hw : U.flagD ρ (k+1) w = 0) :
    U.flagD ρ k (U.flagH ρ k w) = w := by
  have h := U.flag_contracting ρ k w
  rw [hw,map_zero,add_zero] at h
  exact h

/-- The actual augmented equivariant flag differential is injective. -/
theorem flagD_zero_injective : Function.Injective (U.flagD ρ 0) :=
  Function.LeftInverse.injective (U.flagH_D_zero ρ)

end TernaryPoly.SmoothSingularGlobal.InvariantSetCover
