module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Mackey

@[expose] public section


/-!
# Coefficient morphisms of `P`-level correspondences, for a general fibre `F`

Formalized by Claude Sonnet 5.5.

For a subgroup `P ≤ Γ`, `ι : Γ → Ĝ`, a `Ĝ`-module `M`, a `P`-module `F` and an injective `P`-map `J : F → Res_P Res_ι M`, a linear
endomorphism `c` of `F` with `J ∘ c = ρ_M(ξ) ∘ J` is, whenever `ξ` conjugates `ι ∘ j` into `ι ∘ f`, a morphism of
representations `Res_j F → Res_f F` (`coeffG`; `coeffG0` for `j = id`).  Everything is proved for a variable `F`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

variable {Γ Ĝ : Type} [Group Γ] [Group Ĝ] (ι : Γ →* Ĝ) (M : Rep.{0} ℚ Ĝ) {P : Subgroup Γ} (F : Rep.{0} ℚ P)
  (J : F ⟶ Rep.res P.subtype (Rep.res ι M)) (hJ : Function.Injective J.hom)

/-- The coefficient morphism `Res_j F ⟶ Res_f F` of the correspondence `(j, f, ξ, c)`. -/
def coeffG {H : Type} [Group H] (j f : H →* P) (ξ : Ĝ) (c : F →ₗ[ℚ] F)
    (hc : ∀ a, J.hom (c a) = M.ρ ξ (J.hom a))
    (hf : ∀ h, ι ((f h : P) : Γ) = ξ * ι ((j h : P) : Γ) * ξ⁻¹) :
    Rep.res j F ⟶ Rep.res f F :=
  Rep.ofHom ⟨c, fun h => by
    refine LinearMap.ext fun a => ?_
    apply hJ
    have e1 : ∀ (q : P) (b : F),
        J.hom (F.ρ q b) = M.ρ (ι (q : Γ)) (J.hom b) := fun q b => Rep.hom_comm_apply J q b
    change J.hom (c (F.ρ (j h) a)) = J.hom (F.ρ (f h) (c a))
    rw [hc, e1, e1, hc, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hf h,
      inv_mul_cancel_right]⟩

/-- The coefficient morphism `F ⟶ Res_f F` of the correspondence `(f, ξ, c)`. -/
def coeffG0 (f : P →* P) (ξ : Ĝ) (c : F →ₗ[ℚ] F)
    (hc : ∀ a, J.hom (c a) = M.ρ ξ (J.hom a))
    (hf : ∀ h : P, ι ((f h : P) : Γ) = ξ * ι (h : Γ) * ξ⁻¹) :
    F ⟶ Rep.res f F :=
  Rep.ofHom ⟨c, fun h => by
    refine LinearMap.ext fun a => ?_
    apply hJ
    have e1 : ∀ (q : P) (b : F),
        J.hom (F.ρ q b) = M.ρ (ι (q : Γ)) (J.hom b) := fun q b => Rep.hom_comm_apply J q b
    change J.hom (c (F.ρ h a)) = J.hom (F.ρ (f h) (c a))
    rw [hc, e1, e1, hc, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hf h,
      inv_mul_cancel_right]⟩


theorem card_RC_top (N : Subgroup P) [N.FiniteIndex] (hN : ∀ h : P, h ∈ N) :
    Fintype.card (RC N) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ 1, fun y => ?_⟩
  induction y using Quotient.inductionOn' with
  | h a =>
    symm
    show (Quotient.mk (QuotientGroup.rightRel _) 1 : RC N) = Quotient.mk _ a
    rw [rc_eq_iff]
    exact hN _

/-- **The transfer to the whole group is the identity**: for `N = ⊤`, `tr_N ≫ H(f ∘ incl, Res c) = H(f, c)`. -/
theorem trR_top_map (N : Subgroup P) [N.FiniteIndex] (hN : ∀ h : P, h ∈ N) (f : P →* P) (ξ : Ĝ)
    (c : F →ₗ[ℚ] F) (hc : ∀ a, J.hom (c a) = M.ρ ξ (J.hom a))
    (hf : ∀ h : P, ι ((f h : P) : Γ) = ξ * ι (h : Γ) * ξ⁻¹) (k : ℕ) :
    trR N F k ≫ groupHomology.map (f.comp N.subtype)
        (coeffG ι M F J hJ N.subtype (f.comp N.subtype) ξ c hc (fun h => hf (N.subtype h))) k =
      groupHomology.map f (coeffG0 ι M F J hJ f ξ c hc hf) k := by
  have e1 : groupHomology.map (f.comp N.subtype)
        (coeffG ι M F J hJ N.subtype (f.comp N.subtype) ξ c hc (fun h => hf (N.subtype h))) k =
      groupHomology.map N.subtype (𝟙 (Rep.res N.subtype F)) k ≫
        groupHomology.map f (coeffG0 ι M F J hJ f ξ c hc hf) k := by
    have h := groupHomology.map_comp N.subtype f (𝟙 (Rep.res N.subtype F))
      (coeffG0 ι M F J hJ f ξ c hc hf) k
    refine Eq.trans ?_ h
    refine groupHomology.map_congr rfl ?_ k
    exact LinearMap.ext fun a => rfl
  rw [e1, ← Category.assoc, trR_cor, card_RC_top N hN]
  simp

end TernaryPeriodPolynomials.Argument.HeckeHomology
