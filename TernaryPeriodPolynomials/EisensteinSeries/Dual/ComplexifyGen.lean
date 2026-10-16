module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Bridge
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Transport

@[expose] public section


open CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.SeedC3S4c (realDescent realDescent_apply)

/-!
# Complexification of the real classes of the dual series

Formalized by Claude Sonnet 5.5.

The de Rham zig-zag produces classes with coefficients in the REAL model `Coef n` of `E_n`, while the
mixed cuspidal groups and the literal dual `E*` are complex.  `cxGen ρ ρC` is the generalization of the `EisensteinClass.complexify` to any real
representation `ρ` on `Coef n` and complex representation `ρC` with the same action (the identity on 2-cocycles); `cxGen_map` shows it commutes with
pullback along a group homomorphism (`resMorK`: the identity morphism over any field).  Used for the dual coefficient system `ρ ∘ ȷ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.EisensteinClass

section Generic

variable {G : Type} [Group G] {n : ℕ} (ρ : Representation ℝ G (Coef n))
  (ρC : Representation ℂ G (HomogeneousPoly n))
  (hρ : ∀ g (v : Coef n), ((ρ g v : Coef n) : HomogeneousPoly n) = ρC g (v : HomogeneousPoly n))

/-- Real 2-cocycles with values in the real model `Coef n` are complex 2-cocycles for `ρC`. -/
def cxCocyclesGen : cocycles₂ (Rep.of ρ) →ₗ[ℝ] cocycles₂ (Rep.of ρC) where
  toFun c := ⟨fun p => (c.1 p : Coef n), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    let c' : G × G → HomogeneousPoly n := fun p => c.1 p
    change c' (g * h, j) + c' (g, h) = ρC g (c' (h, j)) + c' (g, h * j)
    rw [← hρ g (c.1 (h, j))]
    exact e)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Complexification** `H²(G, ρ)_ℝ → H²(G, ρC)_ℂ` for a real representation on `Coef n` and a complex one with the same action: the
identity on 2-cocycles. -/
def cxGen : H2 (Rep.of ρ) →ₗ[ℝ] H2 (Rep.of ρC) :=
  realDescent (H2π (Rep.of ρ)).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (Rep.of ρC)).hom.restrictScalars ℝ).comp (cxCocyclesGen ρ ρC hρ))
    (fun a b hab => by
      have h : H2π (Rep.of ρ) a = H2π (Rep.of ρ) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (Rep.of ρC) (cxCocyclesGen ρ ρC hρ a) = H2π (Rep.of ρC) (cxCocyclesGen ρ ρC hρ b)
      rw [H2π_eq_iff]
      let y' : G → HomogeneousPoly n := fun g => y g
      refine ⟨y', ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      refine Eq.trans ?_ hp
      rw [← hρ p.1 (y p.2)]
      rfl)

theorem cxGen_H2π (c : cocycles₂ (Rep.of ρ)) :
    cxGen ρ ρC hρ (H2π (Rep.of ρ) c) = H2π (Rep.of ρC) (cxCocyclesGen ρ ρC hρ c) :=
  realDescent_apply _ _ _ _ c

/-- The identity of the coefficient module as a morphism `Res_α ρ' ⟶ ρ` over an arbitrary field. -/
def resMorK {k : Type} [Field k] {G G' : Type} [Group G] [Group G'] {V : Type} [AddCommGroup V] [Module k V]
    (α : G →* G') (ρ : Representation k G V) (ρ' : Representation k G' V) (hρ : ∀ g, ρ g = ρ' (α g)) :
    Rep.res α (Rep.of ρ') ⟶ Rep.of ρ :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    ext v
    simp [hρ g]⟩

end Generic

section Natural

variable {G G' : Type} [Group G] [Group G'] {n : ℕ}
  (ρ : Representation ℝ G (Coef n)) (ρC : Representation ℂ G (HomogeneousPoly n))
  (hρ : ∀ g (v : Coef n), ((ρ g v : Coef n) : HomogeneousPoly n) = ρC g (v : HomogeneousPoly n))
  (ρ' : Representation ℝ G' (Coef n)) (ρC' : Representation ℂ G' (HomogeneousPoly n))
  (hρ' : ∀ g (v : Coef n), ((ρ' g v : Coef n) : HomogeneousPoly n) = ρC' g (v : HomogeneousPoly n))
  (α : G →* G') (hR : ∀ g, ρ g = ρ' (α g)) (hC : ∀ g, ρC g = ρC' (α g))

/-- **Complexification commutes with pullback along a group homomorphism.** -/
theorem cxGen_map (x : H2 (Rep.of ρ')) :
    cxGen ρ ρC hρ ((groupCohomology.map α (resMor α ρ ρ' hR) 2).hom x) =
      (groupCohomology.map α (resMorK α ρC ρC' hC) 2).hom (cxGen ρ' ρC' hρ' x) := by
  induction x using H2_induction_on with
  | _ c =>
    rw [H2π_comp_map_apply, cxGen_H2π, cxGen_H2π, H2π_comp_map_apply]
    congr 1

end Natural


end TernaryPeriodPolynomials.Argument.EisensteinDual
