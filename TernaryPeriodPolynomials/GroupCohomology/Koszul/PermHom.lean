module

public import Mathlib

@[expose] public section


/-!
# Equivariant maps between permutation representations

Formalized by Claude Sonnet 5.5.

For a group `G` and `G`-sets `X`, `Y`, an equivariant coefficient vector `c : X → (Y →₀ ℚ)` (that is,
`c (g • x) = (g • ·)_* (c x)`) defines a morphism `permHom c hc : ℚ[X] ⟶ ℚ[Y]` of permutation representations,
`[x] ↦ c x` (`permHom_single`).  This covers morphisms induced by equivariant maps and their linear combinations.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomologyDescent

open CategoryTheory Representation Rep
open scoped MonoidAlgebra

variable {G : Type} [Group G] {X Y : Type} [MulAction G X] [MulAction G Y]

theorem ofMulAction_symm (g : G) (ψ : Y →₀ ℚ) :
    Representation.ofMulAction ℚ G Y g ((MonoidAlgebra.coeffLinearEquiv ℚ).symm ψ) =
      (MonoidAlgebra.coeffLinearEquiv ℚ).symm (Finsupp.mapDomain (fun y => g • y) ψ) := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, Finsupp.mapDomain_add, map_add]
  | single y r =>
    have : (MonoidAlgebra.coeffLinearEquiv ℚ).symm (Finsupp.single y r) = MonoidAlgebra.single y r := by
      rfl
    rw [this, Representation.ofMulAction_single, Finsupp.mapDomain_single]
    rfl

/-- The linear map `ℚ[X] → ℚ[Y]` sending `[x]` to the coefficient vector `c x`. -/
def permLin (c : X → Y →₀ ℚ) : ℚ[X] →ₗ[ℚ] ℚ[Y] :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ Finsupp.lift (Y →₀ ℚ) ℚ X c ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem permLin_single (c : X → Y →₀ ℚ) (x : X) (r : ℚ) :
    permLin c (MonoidAlgebra.single x r) = (MonoidAlgebra.coeffLinearEquiv ℚ).symm (r • c x) := by
  have : (MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single x r) = Finsupp.single x r := rfl
  simp [permLin, this]

/-- The equivariant map between permutation representations given by an equivariant coefficient vector. -/
def permHom (c : X → Y →₀ ℚ) (hc : ∀ (g : G) (x : X), c (g • x) = Finsupp.mapDomain (fun y => g • y) (c x)) :
    Rep.ofMulAction ℚ G X ⟶ Rep.ofMulAction ℚ G Y :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.ofMulAction ℚ G X).ρ) (σ := (Rep.ofMulAction ℚ G Y).ρ) (permLin c)
    (fun g v => by
      have key : permLin c ∘ₗ (Representation.ofMulAction ℚ G X g) =
          (Representation.ofMulAction ℚ G Y g) ∘ₗ permLin c := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, Representation.ofMulAction_single,
          permLin_single, one_smul, ofMulAction_symm, hc]
      exact LinearMap.congr_fun key v))

theorem permHom_single (c : X → Y →₀ ℚ)
    (hc : ∀ (g : G) (x : X), c (g • x) = Finsupp.mapDomain (fun y => g • y) (c x)) (x : X) (r : ℚ) :
    (permHom c hc).hom (MonoidAlgebra.single x r) = (MonoidAlgebra.coeffLinearEquiv ℚ).symm (r • c x) := by
  simp [permHom, permLin_single]

end TernaryPeriodPolynomials.Argument.GroupHomologyDescent
