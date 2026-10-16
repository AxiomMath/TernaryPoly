module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.RestrictCusp

@[expose] public section


/-!
# The Hochschild-Serre edge of a restricted mixed class

Formalized by Claude Sonnet 5.5.

For `ι : E₂ → E₁` compatible with the extension data and the module `W₂ = Rep.res ι W₁`, the edge of the restriction
of a radical-kernel class is the image under `mapH1 (levTr)` of the edge of the class.
-/

open CategoryTheory
noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.RadicalInduction
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open scoped Classical

section Edge

variable {N M : ℕ} (hle : Gamma M ≤ Gamma N) {E₁ E₂ : Type} [Group E₁] [Group E₂]
  {ext₁ : GroupExtension RadicalLattice E₁ (Gamma N)} {ext₂ : GroupExtension RadicalLattice E₂ (Gamma M)}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (ι : E₂ →* E₁) (ψ : RadicalLattice →* RadicalLattice)
  (hinl : ∀ r, ι (ext₂.inl r) = ext₁.inl (ψ r)) (hsplit : ∀ l, ι (s₂ l) = s₁ (Subgroup.inclusion hle l))
  (W₁ : Rep ℂ E₁)

/-- The transport `trRel` along the identity of the underlying module is the restriction of the cocycle. -/
theorem trRel_class_res (z : relativeTwoCocycles ext₁.inl W₁) :
    (relativeTwoCocycleClass ext₂.inl (Rep.res ι W₁)
      (trRel ι ψ hinl W₁ (Rep.res ι W₁) LinearMap.id (fun _ _ => rfl) z)).val =
      twoCohomologyRestriction ι W₁ (relativeTwoCocycleClass ext₁.inl W₁ z).val := by
  rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, twoCohomologyRestriction_apply]
  congr 1

include hinl hsplit in
/-- **The edge of the restriction of a radical-kernel class** is the transport of its edge. -/
theorem edge_restrict (x : (twoCohomologyRestriction ext₁.inl W₁).ker)
    (y : (twoCohomologyRestriction ext₂.inl (Rep.res ι W₁)).ker) (hxy : y.val = twoCohomologyRestriction ι W₁ x.val) :
    splitCohomologyEdge s₂ (Rep.res ι W₁) y =
      mapH1 hle (levTr hle s₁ s₂ ι ψ hinl hsplit W₁ (Rep.res ι W₁) LinearMap.id (fun _ _ => rfl))
        (splitCohomologyEdge s₁ W₁ x) := by
  obtain ⟨z, rfl⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective W₁ x
  have hy : y = relativeTwoCocycleClass ext₂.inl (Rep.res ι W₁)
      (trRel ι ψ hinl W₁ (Rep.res ι W₁) LinearMap.id (fun _ _ => rfl) z) :=
    Subtype.ext (hxy.trans (trRel_class_res ι ψ hinl W₁ z).symm)
  rw [hy]
  exact edge_tr_class hle s₁ s₂ ι ψ hinl hsplit W₁ (Rep.res ι W₁) LinearMap.id (fun _ _ => rfl) z

end Edge

end TernaryPeriodPolynomials.Argument.LevelDescent
