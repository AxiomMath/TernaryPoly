module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.FrameChange

@[expose] public section


/-!
# The semidirect product model of a split extension

Paper: Lemma C.3 (`ar:lem:seed`).

A split extension `E` of `L` by `N` is isomorphic to the semidirect product `N ⋊ L`
(`Splitting.semidirectProductMulEquiv`), which is the model used by the face library
(`FacePairingFull.Face`).  This file shows that the mixed cuspidal group is unchanged by passing to the
semidirect product model:

* `h1MapId_bijective`: a bijective morphism of `L`-modules induces a bijection of `H¹(L, ·)`;
* `semidirectH1Equiv`: `H¹(L, H¹(N, E))` computed on `E` and on `N ⋊ L` are isomorphic;
* `semidirectH1Equiv_mem_cuspidalFamily`: the isomorphism preserves and reflects `cuspidalFamily`;
* `semidirectH2Map`: the corresponding bijection of `H²`, compatible with the radical restriction
  (`semidirectH2Map_restriction_eq_zero_iff`) and with the Hochschild--Serre edge (`semidirect_edge`).

Formalized by Claude Sonnet 5.5.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section MapBijective

variable {L : Type} [Group L] {V₁ V₂ : Rep ℂ L}

/-- A bijective morphism of `L`-modules induces a bijection on `H¹`. -/
theorem h1MapId_bijective (φ : Rep.res (MonoidHom.id L) V₁ ⟶ V₂) (hφ : Function.Bijective φ.hom) :
    Function.Bijective (groupCohomology.map (MonoidHom.id L) φ 1).hom := by
  have hmap : ∀ (c : groupCohomology.cocycles₁ V₁) (γ : L),
      ((groupCohomology.mapCocycles₁ (MonoidHom.id L) φ c).1 γ) = φ.hom (c.1 γ) := fun c γ => rfl
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using groupCohomology.H1_induction_on with
    | h c =>
      rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_eq_zero_iff] at hx
      obtain ⟨u, hu⟩ := hx
      rw [groupCohomology.H1π_eq_zero_iff]
      obtain ⟨u₁, rfl⟩ := hφ.2 u
      refine ⟨u₁, ?_⟩
      funext γ
      apply hφ.1
      have h1 := congrFun hu γ
      rw [groupCohomology.d₀₁_hom_apply] at h1 ⊢
      rw [map_sub, show φ.hom (V₁.ρ γ u₁) = V₂.ρ γ (φ.hom u₁) from Rep.hom_comm_apply φ γ u₁]
      exact h1.trans (hmap c γ)
  · intro x
    induction x using groupCohomology.H1_induction_on with
    | h c₂ =>
      let e : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective φ.hom.toLinearMap hφ
      have he : ∀ g v, e (V₁.ρ g v) = V₂.ρ g (e v) := fun g v => Rep.hom_comm_apply φ g v
      let c₁ : groupCohomology.cocycles₁ V₁ :=
        ⟨fun γ => e.symm (c₂.1 γ), by
          apply (groupCohomology.mem_cocycles₁_iff _).mpr
          intro a b
          have hrel := (groupCohomology.mem_cocycles₁_iff c₂.1).mp c₂.2 a b
          apply e.injective
          rw [e.apply_symm_apply, map_add, he, e.apply_symm_apply, e.apply_symm_apply]
          exact hrel⟩
      refine ⟨groupCohomology.H1π V₁ c₁, ?_⟩
      rw [groupCohomology.H1π_comp_map_apply]
      congr 1
      apply groupCohomology.cocycles₁_ext
      intro γ
      exact e.apply_symm_apply _

end MapBijective

section SemidirectModel

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L}
  (s : ext.Splitting) (ρ : Rep ℂ E)

/-- The representation of `N ⋊ L` obtained from `ρ` through the canonical isomorphism
`N ⋊ L ≃* E` of a split extension. -/
abbrev semidirectRep : Rep ℂ (N ⋊[s.conjAct] L) :=
  Rep.of (ρ.ρ.comp s.semidirectProductMulEquiv.toMonoidHom)

theorem semidirect_inl (r : N) :
    s.semidirectProductMulEquiv.toMonoidHom (SemidirectProduct.inl r) = ext.inl r := by
  change ext.inl r * s 1 = ext.inl r
  rw [map_one, mul_one]

theorem semidirect_inr (l : L) :
    s.semidirectProductMulEquiv.toMonoidHom (SemidirectProduct.inr l) = s l := by
  change ext.inl 1 * s l = s l
  rw [map_one, one_mul]

/-- The comparison of Levi modules between a split extension and its semidirect product model. -/
def semidirectModMor : Rep.res (MonoidHom.id L) (splitRadicalH1Representation s ρ) ⟶
    splitRadicalH1Representation (SemidirectProduct.inr_splitting s.conjAct) (semidirectRep s ρ) :=
  EdgeNat.modMor s (SemidirectProduct.inr_splitting s.conjAct)
    s.semidirectProductMulEquiv.toMonoidHom (MonoidHom.id L) (MonoidHom.id N) (semidirect_inl s)
    (semidirect_inr s) ρ (semidirectRep s ρ) LinearMap.id (fun _ _ => rfl)

theorem semidirectModMor_bijective : Function.Bijective (semidirectModMor s ρ).hom :=
  EdgeNat.radH1Map_bijective s.semidirectProductMulEquiv.toMonoidHom ρ (semidirectRep s ρ)
    LinearMap.id (fun _ _ => rfl) (MonoidHom.id N) (semidirect_inl s) Function.bijective_id
    Function.bijective_id

/-- **The semidirect product model of a split extension.** The Levi `H¹(L, H¹(N, E))` computed on
the split extension `E` and on the semidirect product `N ⋊ L ≃* E` are isomorphic. -/
def semidirectH1Equiv : groupCohomology.H1 (splitRadicalH1Representation s ρ) ≃ₗ[ℂ]
    groupCohomology.H1 (splitRadicalH1Representation (SemidirectProduct.inr_splitting s.conjAct)
      (semidirectRep s ρ)) :=
  LinearEquiv.ofBijective (groupCohomology.map (MonoidHom.id L) (semidirectModMor s ρ) 1).hom
    (h1MapId_bijective _ (semidirectModMor_bijective s ρ))

/-- Cuspidality is the same on the split extension and on its semidirect product model. -/
theorem semidirectH1Equiv_mem_cuspidalFamily {ι : Type} (B : ι → Subgroup L)
    (x : groupCohomology.H1 (splitRadicalH1Representation s ρ)) :
    semidirectH1Equiv s ρ x ∈ cuspidalFamily B
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting s.conjAct)
          (semidirectRep s ρ)) ↔
      x ∈ cuspidalFamily B (splitRadicalH1Representation s ρ) :=
  (EdgeNat.mem_cuspidalFamily_map_id_iff B _ (semidirectModMor_bijective s ρ) x).symm

/-- The same, in the direction from the semidirect product model to the split extension. -/
theorem semidirectH1Equiv_symm_mem_cuspidalFamily {ι : Type} (B : ι → Subgroup L)
    (w : groupCohomology.H1 (splitRadicalH1Representation (SemidirectProduct.inr_splitting s.conjAct)
      (semidirectRep s ρ))) :
    (semidirectH1Equiv s ρ).symm w ∈ cuspidalFamily B (splitRadicalH1Representation s ρ) ↔
      w ∈ cuspidalFamily B (splitRadicalH1Representation
        (SemidirectProduct.inr_splitting s.conjAct) (semidirectRep s ρ)) := by
  rw [← semidirectH1Equiv_mem_cuspidalFamily s ρ B, LinearEquiv.apply_symm_apply]

/-- The bijection `H²(E, ρ) → H²(N ⋊ L, ρ)` of a split extension and its semidirect model. -/
def semidirectH2Map : groupCohomology.H2 ρ →ₗ[ℂ] groupCohomology.H2 (semidirectRep s ρ) :=
  EdgeNat.h2Map s.semidirectProductMulEquiv.toMonoidHom ρ (semidirectRep s ρ) LinearMap.id
    (fun _ _ => rfl)

theorem semidirectH2Map_bijective : Function.Bijective (semidirectH2Map s ρ) :=
  ⟨EdgeNat.h2Map_injective s.semidirectProductMulEquiv.toMonoidHom ρ (semidirectRep s ρ)
      LinearMap.id (fun _ _ => rfl) s.semidirectProductMulEquiv.bijective Function.bijective_id,
    EdgeNat.h2Map_surjective s.semidirectProductMulEquiv.toMonoidHom ρ (semidirectRep s ρ)
      LinearMap.id (fun _ _ => rfl) s.semidirectProductMulEquiv.bijective Function.bijective_id⟩

/-- The radical restriction of a class vanishes iff that of its transport to the semidirect model
does. -/
theorem semidirectH2Map_restriction_eq_zero_iff (x : groupCohomology.H2 ρ) :
    twoCohomologyRestriction (SemidirectProduct.toGroupExtension s.conjAct).inl (semidirectRep s ρ)
        (semidirectH2Map s ρ x) = 0 ↔
      twoCohomologyRestriction ext.inl ρ x = 0 :=
  EdgeNat.restriction_h2Map_eq_zero_iff s.semidirectProductMulEquiv.toMonoidHom ρ
    (semidirectRep s ρ) LinearMap.id (fun _ _ => rfl) ext.inl
    (SemidirectProduct.toGroupExtension s.conjAct).inl (MonoidHom.id N) (semidirect_inl s)
    Function.bijective_id Function.bijective_id x

/-- **The Hochschild--Serre edge is the same on the split extension and on its semidirect
product model.** -/
theorem semidirect_edge (x : (twoCohomologyRestriction ext.inl ρ).ker) :
    splitCohomologyEdge (SemidirectProduct.inr_splitting s.conjAct) (semidirectRep s ρ)
        ⟨semidirectH2Map s ρ x.1,
          (semidirectH2Map_restriction_eq_zero_iff s ρ x.1).mpr x.2⟩ =
      semidirectH1Equiv s ρ (splitCohomologyEdge s ρ x) :=
  EdgeNat.edge_kerMap s (SemidirectProduct.inr_splitting s.conjAct)
    s.semidirectProductMulEquiv.toMonoidHom (MonoidHom.id L) (MonoidHom.id N) (semidirect_inl s)
    (semidirect_inr s) ρ (semidirectRep s ρ) LinearMap.id (fun _ _ => rfl) x

end SemidirectModel

end TernaryPeriodPolynomials.Argument.SeedC3S4c
