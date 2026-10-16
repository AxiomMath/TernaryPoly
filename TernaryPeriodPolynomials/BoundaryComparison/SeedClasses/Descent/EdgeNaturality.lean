module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.CuspidalFamily

@[expose] public section


/-!
# Naturality of the Hochschild--Serre edge for morphisms of split extensions

Paper: Lemma C.3 (`ar:lem:seed`),
 (the mixed cuspidal group of a face, "the same letters for rational
conjugates", restrictions at the cusps of the binary Levi).

Generalizes `FaceTransport` to morphisms `(τ, α, σ) : ext₂ → ext₁` of split group extensions
`N₂ → E₂ → L₂` and `N₁ → E₁ → L₁` which are not nec. isomorphisms and which may act nontrivially on the
radical (`τ`) and on the Levi (`σ`), compatible with the splittings (`α ∘ s₂ = s₁ ∘ σ`) and with a
comparison `T : ρ₁ → ρ₂` of coefficient modules (`T(ρ₁(α g) v) = ρ₂(g)(T v)`):

* `radH1Map`, `modMor`: the induced morphism of Levi modules `Res_σ H¹(N₁, ρ₁) ⟶ H¹(N₂, ρ₂)`;
* `h2Map`, `kerMap`: the pullback `H²(E₁, ρ₁) → H²(E₂, ρ₂)` along `α`, preserving the radical-zero
  classes;
* `edge_kerMap`: `edge₂ ∘ kerMap = H¹(σ, modMor) ∘ edge₁`.

Instances: restriction to the preimage of a subgroup of the Levi (the stabilizer of a complete flag),
change of frame of a plane cusp (conjugation, with its action on the Levi and the radical),
inclusion of the determinant-one part.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace EdgeNat

theorem map_H1_π_gen {G H : Type} [Group G] [Group H] (f : G →* H) {A : Rep ℂ H} {B : Rep ℂ G}
    (φ : Rep.res f A ⟶ B) (c : groupCohomology.cocycles₁ A) :
    (groupCohomology.map f φ 1).hom (groupCohomology.H1π A c) =
      groupCohomology.H1π B (groupCohomology.mapCocycles₁ f φ c) :=
  groupCohomology.H1π_comp_map_apply f φ c

variable {N₁ N₂ E₁ E₂ L₁ L₂ : Type} [Group N₁] [Group N₂] [Group E₁] [Group E₂] [Group L₁]
  [Group L₂] {ext₁ : GroupExtension N₁ E₁ L₁} {ext₂ : GroupExtension N₂ E₂ L₂}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (α : E₂ →* E₁) (σ : L₂ →* L₁) (τ : N₂ →* N₁)
  (hinl : ∀ r, α (ext₂.inl r) = ext₁.inl (τ r)) (hsplit : ∀ m, α (s₂ m) = s₁ (σ m))

include hinl hsplit in
/-- The Levi actions on the radical agree along `σ` and `τ`. -/
theorem radicalInput_nat (m : L₂) (r : N₂) :
    τ (splitRadicalInput s₂ m r) = splitRadicalInput s₁ (σ m) (τ r) := by
  apply ext₁.inl_injective
  have h1 := ext₁.inl_conjAct_comm (e := s₁ (σ m)⁻¹) (n := τ r)
  have h2 := ext₂.inl_conjAct_comm (e := s₂ m⁻¹) (n := r)
  have h3 := congrArg α h2
  rw [hinl, map_mul, map_mul, hinl, α.map_inv, hsplit, σ.map_inv] at h3
  exact h3.trans h1.symm

variable (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ →ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (α g) v) = ρ₂.ρ g (T v))

include hinl hT in
theorem hT_rad (r : N₂) (v : ρ₁) :
    T (ρ₁.ρ (ext₁.inl (τ r)) v) = ρ₂.ρ (ext₂.inl r) (T v) := by
  have h := hT (ext₂.inl r) v
  rwa [hinl] at h

include hinl hT in
/-- The comparison on radical cohomology `H¹(N₁, ρ₁|_{N₁}) → H¹(N₂, ρ₂|_{N₂})`. -/
def radH1Map : groupCohomology.H1 (Rep.res ext₁.inl ρ₁) →ₗ[ℂ]
    groupCohomology.H1 (Rep.res ext₂.inl ρ₂) :=
  oneCocyclePullbackH1 (Rep.res ext₁.inl ρ₁) (Rep.res ext₂.inl ρ₂) τ T (by
    intro r
    apply LinearMap.ext
    intro v
    exact (hT_rad α τ hinl ρ₁ ρ₂ T hT r v).symm)

theorem radH1Map_π (c : groupCohomology.cocycles₁ (Rep.res ext₁.inl ρ₁)) :
    radH1Map α τ hinl ρ₁ ρ₂ T hT (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (oneCocyclePullback (Rep.res ext₁.inl ρ₁) (Rep.res ext₂.inl ρ₂)
        τ T (by
          intro r
          apply LinearMap.ext
          intro v
          exact (hT_rad α τ hinl ρ₁ ρ₂ T hT r v).symm) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

include hinl hsplit hT in
theorem radH1Map_equivariant (m : L₂)
    (x : groupCohomology.H1 (Rep.res ext₁.inl ρ₁)) :
    radH1Map α τ hinl ρ₁ ρ₂ T hT (splitRadicalH1Action s₁ ρ₁ (σ m) x) =
      splitRadicalH1Action s₂ ρ₂ m (radH1Map α τ hinl ρ₁ ρ₂ T hT x) := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext₁.inl ρ₁) x
  rw [splitRadicalH1Action_apply, radH1Map_π, radH1Map_π, splitRadicalH1Action_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro r
  change T (ρ₁.ρ (s₁ (σ m)) (c.1 (splitRadicalInput s₁ (σ m) (τ r)))) =
    ρ₂.ρ (s₂ m) (T (c.1 (τ (splitRadicalInput s₂ m r))))
  rw [radicalInput_nat s₁ s₂ α σ τ hinl hsplit, ← hT (s₂ m), hsplit]

include hinl hsplit hT in
/-- The comparison of Levi modules, as a morphism of `L₂`-representations. -/
def modMor : Rep.res σ (splitRadicalH1Representation s₁ ρ₁) ⟶
    splitRadicalH1Representation s₂ ρ₂ :=
  oneCocyclePullbackMorphism (splitRadicalH1Representation s₁ ρ₁)
    (splitRadicalH1Representation s₂ ρ₂) σ (radH1Map α τ hinl ρ₁ ρ₂ T hT) (by
      intro m
      apply LinearMap.ext
      intro x
      exact (radH1Map_equivariant s₁ s₂ α σ τ hinl hsplit ρ₁ ρ₂ T hT m x).symm)

include hT in
/-- The comparison morphism `Res(α) ρ₁ ⟶ ρ₂` induced by `T`. -/
def comparison : Rep.res α ρ₁ ⟶ ρ₂ :=
  oneCocyclePullbackMorphism ρ₁ ρ₂ α T (fun g => by
    apply LinearMap.ext
    intro v
    exact (hT g v).symm)

/-- Transport of degree-two cohomology along `α`. -/
def h2Map : groupCohomology.H2 ρ₁ →ₗ[ℂ] groupCohomology.H2 ρ₂ :=
  (groupCohomology.map α (comparison α ρ₁ ρ₂ T hT) 2).hom

theorem h2Map_π (z : groupCohomology.cocycles₂ ρ₁) :
    h2Map α ρ₁ ρ₂ T hT (groupCohomology.H2π ρ₁ z) =
      groupCohomology.H2π ρ₂ (groupCohomology.mapCocycles₂ α (comparison α ρ₁ ρ₂ T hT) z) :=
  groupCohomology.H2π_comp_map_apply α (comparison α ρ₁ ρ₂ T hT) z

include hinl in
theorem mapCocycles₂_rel (z : relativeTwoCocycles ext₁.inl ρ₁) :
    groupCohomology.mapCocycles₂ α (comparison α ρ₁ ρ₂ T hT) z.val ∈
      relativeTwoCocycles ext₂.inl ρ₂ := by
  intro a b
  have := z.property (τ a) (τ b)
  change z.val.1 (ext₁.inl (τ a), ext₁.inl (τ b)) = 0 at this
  change T (z.val.1 (α (ext₂.inl a), α (ext₂.inl b))) = 0
  rw [hinl, hinl, this, map_zero]

include hinl hsplit hT in
theorem splitEdgeCycle_nat (m : L₂) (z : relativeTwoCocycles ext₁.inl ρ₁) :
    splitEdgeCycle s₂ ρ₂ m
        ⟨groupCohomology.mapCocycles₂ α (comparison α ρ₁ ρ₂ T hT) z.val,
          mapCocycles₂_rel α τ hinl ρ₁ ρ₂ T hT z⟩ =
      oneCocyclePullback (Rep.res ext₁.inl ρ₁) (Rep.res ext₂.inl ρ₂) τ T (by
          intro r
          apply LinearMap.ext
          intro v
          exact (hT_rad α τ hinl ρ₁ ρ₂ T hT r v).symm) (splitEdgeCycle s₁ ρ₁ (σ m) z) := by
  apply groupCohomology.cocycles₁_ext
  intro r
  rw [splitEdgeCycle_apply]
  change T (z.val.1 (α (s₂ m), α (ext₂.inl (splitRadicalInput s₂ m r)))) -
    T (z.val.1 (α (ext₂.inl r), α (s₂ m))) = T (splitEdgeCycle s₁ ρ₁ (σ m) z (τ r))
  rw [splitEdgeCycle_apply, hsplit, hinl, hinl, radicalInput_nat s₁ s₂ α σ τ hinl hsplit, map_sub]
  rfl

theorem rel_nat_class (z : relativeTwoCocycles ext₁.inl ρ₁) :
    (relativeTwoCocycleClass ext₂.inl ρ₂
      ⟨groupCohomology.mapCocycles₂ α (comparison α ρ₁ ρ₂ T hT) z.val,
        mapCocycles₂_rel α τ hinl ρ₁ ρ₂ T hT z⟩).val =
      h2Map α ρ₁ ρ₂ T hT (relativeTwoCocycleClass ext₁.inl ρ₁ z).val := by
  rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, h2Map_π]

include hinl hsplit hT in
/-- **Naturality of the Hochschild--Serre edge** for a morphism of split extensions
`(τ, α, σ) : ext₂ → ext₁` compatible with the splittings and with the coefficient comparison
`T`. -/
theorem edge_nat (z : relativeTwoCocycles ext₁.inl ρ₁) :
    ∃ z₂ : relativeTwoCocycles ext₂.inl ρ₂,
      (relativeTwoCocycleClass ext₂.inl ρ₂ z₂).val =
          h2Map α ρ₁ ρ₂ T hT (relativeTwoCocycleClass ext₁.inl ρ₁ z).val ∧
        splitCohomologyEdge s₂ ρ₂ (relativeTwoCocycleClass ext₂.inl ρ₂ z₂) =
          (groupCohomology.map σ (modMor s₁ s₂ α σ τ hinl hsplit ρ₁ ρ₂ T hT) 1).hom
            (splitCohomologyEdge s₁ ρ₁ (relativeTwoCocycleClass ext₁.inl ρ₁ z)) := by
  refine ⟨⟨groupCohomology.mapCocycles₂ α (comparison α ρ₁ ρ₂ T hT) z.val,
    mapCocycles₂_rel α τ hinl ρ₁ ρ₂ T hT z⟩, rel_nat_class α τ hinl ρ₁ ρ₂ T hT z, ?_⟩
  rw [splitCohomologyEdge_apply, splitCohomologyEdge_apply,
    map_H1_π_gen σ (modMor s₁ s₂ α σ τ hinl hsplit ρ₁ ρ₂ T hT)]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro m
  change groupCohomology.H1π _ (splitEdgeCycle s₂ ρ₂ m _) =
    radH1Map α τ hinl ρ₁ ρ₂ T hT (groupCohomology.H1π _ (splitEdgeCycle s₁ ρ₁ (σ m) z))
  rw [radH1Map_π, splitEdgeCycle_nat s₁ s₂ α σ τ hinl hsplit ρ₁ ρ₂ T hT]

include hinl hT in
theorem h2Map_ker (y : groupCohomology.H2 ρ₁)
    (hy : twoCohomologyRestriction ext₁.inl ρ₁ y = 0) :
    twoCohomologyRestriction ext₂.inl ρ₂ (h2Map α ρ₁ ρ₂ T hT y) = 0 := by
  obtain ⟨z, hz⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective ρ₁ ⟨y, hy⟩
  have h2 : (relativeTwoCocycleClass ext₁.inl ρ₁ z).val = y := congrArg Subtype.val hz
  rw [← h2, ← rel_nat_class α τ hinl ρ₁ ρ₂ T hT]
  exact (relativeTwoCocycleClass ext₂.inl ρ₂ _).2

include hinl hT in
/-- The transport of the radical-kernel classes of `H²`. -/
def kerMap : (twoCohomologyRestriction ext₁.inl ρ₁).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext₂.inl ρ₂).ker :=
  (h2Map α ρ₁ ρ₂ T hT).restrict (fun y hy => h2Map_ker α τ hinl ρ₁ ρ₂ T hT y hy)

include hinl hT in
theorem kerMap_val (x : (twoCohomologyRestriction ext₁.inl ρ₁).ker) :
    (kerMap α τ hinl ρ₁ ρ₂ T hT x).val = h2Map α ρ₁ ρ₂ T hT x.val := rfl

include hinl hsplit hT in
/-- **Naturality of the edge on the radical-kernel classes.** -/
theorem edge_kerMap (x : (twoCohomologyRestriction ext₁.inl ρ₁).ker) :
    splitCohomologyEdge s₂ ρ₂ (kerMap α τ hinl ρ₁ ρ₂ T hT x) =
      (groupCohomology.map σ (modMor s₁ s₂ α σ τ hinl hsplit ρ₁ ρ₂ T hT) 1).hom
        (splitCohomologyEdge s₁ ρ₁ x) := by
  obtain ⟨z, rfl⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective ρ₁ x
  obtain ⟨z₂, h1, h2⟩ := edge_nat s₁ s₂ α σ τ hinl hsplit ρ₁ ρ₂ T hT z
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [kerMap_val, ← h1]

end EdgeNat

end TernaryPeriodPolynomials.Argument.SeedC3S4c
