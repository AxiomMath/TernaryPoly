module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.MixedCuspidal

@[expose] public section


/-!
# Transport of a face along an isomorphism of the plane groups

Paper: Lemma C.3 (`ar:lem:seed`),: "Rationally conjugate the finitely many other plane cusps to `P` and
sum the same construction over them"; the faces of type `P` have mixed cuspidal groups `𝒞_R(E)`
 attached to their own radical, Levi and coefficient module.

An extension `ext₂ : N → E₂ → L` that is equivalent (`GroupExtension.Equiv`) to `ext₁ : N → E₁ → L`,
with coefficient modules `ρ₁`, `ρ₂` identified by a linear equivalence `T` intertwining
`ρ₁ ∘ α` with `ρ₂` (`α : E₂ ≃* E₁`), and the splitting `s₂ = α⁻¹ ∘ s₁`, has

* the same Levi action on the radical (`radicalInput_eq`), hence an isomorphism of `L`-modules
  `H¹(N, ρ₁) ≅ H¹(N, ρ₂)` (`modIso`);
* a transport `h2Map : H²(E₁, ρ₁) → H²(E₂, ρ₂)` preserving the radical-zero classes (`kerMap`)
  and carrying the Hochschild--Serre edge of `ext₁` to that of `ext₂` composed with `modIso`
  (`edge_kerMap`);
* the same cuspidal subspace of `H¹(L, H¹(N, E))` up to `modIso` (`cuspidal_map_eq`).

`pullbackExt`/`pullbackEquiv` produce `ext₂` from `ext₁` and `α` (the conjugate plane group).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace FaceTransport

variable {N E₁ E₂ L : Type} [Group N] [Group E₁] [Group E₂] [Group L]
  {ext₁ : GroupExtension N E₁ L} {ext₂ : GroupExtension N E₂ L}

/-- The splitting of `ext₂` transported from a splitting of `ext₁` along an equivalence of
extensions `ext₂ ≃ ext₁`. -/
def splitting (eq : ext₂.Equiv ext₁) (s₁ : ext₁.Splitting) : ext₂.Splitting where
  toFun := fun m => eq.toMulEquiv.symm (s₁ m)
  map_one' := by simp
  map_mul' := by intro a b; simp
  rightInverse_rightHom := by
    intro m
    have h := congrFun eq.rightHom_comm (eq.toMulEquiv.symm (s₁ m))
    simp only [Function.comp_apply, MulEquiv.apply_symm_apply] at h
    rw [← h]
    exact s₁.rightInverse_rightHom m


theorem map_H1_π {G : Type} [Group G] {A B : Rep ℂ G} (φ : A ⟶ B)
    (c : groupCohomology.cocycles₁ A) :
    (groupCohomology.map (MonoidHom.id G) φ 1).hom (groupCohomology.H1π A c) =
      groupCohomology.H1π B (groupCohomology.mapCocycles₁ (MonoidHom.id G) φ c) :=
  groupCohomology.H1π_comp_map_apply (MonoidHom.id G) φ c

theorem iso_H1_π {G : Type} [Group G] {A B : Rep ℂ G} (e : A ≅ B)
    (c : groupCohomology.cocycles₁ A) :
    ((groupCohomology.functor ℂ G 1).mapIso e).toLinearEquiv (groupCohomology.H1π A c) =
      groupCohomology.H1π B (groupCohomology.mapCocycles₁ (MonoidHom.id G) e.hom c) :=
  groupCohomology.H1π_comp_map_apply (MonoidHom.id G) e.hom c

variable (eq : ext₂.Equiv ext₁) (s₁ : ext₁.Splitting)

theorem splitting_apply (m : L) : splitting eq s₁ m = eq.toMulEquiv.symm (s₁ m) := rfl

theorem equiv_splitting (m : L) : eq.toMulEquiv (splitting eq s₁ m) = s₁ m := by
  rw [splitting_apply, MulEquiv.apply_symm_apply]

theorem equiv_inl (r : N) : eq.toMulEquiv (ext₂.inl r) = ext₁.inl r :=
  congrFun eq.inl_comm r

/-- The Levi action on the radical is the same for the transported splitting. -/
theorem radicalInput_eq (m : L) (r : N) :
    splitRadicalInput (splitting eq s₁) m r = splitRadicalInput s₁ m r := by
  apply ext₁.inl_injective
  have h1 := ext₁.inl_conjAct_comm (e := s₁ m⁻¹) (n := r)
  have h2 := ext₂.inl_conjAct_comm (e := (splitting eq s₁) m⁻¹) (n := r)
  have h3 := congrArg eq.toMulEquiv h2
  rw [equiv_inl, map_mul, map_mul, equiv_inl, eq.toMulEquiv.map_inv, equiv_splitting] at h3
  exact h3.trans h1.symm


variable (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ ≃ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (eq.toMulEquiv g) v) = ρ₂.ρ g (T v))

include hT in
theorem hT_rad (r : N) (v : ρ₁) : T (ρ₁.ρ (ext₁.inl r) v) = ρ₂.ρ (ext₂.inl r) (T v) := by
  have h := hT (ext₂.inl r) v
  rwa [equiv_inl] at h

/-- The radical coefficient modules are isomorphic. -/
def radEquivRep : (Rep.res ext₁.inl ρ₁).ρ.Equiv (Rep.res ext₂.inl ρ₂).ρ :=
  Representation.Equiv.mk T (by
    intro r
    apply LinearMap.ext
    intro v
    exact hT_rad eq ρ₁ ρ₂ T hT r v)

/-- The radical coefficient modules as an isomorphism of `N`-representations. -/
def radIso : Rep.res ext₁.inl ρ₁ ≅ Rep.res ext₂.inl ρ₂ :=
  Rep.mkIso (radEquivRep eq ρ₁ ρ₂ T hT)


/-- The induced linear equivalence on radical cohomology. -/
def radH1Equiv : groupCohomology.H1 (Rep.res ext₁.inl ρ₁) ≃ₗ[ℂ]
    groupCohomology.H1 (Rep.res ext₂.inl ρ₂) :=
  ((groupCohomology.functor ℂ N 1).mapIso (radIso eq ρ₁ ρ₂ T hT)).toLinearEquiv

theorem radH1Equiv_π (c : groupCohomology.cocycles₁ (Rep.res ext₁.inl ρ₁)) :
    radH1Equiv eq ρ₁ ρ₂ T hT (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (groupCohomology.mapCocycles₁ (MonoidHom.id N)
        (radIso eq ρ₁ ρ₂ T hT).hom c) :=
  iso_H1_π (radIso eq ρ₁ ρ₂ T hT) c

theorem radIso_hom_apply (v : ρ₁) : (radIso eq ρ₁ ρ₂ T hT).hom.hom v = T v := rfl

/-- The Levi modules `H¹(N, E)` of the two faces are isomorphic. -/
def modIso : splitRadicalH1Representation s₁ ρ₁ ≅
    splitRadicalH1Representation (splitting eq s₁) ρ₂ :=
  Rep.mkIso (Representation.Equiv.mk (radH1Equiv eq ρ₁ ρ₂ T hT) (by
    intro m
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext₁.inl ρ₁) x
    change radH1Equiv eq ρ₁ ρ₂ T hT (splitRadicalH1Action s₁ ρ₁ m (groupCohomology.H1π _ c)) =
      splitRadicalH1Action (splitting eq s₁) ρ₂ m (radH1Equiv eq ρ₁ ρ₂ T hT (groupCohomology.H1π _ c))
    rw [splitRadicalH1Action_apply, radH1Equiv_π, radH1Equiv_π, splitRadicalH1Action_apply]
    congr 1
    apply groupCohomology.cocycles₁_ext
    intro r
    change T (ρ₁.ρ (s₁ m) (c.1 (splitRadicalInput s₁ m r))) =
      ρ₂.ρ (splitting eq s₁ m) (T (c.1 (splitRadicalInput (splitting eq s₁) m r)))
    rw [radicalInput_eq, ← hT (splitting eq s₁ m), equiv_splitting]))


/-- The comparison morphism `Res(α) ρ₁ ⟶ ρ₂` induced by `T`. -/
def comparison : Rep.res eq.toMulEquiv.toMonoidHom ρ₁ ⟶ ρ₂ :=
  oneCocyclePullbackMorphism ρ₁ ρ₂ eq.toMulEquiv.toMonoidHom T.toLinearMap (fun g => by
    apply LinearMap.ext
    intro v
    exact (hT g v).symm)

/-- Transport of degree-two cohomology along the equivalence of the middle groups. -/
def h2Map : groupCohomology.H2 ρ₁ →ₗ[ℂ] groupCohomology.H2 ρ₂ :=
  (groupCohomology.map eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) 2).hom

theorem h2Map_π (z : groupCohomology.cocycles₂ ρ₁) :
    h2Map eq ρ₁ ρ₂ T hT (groupCohomology.H2π ρ₁ z) =
      groupCohomology.H2π ρ₂ (groupCohomology.mapCocycles₂ eq.toMulEquiv.toMonoidHom
        (comparison eq ρ₁ ρ₂ T hT) z) :=
  groupCohomology.H2π_comp_map_apply eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) z

theorem mapCocycles₂_apply (z : groupCohomology.cocycles₂ ρ₁) (a b : E₂) :
    (groupCohomology.mapCocycles₂ eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) z).1 (a, b) =
      T (z.1 (eq.toMulEquiv a, eq.toMulEquiv b)) := rfl

theorem mapCocycles₂_rel (z : relativeTwoCocycles ext₁.inl ρ₁) :
    groupCohomology.mapCocycles₂ eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) z.val ∈
      relativeTwoCocycles ext₂.inl ρ₂ := by
  intro a b
  have := z.property a b
  change z.val.1 (ext₁.inl a, ext₁.inl b) = 0 at this
  change T (z.val.1 (eq.toMulEquiv (ext₂.inl a), eq.toMulEquiv (ext₂.inl b))) = 0
  rw [equiv_inl, equiv_inl, this, map_zero]


theorem splitEdgeCycle_transport (m : L) (z : relativeTwoCocycles ext₁.inl ρ₁) :
    splitEdgeCycle (splitting eq s₁) ρ₂ m
        ⟨groupCohomology.mapCocycles₂ eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) z.val,
          mapCocycles₂_rel eq ρ₁ ρ₂ T hT z⟩ =
      groupCohomology.mapCocycles₁ (MonoidHom.id N) (radIso eq ρ₁ ρ₂ T hT).hom
        (splitEdgeCycle s₁ ρ₁ m z) := by
  apply groupCohomology.cocycles₁_ext
  intro r
  rw [splitEdgeCycle_apply]
  change T (z.val.1 (eq.toMulEquiv (splitting eq s₁ m),
      eq.toMulEquiv (ext₂.inl (splitRadicalInput (splitting eq s₁) m r)))) -
    T (z.val.1 (eq.toMulEquiv (ext₂.inl r), eq.toMulEquiv (splitting eq s₁ m))) =
    T (splitEdgeCycle s₁ ρ₁ m z r)
  rw [splitEdgeCycle_apply, equiv_splitting, equiv_inl, equiv_inl, radicalInput_eq, map_sub]
  rfl

/-- **The Hochschild--Serre edge is natural for the transport of faces.** -/
theorem edge_h2Map (z : relativeTwoCocycles ext₁.inl ρ₁) :
    ∃ z₂ : relativeTwoCocycles ext₂.inl ρ₂,
      (relativeTwoCocycleClass ext₂.inl ρ₂ z₂).val =
          h2Map eq ρ₁ ρ₂ T hT (relativeTwoCocycleClass ext₁.inl ρ₁ z).val ∧
        splitCohomologyEdge (splitting eq s₁) ρ₂ (relativeTwoCocycleClass ext₂.inl ρ₂ z₂) =
          (groupCohomology.map (MonoidHom.id L) (modIso eq s₁ ρ₁ ρ₂ T hT).hom 1).hom
            (splitCohomologyEdge s₁ ρ₁ (relativeTwoCocycleClass ext₁.inl ρ₁ z)) := by
  refine ⟨⟨groupCohomology.mapCocycles₂ eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) z.val,
    mapCocycles₂_rel eq ρ₁ ρ₂ T hT z⟩, ?_, ?_⟩
  · rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, h2Map_π]
  · rw [splitCohomologyEdge_apply, splitCohomologyEdge_apply]
    rw [map_H1_π (modIso eq s₁ ρ₁ ρ₂ T hT).hom]
    congr 1
    apply groupCohomology.cocycles₁_ext
    intro m
    change groupCohomology.H1π _ (splitEdgeCycle (splitting eq s₁) ρ₂ m _) =
      radH1Equiv eq ρ₁ ρ₂ T hT (groupCohomology.H1π _ (splitEdgeCycle s₁ ρ₁ m z))
    rw [radH1Equiv_π, splitEdgeCycle_transport]


/-- The extension `ext₁` pulled back along an isomorphism `α : E₂ ≃* E₁` of the middle groups. -/
def pullbackExt (ext : GroupExtension N E₁ L) (α : E₂ ≃* E₁) : GroupExtension N E₂ L where
  inl := α.symm.toMonoidHom.comp ext.inl
  rightHom := ext.rightHom.comp α.toMonoidHom
  inl_injective := α.symm.injective.comp ext.inl_injective
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      change ext.rightHom (α (α.symm (ext.inl n))) = 1
      rw [MulEquiv.apply_symm_apply]
      have : ext.inl n ∈ ext.rightHom.ker := by rw [← ext.range_inl_eq_ker_rightHom]; exact ⟨n, rfl⟩
      exact this
    · intro hx
      have hx' : α x ∈ ext.inl.range := by
        rw [ext.range_inl_eq_ker_rightHom]; exact hx
      obtain ⟨n, hn⟩ := hx'
      exact ⟨n, by change α.symm (ext.inl n) = x; rw [hn]; simp⟩
  rightHom_surjective := ext.rightHom_surjective.comp α.surjective

/-- The pulled back extension is equivalent to the original one. -/
def pullbackEquiv (ext : GroupExtension N E₁ L) (α : E₂ ≃* E₁) : (pullbackExt ext α).Equiv ext where
  toMulEquiv := α
  inl_comm := by
    funext n
    change α (α.symm (ext.inl n)) = ext.inl n
    simp
  rightHom_comm := rfl


theorem rel_transport_class (z : relativeTwoCocycles ext₁.inl ρ₁) :
    (relativeTwoCocycleClass ext₂.inl ρ₂
      ⟨groupCohomology.mapCocycles₂ eq.toMulEquiv.toMonoidHom (comparison eq ρ₁ ρ₂ T hT) z.val,
        mapCocycles₂_rel eq ρ₁ ρ₂ T hT z⟩).val =
      h2Map eq ρ₁ ρ₂ T hT (relativeTwoCocycleClass ext₁.inl ρ₁ z).val := by
  rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, h2Map_π]

theorem h2Map_ker (y : groupCohomology.H2 ρ₁)
    (hy : twoCohomologyRestriction ext₁.inl ρ₁ y = 0) :
    twoCohomologyRestriction ext₂.inl ρ₂ (h2Map eq ρ₁ ρ₂ T hT y) = 0 := by
  obtain ⟨z, hz⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective ρ₁ ⟨y, hy⟩
  have h2 : (relativeTwoCocycleClass ext₁.inl ρ₁ z).val = y := congrArg Subtype.val hz
  rw [← h2, ← rel_transport_class]
  exact (relativeTwoCocycleClass ext₂.inl ρ₂ _).2

/-- The transport of the radical-kernel classes of `H²`. -/
def kerMap : (twoCohomologyRestriction ext₁.inl ρ₁).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext₂.inl ρ₂).ker :=
  (h2Map eq ρ₁ ρ₂ T hT).restrict (fun y hy => h2Map_ker eq ρ₁ ρ₂ T hT y hy)

theorem kerMap_val (x : (twoCohomologyRestriction ext₁.inl ρ₁).ker) :
    (kerMap eq ρ₁ ρ₂ T hT x).val = h2Map eq ρ₁ ρ₂ T hT x.val := rfl

/-- **The Hochschild--Serre edge is natural for the transport of faces.** -/
theorem edge_kerMap (x : (twoCohomologyRestriction ext₁.inl ρ₁).ker) :
    splitCohomologyEdge (splitting eq s₁) ρ₂ (kerMap eq ρ₁ ρ₂ T hT x) =
      (groupCohomology.map (MonoidHom.id L) (modIso eq s₁ ρ₁ ρ₂ T hT).hom 1).hom
        (splitCohomologyEdge s₁ ρ₁ x) := by
  obtain ⟨z, rfl⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective ρ₁ x
  obtain ⟨z₂, h1, h2⟩ := edge_h2Map eq s₁ ρ₁ ρ₂ T hT z
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [kerMap_val, ← h1]


section CuspidalTransport

variable {Λ : Subgroup SL(2, ℤ)}

/-- The cuspidal condition transports along an isomorphism of `Λ`-modules (surjective form). -/
theorem cuspidal_map_eq {V W : Rep ℂ Λ} (e : V ≅ W) :
    Submodule.map (groupCohomology.map (MonoidHom.id Λ) e.hom 1).hom (cuspidalSubspace Λ V) =
      cuspidalSubspace Λ W := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (cuspidal_iso_iff e x).mp hx
  · intro hy
    obtain ⟨x, hx⟩ := ((groupCohomology.functor ℂ Λ 1).mapIso e).toLinearEquiv.surjective y
    refine ⟨x, ?_, hx⟩
    exact (cuspidal_iso_iff e x).mpr (by
      have : ModuleCat.Hom.hom ((groupCohomology.functor ℂ Λ 1).mapIso e).hom x = y := hx
      rw [this]; exact hy)

end CuspidalTransport

end FaceTransport

end TernaryPeriodPolynomials.Argument.SeedC3S4c
