module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.TwistBasic

@[expose] public section


/-!
# The Hochschild-Serre edge under a twisted isomorphism of extensions

Formalized by Claude Sonnet 5.5.

`edge_kerMapX`: for a twisted isomorphism `X : ext₂ ≅ ext₁` (radical map `φ`, Levi map `α`) and a coefficient isomorphism `T`, the Hochschild-Serre edge of `ext₂` of the transported class equals the transport `Ξ̃` (cohomology
map along `α` of `radXi`) of the edge of `ext₁`.  The two splittings are arbitrary: the lift shift `edge_shift` and `h1_eq_of_twist` show that the edge class does not depend on the lift.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E₁ E₂ L : Type} [Group E₁] [Group E₂] [Group L]
  {ext₁ : GroupExtension RadicalLattice E₁ L} {ext₂ : GroupExtension RadicalLattice E₂ L}

/-- Shifting the lift `e` of a Levi element by a radical element changes the edge cocycle by the action of that element and a coboundary. -/
theorem edge_shift (ρ : Rep ℂ E₁) (z : relativeTwoCocycles ext₁.inl ρ) (e : E₁) (c rr rr' : RadicalLattice)
    (hcomm : ext₁.inl rr * e = e * ext₁.inl rr') :
    z.1 (ext₁.inl c * e, ext₁.inl rr') - z.1 (ext₁.inl rr, ext₁.inl c * e) =
      ρ.ρ (ext₁.inl c) (z.1 (e, ext₁.inl rr') - z.1 (ext₁.inl rr, e)) +
        (ρ.ρ (ext₁.inl rr) (z.1 (ext₁.inl c, e)) - z.1 (ext₁.inl c, e)) := by
  have E1 := twoCocycle_relation ρ z.1 (ext₁.inl c) e (ext₁.inl rr')
  have E2 := twoCocycle_relation ρ z.1 (ext₁.inl rr) (ext₁.inl c) e
  have E3 := twoCocycle_relation ρ z.1 (ext₁.inl c) (ext₁.inl rr) e
  have z1 : z.1 (ext₁.inl rr, ext₁.inl c) = 0 := z.2 rr c
  have z2 : z.1 (ext₁.inl c, ext₁.inl rr) = 0 := z.2 c rr
  have hRn : ext₁.inl rr * ext₁.inl c = ext₁.inl c * ext₁.inl rr := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [← hcomm] at E1
  rw [hRn, z1] at E2
  rw [z2] at E3
  rw [map_sub]
  linear_combination (norm := abel) E1 + E2 - E3

section Edge

variable (X : TwistEquiv ext₂ ext₁) (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ ≃ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (X.θ g) v) = ρ₂.ρ g (T v))

/-- The comparison morphism `Res(θ) ρ₁ ⟶ ρ₂` induced by `T`. -/
def cmpX : Rep.res X.θ.toMonoidHom ρ₁ ⟶ ρ₂ :=
  oneCocyclePullbackMorphism ρ₁ ρ₂ X.θ.toMonoidHom T.toLinearMap (fun g => by
    apply LinearMap.ext
    intro v
    exact (hT g v).symm)

/-- Transport of degree-two cohomology along `θ`. -/
def h2X : groupCohomology.H2 ρ₁ →ₗ[ℂ] groupCohomology.H2 ρ₂ :=
  (groupCohomology.map X.θ.toMonoidHom (cmpX X ρ₁ ρ₂ T hT) 2).hom

theorem h2X_π (z : groupCohomology.cocycles₂ ρ₁) :
    h2X X ρ₁ ρ₂ T hT (groupCohomology.H2π ρ₁ z) =
      groupCohomology.H2π ρ₂ (groupCohomology.mapCocycles₂ X.θ.toMonoidHom (cmpX X ρ₁ ρ₂ T hT) z) :=
  groupCohomology.H2π_comp_map_apply X.θ.toMonoidHom (cmpX X ρ₁ ρ₂ T hT) z

theorem mapCocycles₂X_apply (z : groupCohomology.cocycles₂ ρ₁) (a b : E₂) :
    (groupCohomology.mapCocycles₂ X.θ.toMonoidHom (cmpX X ρ₁ ρ₂ T hT) z).1 (a, b) =
      T (z.1 (X.θ a, X.θ b)) := rfl

theorem mapCocycles₂X_rel (z : relativeTwoCocycles ext₁.inl ρ₁) :
    groupCohomology.mapCocycles₂ X.θ.toMonoidHom (cmpX X ρ₁ ρ₂ T hT) z.val ∈ relativeTwoCocycles ext₂.inl ρ₂ := by
  intro a b
  change T (z.val.1 (X.θ (ext₂.inl a), X.θ (ext₂.inl b))) = 0
  rw [X.inl_comm, X.inl_comm]
  exact (congrArg T (z.property (X.φ a) (X.φ b))).trans (map_zero T)

/-- The transport of a relative two-cocycle. -/
def relMapX (z : relativeTwoCocycles ext₁.inl ρ₁) : relativeTwoCocycles ext₂.inl ρ₂ :=
  ⟨groupCohomology.mapCocycles₂ X.θ.toMonoidHom (cmpX X ρ₁ ρ₂ T hT) z.val, mapCocycles₂X_rel X ρ₁ ρ₂ T hT z⟩

variable (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting)

/-- The radical cohomology class of the edge cycle at `m` is transported by `radXi` from the class at `α m`. -/
theorem edgeCycle_class (z : relativeTwoCocycles ext₁.inl ρ₁) (m : L) :
    groupCohomology.H1π (Rep.res ext₂.inl ρ₂) (splitEdgeCycle s₂ ρ₂ m (relMapX X ρ₁ ρ₂ T hT z)) =
      radXi X ρ₁ ρ₂ T hT (groupCohomology.H1π (Rep.res ext₁.inl ρ₁) (splitEdgeCycle s₁ ρ₁ (X.α m) z)) := by
  obtain ⟨c₀, hc₀⟩ := X.exists_lift s₁ s₂ m
  rw [radXi_π]
  refine h1_eq_of_twist ext₂ ρ₂ _ _ (X.φ.symm c₀) (T (z.1 (ext₁.inl c₀, s₁ (X.α m)))) (fun r => ?_)
  have hr' : X.θ (ext₂.inl (splitRadicalInput s₂ m r)) = ext₁.inl (splitRadicalInput s₁ (X.α m) (X.φ r)) := by
    rw [X.inl_comm, X.radicalInput s₁ s₂ m r]
  have shift := edge_shift ρ₁ z (s₁ (X.α m)) c₀ (X.φ r) (splitRadicalInput s₁ (X.α m) (X.φ r))
    (splitRadicalInput_commute s₁ (X.α m) (X.φ r))
  have e1 := hT (ext₂.inl (X.φ.symm c₀)) (z.1 (s₁ (X.α m), ext₁.inl (splitRadicalInput s₁ (X.α m) (X.φ r))) -
    z.1 (ext₁.inl (X.φ r), s₁ (X.α m)))
  have e2 := hT (ext₂.inl r) (z.1 (ext₁.inl c₀, s₁ (X.α m)))
  rw [X.inl_comm, MulEquiv.apply_symm_apply] at e1
  rw [X.inl_comm] at e2
  rw [splitEdgeCycle_apply, oneCocyclePullback_apply, splitEdgeCycle_apply]
  change T (z.1 (X.θ (s₂ m), X.θ (ext₂.inl (splitRadicalInput s₂ m r)))) - T (z.1 (X.θ (ext₂.inl r), X.θ (s₂ m))) = _
  rw [hr', X.inl_comm r, hc₀, ← map_sub, shift, map_add, e1,
    map_sub T ((ρ₁.ρ (ext₁.inl (X.φ r))) (z.1 (ext₁.inl c₀, s₁ (X.α m)))), e2]
  rfl

/-- **The transport `H¹(L, H¹(N, ρ₁)) → H¹(L, H¹(N, ρ₂))`**: cohomology along the Levi map `α` of the radical transport `radXi`. -/
def leviXi : groupCohomology.H1 (splitRadicalH1Representation s₁ ρ₁) →ₗ[ℂ]
    groupCohomology.H1 (splitRadicalH1Representation s₂ ρ₂) :=
  oneCocyclePullbackH1 (splitRadicalH1Representation s₁ ρ₁) (splitRadicalH1Representation s₂ ρ₂) X.α.toMonoidHom
    (radXi X ρ₁ ρ₂ T hT) (fun l => LinearMap.ext fun x => (radXi_levi X ρ₁ ρ₂ T hT s₁ s₂ l x).symm)

theorem leviXi_π (c : groupCohomology.cocycles₁ (splitRadicalH1Representation s₁ ρ₁)) :
    leviXi X ρ₁ ρ₂ T hT s₁ s₂ (groupCohomology.H1π _ c) = groupCohomology.H1π _
      (oneCocyclePullback (splitRadicalH1Representation s₁ ρ₁) (splitRadicalH1Representation s₂ ρ₂) X.α.toMonoidHom
        (radXi X ρ₁ ρ₂ T hT) (fun l => LinearMap.ext fun x => (radXi_levi X ρ₁ ρ₂ T hT s₁ s₂ l x).symm) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

/-- **The Hochschild-Serre edge is natural for a twisted isomorphism of extensions** (relative cocycle form). -/
theorem edge_relMapX (z : relativeTwoCocycles ext₁.inl ρ₁) :
    splitCohomologyEdge s₂ ρ₂ (relativeTwoCocycleClass ext₂.inl ρ₂ (relMapX X ρ₁ ρ₂ T hT z)) =
      leviXi X ρ₁ ρ₂ T hT s₁ s₂ (splitCohomologyEdge s₁ ρ₁ (relativeTwoCocycleClass ext₁.inl ρ₁ z)) := by
  rw [splitCohomologyEdge_apply, splitCohomologyEdge_apply, leviXi_π]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro m
  exact edgeCycle_class X ρ₁ ρ₂ T hT s₁ s₂ z m

theorem relMapX_class (z : relativeTwoCocycles ext₁.inl ρ₁) :
    (relativeTwoCocycleClass ext₂.inl ρ₂ (relMapX X ρ₁ ρ₂ T hT z)).val =
      h2X X ρ₁ ρ₂ T hT (relativeTwoCocycleClass ext₁.inl ρ₁ z).val := by
  rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, h2X_π]
  rfl

theorem h2X_ker (y : groupCohomology.H2 ρ₁) (hy : twoCohomologyRestriction ext₁.inl ρ₁ y = 0) :
    twoCohomologyRestriction ext₂.inl ρ₂ (h2X X ρ₁ ρ₂ T hT y) = 0 := by
  obtain ⟨z, hz⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective ρ₁ ⟨y, hy⟩
  have h2 : (relativeTwoCocycleClass ext₁.inl ρ₁ z).val = y := congrArg Subtype.val hz
  rw [← h2, ← relMapX_class X ρ₁ ρ₂ T hT z]
  exact (relativeTwoCocycleClass ext₂.inl ρ₂ _).2

/-- The transport of the radical-kernel classes of `H²`. -/
def kerMapX : (twoCohomologyRestriction ext₁.inl ρ₁).ker →ₗ[ℂ] (twoCohomologyRestriction ext₂.inl ρ₂).ker :=
  (h2X X ρ₁ ρ₂ T hT).restrict (fun y hy => h2X_ker X ρ₁ ρ₂ T hT y hy)

theorem kerMapX_val (x : (twoCohomologyRestriction ext₁.inl ρ₁).ker) :
    (kerMapX X ρ₁ ρ₂ T hT x).val = h2X X ρ₁ ρ₂ T hT x.val := rfl

/-- **Edge naturality for a twisted isomorphism of extensions**, for arbitrary splittings of the two extensions. -/
theorem edge_kerMapX (x : (twoCohomologyRestriction ext₁.inl ρ₁).ker) :
    splitCohomologyEdge s₂ ρ₂ (kerMapX X ρ₁ ρ₂ T hT x) =
      leviXi X ρ₁ ρ₂ T hT s₁ s₂ (splitCohomologyEdge s₁ ρ₁ x) := by
  obtain ⟨z, rfl⟩ := relativeTwoCocycleClass_surjective ext₁.inl ext₁.inl_injective ρ₁ x
  rw [← edge_relMapX X ρ₁ ρ₂ T hT s₁ s₂ z]
  congr 1
  apply Subtype.ext
  rw [kerMapX_val, ← relMapX_class]

end Edge

end TernaryPeriodPolynomials.Argument.FrameInvariance
