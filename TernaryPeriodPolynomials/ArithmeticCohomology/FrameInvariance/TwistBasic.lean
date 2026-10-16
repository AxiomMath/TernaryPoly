module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Transport

@[expose] public section


/-!
# Twisted isomorphisms of split extensions: the lift action and the radical map

Formalized by Claude Sonnet 5.5.

A twisted isomorphism `ext₂ ≅ ext₁` of extensions `RadicalLattice → E → L` consists of `θ : E₂ ≃* E₁` inducing `φ` on the radical and `α` on the Levi quotient.
Neither splitting is assumed compatible: two lifts of the same Levi element differ by a radical element, which acts trivially on `H¹(N, E)` because the radical lattice is abelian (`h1_eq_of_twist`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E₁ E₂ L : Type} [Group E₁] [Group E₂] [Group L]

/-- A twisted isomorphism of extensions of `L` by the radical lattice. -/
structure TwistEquiv (ext₂ : GroupExtension RadicalLattice E₂ L) (ext₁ : GroupExtension RadicalLattice E₁ L) where
  θ : E₂ ≃* E₁
  φ : RadicalLattice ≃* RadicalLattice
  α : L ≃* L
  inl_comm : ∀ r, θ (ext₂.inl r) = ext₁.inl (φ r)
  rightHom_comm : ∀ e, ext₁.rightHom (θ e) = α (ext₂.rightHom e)

variable {ext₁ : GroupExtension RadicalLattice E₁ L} {ext₂ : GroupExtension RadicalLattice E₂ L}

/-- Two lifts of a Levi element differ by a radical element. -/
theorem TwistEquiv.exists_lift (X : TwistEquiv ext₂ ext₁) (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (l : L) :
    ∃ c : RadicalLattice, X.θ (s₂ l) = ext₁.inl c * s₁ (X.α l) := by
  have h1 : ext₁.rightHom (X.θ (s₂ l) * (s₁ (X.α l))⁻¹) = 1 := by
    have e1 : ext₁.rightHom (s₁ (X.α l)) = X.α l := s₁.rightInverse_rightHom _
    have e2 : ext₂.rightHom (s₂ l) = l := s₂.rightInverse_rightHom _
    rw [map_mul, map_inv, X.rightHom_comm, e1, e2, mul_inv_cancel]
  have h2 : X.θ (s₂ l) * (s₁ (X.α l))⁻¹ ∈ ext₁.inl.range := by
    rw [ext₁.range_inl_eq_ker_rightHom]; exact h1
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩

/-- **The Levi action on the radical is compatible with the twist**, for arbitrary splittings. -/
theorem TwistEquiv.radicalInput (X : TwistEquiv ext₂ ext₁) (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (l : L)
    (r : RadicalLattice) :
    X.φ (splitRadicalInput s₂ l r) = splitRadicalInput s₁ (X.α l) (X.φ r) := by
  obtain ⟨c, hc⟩ := X.exists_lift s₁ s₂ l
  apply ext₁.inl_injective
  have h2 := congrArg X.θ (splitRadicalInput_commute s₂ l r)
  rw [map_mul, map_mul, X.inl_comm, X.inl_comm, hc] at h2
  have h1 := splitRadicalInput_commute s₁ (X.α l) (X.φ r)
  have hcomm : ext₁.inl (X.φ r) * ext₁.inl c = ext₁.inl c * ext₁.inl (X.φ r) := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [← mul_assoc, hcomm, mul_assoc, h1, ← mul_assoc] at h2
  exact (mul_left_cancel h2).symm


/-- **The radical acts trivially on `H¹(N, E)`**: a cocycle twisted by `ρ(inl c)` and a coboundary is cohomologous to the original (the radical lattice is abelian). -/
theorem h1_eq_of_twist (ext : GroupExtension RadicalLattice E₁ L) (ρ : Rep ℂ E₁)
    (d d' : groupCohomology.cocycles₁ (Rep.res ext.inl ρ)) (c : RadicalLattice) (w : ρ)
    (h : ∀ r, d' r = ρ.ρ (ext.inl c) (d r) + (ρ.ρ (ext.inl r) w - w)) :
    groupCohomology.H1π (Rep.res ext.inl ρ) d' = groupCohomology.H1π (Rep.res ext.inl ρ) d := by
  rw [groupCohomology.H1π_eq_iff]
  refine ⟨d c + w, ?_⟩
  funext r
  simp only [groupCohomology.d₀₁_hom_apply]
  have h1 := oneCocycle_mul (Rep.res ext.inl ρ) d c r
  have h2 := oneCocycle_mul (Rep.res ext.inl ρ) d r c
  rw [mul_comm c r] at h1
  have h3 : ρ.ρ (ext.inl c) (d r) + d c = ρ.ρ (ext.inl r) (d c) + d r := by
    exact h1.symm.trans h2
  change ρ.ρ (ext.inl r) (d c + w) - (d c + w) = d' r - d r
  rw [h r, map_add]
  linear_combination (norm := abel) -h3


section Transport

variable (X : TwistEquiv ext₂ ext₁) (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ ≃ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (X.θ g) v) = ρ₂.ρ g (T v))

include hT in
theorem radInter (r : RadicalLattice) :
    ((Rep.res ext₂.inl ρ₂).ρ r).comp T.toLinearMap =
      T.toLinearMap.comp ((Rep.res ext₁.inl ρ₁).ρ (X.φ.toMonoidHom r)) := by
  apply LinearMap.ext
  intro v
  change ρ₂.ρ (ext₂.inl r) (T v) = T (ρ₁.ρ (ext₁.inl (X.φ r)) v)
  rw [← X.inl_comm]
  exact (hT _ v).symm

/-- **The transport `H¹(N, ρ₁) → H¹(N, ρ₂)` along the radical map `φ` and the coefficient isomorphism `T`.** -/
def radXi : groupCohomology.H1 (Rep.res ext₁.inl ρ₁) →ₗ[ℂ] groupCohomology.H1 (Rep.res ext₂.inl ρ₂) :=
  oneCocyclePullbackH1 (Rep.res ext₁.inl ρ₁) (Rep.res ext₂.inl ρ₂) X.φ.toMonoidHom T.toLinearMap
    (radInter X ρ₁ ρ₂ T hT)

theorem radXi_π (c : groupCohomology.cocycles₁ (Rep.res ext₁.inl ρ₁)) :
    radXi X ρ₁ ρ₂ T hT (groupCohomology.H1π _ c) = groupCohomology.H1π _
      (oneCocyclePullback (Rep.res ext₁.inl ρ₁) (Rep.res ext₂.inl ρ₂) X.φ.toMonoidHom T.toLinearMap
        (radInter X ρ₁ ρ₂ T hT) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

/-- **`radXi` intertwines the Levi actions**, for arbitrary splittings of the two extensions. -/
theorem radXi_levi (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (l : L)
    (x : groupCohomology.H1 (Rep.res ext₁.inl ρ₁)) :
    radXi X ρ₁ ρ₂ T hT (splitRadicalH1Action s₁ ρ₁ (X.α l) x) =
      splitRadicalH1Action s₂ ρ₂ l (radXi X ρ₁ ρ₂ T hT x) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [splitRadicalH1Action_apply, radXi_π, radXi_π, splitRadicalH1Action_apply]
    obtain ⟨c₀, hc₀⟩ := X.exists_lift s₁ s₂ l
    have key : ∀ v : ρ₁, ρ₂.ρ (s₂ l) (T v) = ρ₂.ρ (ext₂.inl (X.φ.symm c₀)) (T (ρ₁.ρ (s₁ (X.α l)) v)) := by
      intro v
      rw [← hT (s₂ l) v, hc₀, map_mul, Module.End.mul_apply]
      have := hT (ext₂.inl (X.φ.symm c₀)) (ρ₁.ρ (s₁ (X.α l)) v)
      rw [X.inl_comm, MulEquiv.apply_symm_apply] at this
      exact this
    refine (h1_eq_of_twist ext₂ ρ₂ _ _ (X.φ.symm c₀) 0 (fun r => ?_)).symm
    simp only [oneCocyclePullback_apply, splitRadicalCocycleAction_apply, map_zero, sub_zero, add_zero,
      MulEquiv.coe_toMonoidHom]
    rw [X.radicalInput s₁ s₂ l r]
    exact key _

end Transport

end TernaryPeriodPolynomials.Argument.FrameInvariance
