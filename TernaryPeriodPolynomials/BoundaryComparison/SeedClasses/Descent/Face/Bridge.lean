module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Iso
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.H1Dictionary
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FlagStabilizers

@[expose] public section


/-!
# Bridge: Mathlib group cohomology on `GroupExtension` versus the face library's crossed model

Paper: Lemma C.3 (`ar:lem:seed`),: `𝒞_R(E) ⊂ H¹(L_R, H¹(N_R, E))` is the subspace of classes whose restrictions at all
rational cusps of the binary Levi vanish, and it injects into degree-two face cohomology by
Hochschild--Serre.

The library has two models of this group.  `SeedC3S4c.MixedCuspidal` computes it in
Mathlib's `groupCohomology` on a `GroupExtension` (`splitRadicalH1Representation`,
`splitCohomologyEdge`, `cuspidalFamily`).  The face library `FacePairingFull.Face` computes it with
crossed homomorphisms on `SemidirectProduct Radical Levi action` (`CrossedH1`,
`leviCrossedH1Representation`, `radicalKernelMixedMap`, `FaceCuspidal`) and shows that its
`locallyInnerClasses` correspond to it.  This file proves that the two models agree, for an
arbitrary semidirect product `Radical ⋊ Levi` and an arbitrary representation of it:

* `crossedH1Equiv`: transport of crossed `H¹` along an intertwining module isomorphism;
* `leviMixedEquiv`: `CrossedH1 (leviCrossedH1Representation action ρ) ≃ₗ
  groupCohomology.H1 (splitRadicalH1Representation (inr_splitting action) (Rep.of ρ))`, built from
  `h1EquivCrossed` for the radical (`levi_intertwines` is the equivariance, the two Levi actions
  being literally the same formula) and for the Levi;
* `leviMixedEquiv_mem_cuspidalFamily`: a class of the crossed model restricts to zero on every
  member of a family of cusp subgroups iff its image lies in `cuspidalFamily`;
* `h2Equiv`: `InhomogeneousH2 ρ ≃ₗ groupCohomology.H2 (Rep.of ρ)`, natural for the radical
  restriction (`h2Equiv_radicalRestriction`);
* `leviMixedEquiv_radicalKernelMixedMap`: the face library's mixed class (`radicalKernelMixedMap`)
  corresponds under these isomorphisms to the library's Hochschild--Serre edge
  `splitCohomologyEdge` of the split extension, with sign `+1` (the two cocycle formulas
  `c(ℓ, ℓ⁻¹rℓ) - c(r, ℓ)` coincide);
* `faceCuspidal_map_eq`: for a face `F` presented as `Radical ⋊ Levi ≃* Γ_F`, `FaceCuspidal` is
  carried onto `cuspidalFamily` of the Levi parts of the stabilizers of the complete flags over `F`;
* `locallyInner_iff_edge_mem_cuspidalFamily`: a class of `H²(Γ_F, E)` is locally inner iff it has zero
  radical restriction and the Hochschild--Serre edge of its Mathlib class is in that
  `cuspidalFamily`.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section Transport

variable {G V₁ V₂ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
  [Module ℂ V₂] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (T : V₁ ≃ₗ[ℂ] V₂)
  (hT : ∀ g v, T (ρ₁ g v) = ρ₂ g (T v))

include hT

/-- A module isomorphism intertwining two representations carries crossed homomorphisms to
crossed homomorphisms. -/
def crossedCocyclesMap : crossedCocycles ρ₁ →ₗ[ℂ] crossedCocycles ρ₂ where
  toFun c := ⟨fun g => T (c.val g), fun a b => by
    change T (c.val (a * b)) = T (c.val a) + ρ₂ a (T (c.val b))
    rw [c.property a b, map_add, hT]⟩
  map_add' _ _ := Subtype.ext (funext fun g => map_add T _ _)
  map_smul' _ _ := Subtype.ext (funext fun g => map_smul T _ _)

theorem crossedCocyclesMap_boundary (v : V₁) :
    crossedCocyclesMap T hT (crossedBoundary ρ₁ v) = crossedBoundary ρ₂ (T v) := by
  apply Subtype.ext
  funext g
  change T (ρ₁ g v - v) = ρ₂ g (T v) - T v
  rw [map_sub, hT]

/-- The induced map on crossed `H¹`. -/
def crossedH1Map : CrossedH1 ρ₁ →ₗ[ℂ] CrossedH1 ρ₂ :=
  (crossedBoundaries ρ₁).mapQ (crossedBoundaries ρ₂) (crossedCocyclesMap T hT) (by
    rintro c ⟨v, rfl⟩
    exact ⟨T v, (crossedCocyclesMap_boundary T hT v).symm⟩)

theorem crossedH1Map_mk (c : crossedCocycles ρ₁) :
    crossedH1Map T hT ((crossedBoundaries ρ₁).mkQ c) =
      (crossedBoundaries ρ₂).mkQ (crossedCocyclesMap T hT c) := rfl

theorem hT_symm (g : G) (v : V₂) : T.symm (ρ₂ g v) = ρ₁ g (T.symm v) := by
  apply T.injective
  rw [LinearEquiv.apply_symm_apply, hT, LinearEquiv.apply_symm_apply]

/-- Transport of crossed `H¹` along an intertwining module isomorphism. -/
def crossedH1Equiv : CrossedH1 ρ₁ ≃ₗ[ℂ] CrossedH1 ρ₂ :=
  LinearEquiv.ofLinearMap (crossedH1Map T hT) (crossedH1Map T.symm (hT_symm T hT))
    (by
      apply LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | H c =>
        refine congrArg (crossedBoundaries ρ₂).mkQ (Subtype.ext (funext fun g => ?_))
        exact T.apply_symm_apply _)
    (by
      apply LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | H c =>
        refine congrArg (crossedBoundaries ρ₁).mkQ (Subtype.ext (funext fun g => ?_))
        exact T.symm_apply_apply _)

theorem crossedH1Equiv_mk (c : crossedCocycles ρ₁) :
    crossedH1Equiv T hT ((crossedBoundaries ρ₁).mkQ c) =
      (crossedBoundaries ρ₂).mkQ (crossedCocyclesMap T hT c) := rfl

theorem exists_coboundary_iff {S : Type} (j : S → G) (f : S → V₁) :
    (∃ u : V₁, ∀ γ : S, f γ = ρ₁ (j γ) u - u) ↔
      ∃ u : V₂, ∀ γ : S, T (f γ) = ρ₂ (j γ) u - u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨T u, fun γ => by rw [hu γ, map_sub, hT]⟩
  · rintro ⟨u, hu⟩
    refine ⟨T.symm u, fun γ => T.injective ?_⟩
    rw [hu γ, map_sub, hT, LinearEquiv.apply_symm_apply]

end Transport

section Semidirect

variable {Radical Levi V : Type} [Group Radical] [Group Levi] [AddCommGroup V] [Module ℂ V]
  (action : Levi →* MulAut Radical) (ρ : Representation ℂ (SemidirectProduct Radical Levi action) V)

theorem inrSplitting_conjAct (l : Levi) (r : Radical) :
    (SemidirectProduct.inr_splitting action).conjAct l r = action l r := by
  apply (SemidirectProduct.toGroupExtension action).inl_injective
  have := (SemidirectProduct.toGroupExtension action).inl_conjAct_comm
    (e := (SemidirectProduct.inr_splitting action) l) (n := r)
  change SemidirectProduct.inl (((SemidirectProduct.toGroupExtension action).conjAct
    (SemidirectProduct.inr l)) r) = _ at this
  show SemidirectProduct.inl (((SemidirectProduct.toGroupExtension action).conjAct
    (SemidirectProduct.inr l)) r) = SemidirectProduct.inl (action l r)
  rw [this]
  rw [SemidirectProduct.inl_aut (φ := action) l r]
  have h : (SemidirectProduct.inr_splitting action) l = SemidirectProduct.inr l := rfl
  rw [h, map_inv]
  rfl

theorem splitRadicalInput_semidirect (l : Levi) (r : Radical) :
    splitRadicalInput (SemidirectProduct.inr_splitting action) l r = action l⁻¹ r := by
  change (SemidirectProduct.inr_splitting action).conjAct l⁻¹ r = _
  exact inrSplitting_conjAct action l⁻¹ r

/-- The radical coefficient representation `E|_N`, as the restriction along the extension's `inl`. -/
abbrev radRep : Rep ℂ Radical :=
  Rep.res (SemidirectProduct.toGroupExtension action).inl (Rep.of ρ)

theorem levi_intertwines (l : Levi) (x : CrossedH1 (ρ.comp SemidirectProduct.inl)) :
    h1EquivCrossed (radRep action ρ) (leviCrossedH1Representation action ρ l x) =
      (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)).ρ l
        (h1EquivCrossed (radRep action ρ) x) := by
  obtain ⟨c, rfl⟩ := (crossedBoundaries (ρ.comp SemidirectProduct.inl)).mkQ_surjective x
  have hL := h1EquivCrossed_mk (radRep action ρ) (leviCrossedAction action ρ l c)
  have hR := h1EquivCrossed_mk (radRep action ρ) c
  have hcoc : cocycleOfCrossed (radRep action ρ) (leviCrossedAction action ρ l c) =
      splitRadicalCocycleAction (SemidirectProduct.inr_splitting action) (Rep.of ρ) l
        (cocycleOfCrossed (radRep action ρ) c) := by
    apply groupCohomology.cocycles₁_ext
    intro r
    rw [splitRadicalCocycleAction_apply, splitRadicalInput_semidirect]
    rfl
  rw [leviCrossedH1Representation_mk]
  exact hL.trans ((congrArg (groupCohomology.H1π (radRep action ρ)) hcoc).trans
    ((splitRadicalH1Action_apply (SemidirectProduct.inr_splitting action) (Rep.of ρ) l _).symm.trans
      (congrArg _ hR.symm)))

/-- **The Hochschild--Serre coordinate of the Levi module.** The crossed model
`H¹(Levi, H¹(Radical, E))` of the face library is isomorphic to Mathlib's `H¹` of the Levi
representation `splitRadicalH1Representation` of the split extension. -/
def leviMixedEquiv : CrossedH1 (leviCrossedH1Representation action ρ) ≃ₗ[ℂ]
    groupCohomology.H1 (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)) :=
  (crossedH1Equiv (h1EquivCrossed (radRep action ρ)) (levi_intertwines action ρ)).trans
    (h1EquivCrossed (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)))

theorem leviMixedEquiv_mk (c : crossedCocycles (leviCrossedH1Representation action ρ)) :
    leviMixedEquiv action ρ ((crossedBoundaries (leviCrossedH1Representation action ρ)).mkQ c) =
      groupCohomology.H1π (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ))
        (cocycleOfCrossed _ (crossedCocyclesMap (h1EquivCrossed (radRep action ρ))
          (levi_intertwines action ρ) c)) := rfl

/-- Membership in the cuspidal subspace of the crossed model, in terms of a representative. -/
theorem mem_iInf_crossedPullback_iff {ι : Type} (B : ι → Subgroup Levi)
    (c : crossedCocycles (leviCrossedH1Representation action ρ)) :
    (crossedBoundaries (leviCrossedH1Representation action ρ)).mkQ c ∈
        (⨅ i, LinearMap.ker (crossedPullbackH1 (B i).subtype (leviCrossedH1Representation action ρ))) ↔
      ∀ i, ∃ u : CrossedH1 (ρ.comp SemidirectProduct.inl),
        ∀ γ : B i, c.val (γ : Levi) = leviCrossedH1Representation action ρ (γ : Levi) u - u := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, crossedPullbackH1_mk]
  refine forall_congr' fun i => ?_
  change Submodule.Quotient.mk _ = _ ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, fun γ => congrArg (fun y : crossedCocycles _ => y.val γ) hu.symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, Subtype.ext (funext fun γ => (hu γ).symm)⟩

/-- **The face library's mixed cuspidal condition is the literal one.** A class of the crossed model
restricts to zero on every cusp subgroup `B i` iff its Hochschild--Serre coordinate lies in
`cuspidalFamily B`. -/
theorem leviMixedEquiv_mem_cuspidalFamily {ι : Type} (B : ι → Subgroup Levi)
    (x : CrossedH1 (leviCrossedH1Representation action ρ)) :
    leviMixedEquiv action ρ x ∈ cuspidalFamily B
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)) ↔
      x ∈ ⨅ i, LinearMap.ker (crossedPullbackH1 (B i).subtype (leviCrossedH1Representation action ρ)) := by
  obtain ⟨c, rfl⟩ := (crossedBoundaries (leviCrossedH1Representation action ρ)).mkQ_surjective x
  rw [leviMixedEquiv_mk, mem_cuspidalFamily_π, mem_iInf_crossedPullback_iff]
  refine forall_congr' fun i => ?_
  exact (exists_coboundary_iff (h1EquivCrossed (radRep action ρ)) (levi_intertwines action ρ)
    (fun γ : B i => (γ : Levi)) (fun γ => c.val (γ : Levi))).symm

end Semidirect

section H2Dictionary

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- A two-cocycle of the face library (a curried function) is a Mathlib two-cocycle. -/
def twoCycleToMathlib : inhomogeneousTwoCycles ρ →ₗ[ℂ] groupCohomology.cocycles₂ (Rep.of ρ) where
  toFun c := ⟨fun p => c.val p.1 p.2, (groupCohomology.mem_cocycles₂_iff _).mpr fun a b d => by
    have h := c.property a b d
    change c.val (a * b) d + c.val a b = ρ a (c.val b d) + c.val a (b * d)
    linear_combination (norm := abel) -h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A Mathlib two-cocycle is a two-cocycle of the face library. -/
def twoCycleOfMathlib : groupCohomology.cocycles₂ (Rep.of ρ) →ₗ[ℂ] inhomogeneousTwoCycles ρ where
  toFun c := ⟨fun a b => c.val (a, b), fun a b d => by
    have h := (groupCohomology.mem_cocycles₂_iff _).mp c.property a b d
    change ρ a (c.val (b, d)) - c.val (a * b, d) + c.val (a, b * d) - c.val (a, b) = 0
    change c.val (a * b, d) + c.val (a, b) = ρ a (c.val (b, d)) + c.val (a, b * d) at h
    linear_combination (norm := abel) -h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem twoCycleToMathlib_boundary (f : G → V) :
    ⇑(twoCycleToMathlib ρ (inhomogeneousBoundaryMap ρ f)) ∈
      groupCohomology.coboundaries₂ (Rep.of ρ) :=
  ⟨f, rfl⟩

/-- Mathlib's `H²` as a quotient of the face library's inhomogeneous cycles. -/
def h2Dict : InhomogeneousH2 ρ →ₗ[ℂ] groupCohomology.H2 (Rep.of ρ) :=
  (inhomogeneousBoundaries ρ).liftQ
    ((groupCohomology.H2π (Rep.of ρ)).hom ∘ₗ twoCycleToMathlib ρ) (by
      rintro _ ⟨f, rfl⟩
      rw [LinearMap.mem_ker]
      change groupCohomology.H2π (Rep.of ρ) (twoCycleToMathlib ρ (inhomogeneousBoundaryMap ρ f)) = 0
      rw [groupCohomology.H2π_eq_zero_iff]
      exact twoCycleToMathlib_boundary ρ f)

theorem h2Dict_mk (c : inhomogeneousTwoCycles ρ) :
    h2Dict ρ ((inhomogeneousBoundaries ρ).mkQ c) =
      groupCohomology.H2π (Rep.of ρ) (twoCycleToMathlib ρ c) := rfl

theorem h2Dict_bijective : Function.Bijective (h2Dict ρ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨c, rfl⟩ := (inhomogeneousBoundaries ρ).mkQ_surjective m
    have h : groupCohomology.H2π (Rep.of ρ) (twoCycleToMathlib ρ c) = 0 := hm
    rw [groupCohomology.H2π_eq_zero_iff] at h
    obtain ⟨f, hf⟩ := h
    refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, ?_⟩
    apply Subtype.ext
    funext a b
    exact congrFun hf (a, b)
  · intro x
    induction x using groupCohomology.H2_induction_on with
    | h z => exact ⟨(inhomogeneousBoundaries ρ).mkQ (twoCycleOfMathlib ρ z), rfl⟩

/-- **Mathlib's `H²` is the face library's inhomogeneous `H²`.** -/
def h2Equiv : InhomogeneousH2 ρ ≃ₗ[ℂ] groupCohomology.H2 (Rep.of ρ) :=
  LinearEquiv.ofBijective (h2Dict ρ) (h2Dict_bijective ρ)

theorem h2Equiv_apply_mk (c : inhomogeneousTwoCycles ρ) :
    h2Equiv ρ ((inhomogeneousBoundaries ρ).mkQ c) =
      groupCohomology.H2π (Rep.of ρ) (twoCycleToMathlib ρ c) := rfl

section Restriction

variable {Radical Levi : Type} [Group Radical] [Group Levi]
  (action : Levi →* MulAut Radical)
  (ρ' : Representation ℂ (SemidirectProduct Radical Levi action) V)

/-- The Mathlib radical restriction `H²(Γ, E) → H²(N, E)` is the face library's one. -/
theorem h2Equiv_radicalRestriction (x : InhomogeneousH2 ρ') :
    twoCohomologyRestriction (SemidirectProduct.toGroupExtension action).inl (Rep.of ρ')
        (h2Equiv ρ' x) =
      h2Equiv (ρ'.comp SemidirectProduct.inl) (radicalRestrictionH2 action ρ' x) := by
  obtain ⟨c, rfl⟩ := (inhomogeneousBoundaries ρ').mkQ_surjective x
  rw [h2Equiv_apply_mk]
  have e1 := twoCohomologyRestriction_apply (SemidirectProduct.toGroupExtension action).inl
    (Rep.of ρ') (twoCycleToMathlib ρ' c)
  have e2 : radicalRestrictionH2 action ρ' ((inhomogeneousBoundaries ρ').mkQ c) =
      (inhomogeneousBoundaries (ρ'.comp SemidirectProduct.inl)).mkQ
        (inhomogeneousPullbackCycles SemidirectProduct.inl ρ' c) := rfl
  rw [e2]
  exact e1.trans (congrArg _ (groupCohomology.cocycles₂_ext fun a b => rfl))

theorem h2Equiv_mem_ker (x : (radicalRestrictionH2 action ρ').ker) :
    h2Equiv ρ' x.1 ∈
      (twoCohomologyRestriction (SemidirectProduct.toGroupExtension action).inl (Rep.of ρ')).ker := by
  rw [LinearMap.mem_ker, h2Equiv_radicalRestriction, LinearMap.mem_ker.mp x.2, map_zero]
  rfl

/-- **The mixed class of the face library is the Hochschild--Serre edge.** For a class with zero
radical restriction, the Hochschild--Serre coordinate (`leviMixedEquiv`) of its mixed class
(`radicalKernelMixedMap`) is the library edge `splitCohomologyEdge` of the corresponding
Mathlib class. -/
theorem leviMixedEquiv_radicalKernelMixedMap (x : (radicalRestrictionH2 action ρ').ker) :
    leviMixedEquiv action ρ' (radicalKernelMixedMap action ρ' x) =
      splitCohomologyEdge (SemidirectProduct.inr_splitting action) (Rep.of ρ')
        ⟨h2Equiv ρ' x.1, h2Equiv_mem_ker action ρ' x⟩ := by
  obtain ⟨y, rfl⟩ := (radicalZeroH2ToKernel_bijective action ρ').2 x
  obtain ⟨cyc, rfl⟩ := (radicalZeroBoundaries action ρ').mkQ_surjective y
  rw [radicalKernelMixedMap_representative, leviMixedEquiv_mk]
  let z : relativeTwoCocycles (SemidirectProduct.toGroupExtension action).inl (Rep.of ρ') :=
    ⟨twoCycleToMathlib ρ' cyc.val, fun a b => cyc.property a b⟩
  have hx : (⟨h2Equiv ρ' (radicalZeroH2ToKernel action ρ'
      ((radicalZeroBoundaries action ρ').mkQ cyc)).1, h2Equiv_mem_ker action ρ' _⟩ :
      (twoCohomologyRestriction (SemidirectProduct.toGroupExtension action).inl
        (Rep.of ρ')).ker) =
      relativeTwoCocycleClass (SemidirectProduct.toGroupExtension action).inl (Rep.of ρ') z :=
    Subtype.ext rfl
  rw [hx, splitCohomologyEdge_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro l
  change groupCohomology.H1π (radRep action ρ') _ = groupCohomology.H1π (radRep action ρ') _
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro r
  change cyc.val.val (SemidirectProduct.inr l) (SemidirectProduct.inl (action l⁻¹ r)) -
      cyc.val.val (SemidirectProduct.inl r) (SemidirectProduct.inr l) =
    z.val (SemidirectProduct.inr_splitting action l, (SemidirectProduct.toGroupExtension action).inl
      (splitRadicalInput (SemidirectProduct.inr_splitting action) l r)) -
    z.val ((SemidirectProduct.toGroupExtension action).inl r, SemidirectProduct.inr_splitting action l)
  rw [splitRadicalInput_semidirect]
  rfl

end Restriction

end H2Dictionary

section Face

open GeneralEisenstein Matrix

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- Generic form of `faceCuspidal_map_eq`. -/
theorem map_leviMixedEquiv_eq_cuspidalFamily {Radical Levi V : Type} [Group Radical] [Group Levi]
    [AddCommGroup V] [Module ℂ V] (action : Levi →* MulAut Radical)
    (ρ : Representation ℂ (SemidirectProduct Radical Levi action) V) {ι : Type}
    (B : ι → Subgroup Levi)
    (S : Submodule ℂ (CrossedH1 (leviCrossedH1Representation action ρ)))
    (hS : S = ⨅ i, LinearMap.ker
      (crossedPullbackH1 (B i).subtype (leviCrossedH1Representation action ρ))) :
    Submodule.map (leviMixedEquiv action ρ).toLinearMap S =
      cuspidalFamily B
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)) := by
  subst hS
  ext y
  obtain ⟨x, rfl⟩ := (leviMixedEquiv action ρ).surjective y
  rw [leviMixedEquiv_mem_cuspidalFamily]
  constructor
  · rintro ⟨x', hx', h⟩
    have := (leviMixedEquiv action ρ).injective h
    subst this
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The face library's `FaceCuspidal` is the literal mixed cuspidal group.** Under the
Hochschild--Serre coordinate `leviMixedEquiv` of the Levi module, `FaceCuspidal` (classes of
`H¹(Levi, H¹(Radical, E))` whose pullback to the Levi part of the stabilizer of every complete
flag over `F` vanishes) is `cuspidalFamily` of Mathlib's `H¹` for the family of those subgroups. -/
theorem faceCuspidal_map_eq :
    Submodule.map (leviMixedEquiv action
        (FacePairingFull.Face.faceRep action degree character F ι)).toLinearMap
      (FacePairingFull.Face.FaceCuspidal action degree character F ι) =
      cuspidalFamily
        (fun e : {e : Edges // endpoint side e = F} =>
          FacePairingFull.Face.faceCusp action F ι e.1)
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
          (Rep.of (FacePairingFull.Face.faceRep action degree character F ι))) :=
  map_leviMixedEquiv_eq_cuspidalFamily action
    (FacePairingFull.Face.faceRep action degree character F ι)
    (fun e : {e : Edges // endpoint side e = F} => FacePairingFull.Face.faceCusp action F ι e.1)
    (FacePairingFull.Face.FaceCuspidal action degree character F ι) rfl

/-- Generic form of `locallyInner_iff_edge_mem_cuspidalFamily`. -/
theorem edge_mem_cuspidalFamily_iff_pullback {Radical Levi V : Type} [Group Radical] [Group Levi]
    [AddCommGroup V] [Module ℂ V] (action : Levi →* MulAut Radical)
    (ρ : Representation ℂ (SemidirectProduct Radical Levi action) V) {ι : Type}
    (B : ι → Subgroup Levi) (x : (radicalRestrictionH2 action ρ).ker) :
    splitCohomologyEdge (SemidirectProduct.inr_splitting action) (Rep.of ρ)
        ⟨h2Equiv ρ x.1, h2Equiv_mem_ker action ρ x⟩ ∈
      cuspidalFamily B
        (splitRadicalH1Representation (SemidirectProduct.inr_splitting action) (Rep.of ρ)) ↔
      ∀ i, crossedPullbackH1 (B i).subtype (leviCrossedH1Representation action ρ)
        (radicalKernelMixedMap action ρ x) = 0 := by
  rw [← leviMixedEquiv_radicalKernelMixedMap, leviMixedEquiv_mem_cuspidalFamily]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

/-- **Locally inner classes are the classes whose Hochschild--Serre edge is cuspidal.** A class of
`H²(Γ_F, E)` is locally inner (restricts to zero on the stabilizer of every complete flag over `F`)
iff it has zero restriction to the radical and the library's Hochschild--Serre edge
(`splitCohomologyEdge`) of its Mathlib class lies in `cuspidalFamily` of the Levi parts of those
stabilizers. -/
theorem locallyInner_iff_edge_mem_cuspidalFamily
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)
    (coordinate : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character side F ↔
      ∃ hr : FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate ∈
          (radicalRestrictionH2 action
            (FacePairingFull.Face.faceRep action degree character F ι)).ker,
        splitCohomologyEdge (SemidirectProduct.inr_splitting action)
            (Rep.of (FacePairingFull.Face.faceRep action degree character F ι))
            ⟨h2Equiv (FacePairingFull.Face.faceRep action degree character F ι)
              (FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate),
              h2Equiv_mem_ker action _
                ⟨FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate, hr⟩⟩ ∈
          cuspidalFamily
            (fun e : {e : Edges // endpoint side e = F} =>
              FacePairingFull.Face.faceCusp action F ι e.1)
            (splitRadicalH1Representation (SemidirectProduct.inr_splitting action)
              (Rep.of (FacePairingFull.Face.faceRep action degree character F ι))) :=
  (FacePairingFull.Face.face_locallyInner_iff_uniform action degree character F ι hfix ψ
    injective coordinate).trans
    (exists_congr fun hr =>
      ((edge_mem_cuspidalFamily_iff_pullback action
        (FacePairingFull.Face.faceRep action degree character F ι)
        (fun e : {e : Edges // endpoint side e = F} => FacePairingFull.Face.faceCusp action F ι e.1)
        ⟨FacePairingFull.Face.faceH2Equiv action degree character F ι coordinate, hr⟩).trans
          Subtype.forall).symm)

end Face

end TernaryPeriodPolynomials.Argument.SeedC3S4c
