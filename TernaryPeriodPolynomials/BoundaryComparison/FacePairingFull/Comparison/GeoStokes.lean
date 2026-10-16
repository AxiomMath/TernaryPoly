module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.GeoPairing
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnecting
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Duality
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapComparison

@[expose] public section


/-!
# Geometric Stokes and the Lagrangian property of the restriction image on `∂M`

The geometric (Submission-side) counterpart of the paper's Stokes lemma and of the Poincaré-Lefschetz perfectness
argument for the face pairing.  `M̄` is the compact bordification of the arithmetic quotient, `∂M` its boundary,
`geoPairing` (`GeoPairing.lean`) the Poincaré-duality pairing of the closed oriented boundary
`H²(∂M; V*) × H²(∂M; V) → ℚ`, and `res` the restriction `H²(M̄; ·) → H²(∂M; ·)`.  All statements are for an arbitrary
rational representation `V` of `Γ(6)` (in particular the coefficient systems `E_n` of the geometric side) with its full
contragredient, and an orientation `o` of `∂M` whose ordinary fundamental class is the boundary fundamental class
(`boundaryOrientation`, `GeoEval.boundaryOrientation_class`).

* `boundaryOrdinaryCap_eq_absolute`: the ordinary cap on `∂M` is the absolute cap with the connecting image of the
  relative fundamental class of `(M̄, ∂M)`.
* `inclusion_cap_restriction`: `i_*([∂M] ∩ res b') = 0` (the library's relative cap/connecting square).
* `geoPairing_restriction` (**geometric Stokes**): `⟨res a', res b'⟩_{∂M} = 0` for `a' ∈ H²(M̄; V*)`, `b' ∈ H²(M̄; V)`.
* `relativeCap_three_injective`, `exists_restriction_of_inclusion_eq_zero`: Lefschetz duality for `(M̄, ∂M)` in the
  degrees used (relative cap iso `relativeCapMap_isIso`).
* `geoPairing_annihilator_iff` (**Lagrangian property**): `α ∈ H²(∂M; V*)` annihilates `res H²(M̄; V)` iff
  `α ∈ res H²(M̄; V*)`.  Uses universal coefficients (`SingularLocalDuality`) and linear algebra over `ℚ`.

Scope: these are statements on the manifold.  The identification of the cochain model's `facePairing` with `geoPairing`
is NOT asserted here.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.RationalLocalOrientation
  TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SymmetricSpaceBordifiedPrincipalSix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable (V : Rep.{0} ℚ principalSix)

/-- The ordinary `H²(∂M)`-to-`H₂(∂M)` cap is the absolute cap against the connecting image of the relative class. -/
theorem boundaryOrdinaryCap_eq_absolute (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass)
    (x : (localBoundaryCochains V).homology 2) :
    (boundaryOrdinaryCap V o 2 2 rfl).hom x =
      absolute boundaryProjection boundaryQuotientCovering V 2 2 x
        SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass := by
  change CompactOrdinaryCap.ordinaryCapMap boundaryProjection V 2 boundaryEuclidean o 2 2 rfl x =
    absolute boundaryProjection boundaryQuotientCovering V 2 2 x
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass
  have h := RelativeCapConnecting.ordinaryCap_eq_absolute boundaryProjection V 2 boundaryEuclidean o
    2 2 rfl x
  simpa only [SingularLocalCompactCap.homologyDegreeChange,eqToHom_refl,ModuleCat.id_apply,ho] using h

/-- The cap of a restricted class with the boundary fundamental class dies in `H₂` of the bordification. -/
theorem inclusion_cap_restriction (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass)
    (b' : (localCochains wholeProjection wholeQuotientCovering V).homology 2) :
    homologyMap (boundaryInclusionMap V) 2
      ((boundaryOrdinaryCap V o 2 2 rfl).hom
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b')) = 0 := by
  let : Mono (scalarSpaceMap boundaryBaseInclusion) :=
    (inferInstance : Mono (RationalRelativeSingular.inclusion (boundary principalSix)))
  let : Epi (SingularCoverNaturality.localPullback boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V) :=
      (inferInstance : Epi (geometricBoundaryRestriction V))
  have hker : (RelativeCochainSequence.connecting (geometricBoundaryRestriction V) 2).hom
      ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b') = 0 := by
    have hm : (RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b' ∈
        LinearMap.range (RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom :=
      ⟨b', rfl⟩
    rw [RelativeCochainSequence.range_restriction_eq_kernel_connecting] at hm
    exact hm
  rw [boundaryOrdinaryCap_eq_absolute V o ho]
  have h := RelativeCapConnecting.geometric_connecting_cap boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 2
    ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b')
    SymmetricSpaceRelativeFundamental.fundamentalClass
  refine h.trans ?_
  unfold geometricBoundaryRestriction at hker
  erw [hker, map_zero, LinearMap.zero_apply]
  rfl

/-- **Geometric Stokes on `∂M`.**  The restriction of a class of `H²(M̄; V*)` pairs to zero, under the
Poincaré-duality pairing of the oriented boundary, with the restriction of every class of `H²(M̄; V)`. -/
theorem geoPairing_restriction (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass)
    (a' : (localCochains wholeProjection wholeQuotientCovering
      (SingularLocalDuality.dualRepresentation V)).homology 2)
    (b' : (localCochains wholeProjection wholeQuotientCovering V).homology 2) :
    geoPairing V o
      ((RelativeCochainSequence.restrictionMap
        (geometricBoundaryRestriction (SingularLocalDuality.dualRepresentation V)) 2).hom a')
      ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b') = 0 := by
  have : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
  have hn := SingularLocalDuality.homologyPairing_natural boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 a'
    ((boundaryOrdinaryCap V o 2 2 rfl).hom
      ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b'))
  have hz := inclusion_cap_restriction V o ho b'
  change SingularLocalDuality.homologyPairing boundaryProjection boundaryQuotientCovering V 2
      ((RelativeCochainSequence.restrictionMap
        (geometricBoundaryRestriction (SingularLocalDuality.dualRepresentation V)) 2).hom a')
      ((boundaryOrdinaryCap V o 2 2 rfl).hom
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b')) = 0
  have hz' : (homologyMap (localSpaceMap boundaryInclusion boundaryInclusion_equivariant V
      boundaryProjection wholeProjection boundaryQuotientCovering wholeQuotientCovering) 2)
      ((boundaryOrdinaryCap V o 2 2 rfl).hom
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b')) = 0 := hz
  exact hn.trans (by rw [hz']; exact map_zero _)

/-- **Lefschetz duality for the actual pair `(M̄, ∂M)`, in the degrees used here**: cap with the relative
fundamental class is injective on `H³` of the geometric relative cochains. -/
theorem relativeCap_three_injective (x : (geometricRelativeCochains V).homology 3)
    (hx : relativeCochainCapHomology boundaryProjection wholeProjection boundaryInclusion
      boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
      boundaryInclusion_equivariant V 3 2 x SymmetricSpaceRelativeFundamental.fundamentalClass = 0) :
    x = 0 := by
  have h := geometricSupport_cap_homology V 3 2 x SymmetricSpaceRelativeFundamental.fundamentalClass
  have hm : (TernaryPoly.SymmetricSpaceRelativeCap.relativeCapMap V 3 2 rfl).hom
      ((homologyMap (geometricSupportIso V).hom 3).hom x) = 0 := h.trans hx
  have hi := TernaryPoly.SymmetricSpaceRelativeCap.relativeCapMap_isIso V 3 2 rfl
  have h2 : (homologyMap (geometricSupportIso V).hom 3).hom x = 0 := by
    have := (asIso (TernaryPoly.SymmetricSpaceRelativeCap.relativeCapMap V 3 2 rfl)).toLinearEquiv.injective
      (hm.trans (map_zero _).symm)
    exact this
  exact ((asIso (homologyMap (geometricSupportIso V).hom 3)).toLinearEquiv.injective
    (h2.trans (map_zero _).symm))

/-- **Lefschetz exactness on the boundary**: a class of `H₂(∂M; V)` that dies in `H₂(M̄; V)` is the cap with the
boundary fundamental class of a restriction of a class of `H²(M̄; V)`. -/
theorem exists_restriction_of_inclusion_eq_zero (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass)
    (y : (boundaryLocalChains V).homology 2) (hy : homologyMap (boundaryInclusionMap V) 2 y = 0) :
    ∃ b' : (localCochains wholeProjection wholeQuotientCovering V).homology 2,
      (boundaryOrdinaryCap V o 2 2 rfl).hom
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b') = y := by
  let : Mono (scalarSpaceMap boundaryBaseInclusion) :=
    (inferInstance : Mono (RationalRelativeSingular.inclusion (boundary principalSix)))
  let : Epi (SingularCoverNaturality.localPullback boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V) :=
      (inferInstance : Epi (geometricBoundaryRestriction V))
  let γ := (boundaryOrdinaryCapIso V o 2 2 rfl).toLinearEquiv.symm y
  have hγ : (boundaryOrdinaryCap V o 2 2 rfl).hom γ = y :=
    (boundaryOrdinaryCapIso V o 2 2 rfl).toLinearEquiv.apply_symm_apply y
  have h := RelativeCapConnecting.geometric_connecting_cap boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 2 γ
    SymmetricSpaceRelativeFundamental.fundamentalClass
  have hl : (homologyMap (localSpaceMap boundaryInclusion boundaryInclusion_equivariant V
      boundaryProjection wholeProjection boundaryQuotientCovering wholeQuotientCovering) 2)
      (absolute boundaryProjection boundaryQuotientCovering V 2 2 γ
        ((RelativeChainSequence.connecting (scalarSpaceMap boundaryBaseInclusion) (2+2)).hom
          SymmetricSpaceRelativeFundamental.fundamentalClass)) = 0 := by
    have e := boundaryOrdinaryCap_eq_absolute V o ho γ
    have e2 : absolute boundaryProjection boundaryQuotientCovering V 2 2 γ
        SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass = y := e.symm.trans hγ
    exact (congrArg _ e2).trans hy
  have hz := hl.symm.trans h
  have hc : (RelativeCochainSequence.connecting (geometricBoundaryRestriction V) 2).hom γ = 0 := by
    apply relativeCap_three_injective V
    exact hz.symm
  have hm : γ ∈ LinearMap.range
      (RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom := by
    rw [RelativeCochainSequence.range_restriction_eq_kernel_connecting]
    exact hc
  rcases hm with ⟨b', hb'⟩
  exact ⟨b', hb'.symm ▸ hγ⟩

/-- **The restriction image is its own annihilator (geometric Lagrangian property).**  A class `α` of
`H²(∂M; V*)` pairs to zero, under the Poincaré-duality pairing of the oriented boundary, with the restriction of every
class of `H²(M̄; V)` exactly when it is the restriction of a class of `H²(M̄; V*)`.  The "if" is geometric Stokes
(`geoPairing_restriction`); the "only if" is Lefschetz duality for `(M̄, ∂M)` with universal coefficients. -/
theorem geoPairing_annihilator_iff (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass)
    (α : (localBoundaryCochains (SingularLocalDuality.dualRepresentation V)).homology 2) :
    (∀ b' : (localCochains wholeProjection wholeQuotientCovering V).homology 2,
      geoPairing V o α
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b') = 0) ↔
    α ∈ LinearMap.range (RelativeCochainSequence.restrictionMap
      (geometricBoundaryRestriction (SingularLocalDuality.dualRepresentation V)) 2).hom := by
  constructor
  · intro hα
    have : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
    have := wholeQuotientCovering.isCancelSMul
    set ι := (homologyMap (boundaryInclusionMap V) 2).hom with hι
    set ψ := SingularLocalDuality.homologyPairing boundaryProjection boundaryQuotientCovering V 2 α with hψ
    have hker : LinearMap.ker ι ≤ LinearMap.ker ψ := by
      intro y hy
      obtain ⟨b', hb'⟩ := exists_restriction_of_inclusion_eq_zero V o ho y hy
      have h1 := hα b'
      change ψ ((boundaryOrdinaryCap V o 2 2 rfl).hom
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b')) = 0 at h1
      rw [hb'] at h1
      exact h1
    obtain ⟨χ, hχ⟩ := LinearMap.exists_extend
      ((LinearMap.ker ι).liftQ ψ hker ∘ₗ ι.quotKerEquivRange.symm.toLinearMap)
    have hχι : ∀ x, χ (ι x) = ψ x := by
      intro x
      have := congrArg (fun g => g ⟨ι x, LinearMap.mem_range_self ι x⟩) hχ
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      have e := LinearMap.quotKerEquivRange_symm_apply_image ι x (LinearMap.mem_range_self ι x)
      rw [this]
      change (LinearMap.ker ι).liftQ ψ hker (ι.quotKerEquivRange.symm ⟨ι x, _⟩) = _
      rw [e]
      rfl
    let U := SingularLocalDuality.universalCoefficientIso wholeProjection wholeQuotientCovering V 2
    refine ⟨U.toLinearEquiv.symm χ, ?_⟩
    let U0 := SingularLocalDuality.universalCoefficientIso boundaryProjection boundaryQuotientCovering V 2
    apply U0.toLinearEquiv.injective
    apply LinearMap.ext
    intro x
    have hn := SingularLocalDuality.homologyPairing_natural boundaryProjection wholeProjection
      boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
      wholeQuotientCovering boundaryInclusion_equivariant V 2 (U.toLinearEquiv.symm χ) x
    have hU : SingularLocalDuality.homologyPairing wholeProjection wholeQuotientCovering V 2
        (U.toLinearEquiv.symm χ) = χ := U.toLinearEquiv.apply_symm_apply χ
    change SingularLocalDuality.homologyPairing boundaryProjection boundaryQuotientCovering V 2
        ((RelativeCochainSequence.restrictionMap
          (geometricBoundaryRestriction (SingularLocalDuality.dualRepresentation V)) 2).hom
            (U.toLinearEquiv.symm χ)) x = ψ x
    refine hn.trans ?_
    rw [hU]
    exact hχι x
  · rintro ⟨a'', rfl⟩ b'
    exact geoPairing_restriction V o ho a'' b'

/-- Geometric Stokes for the orientation of the boundary fundamental class. -/
theorem geoPairingBoundary_restriction
    (a' : (localCochains wholeProjection wholeQuotientCovering
      (SingularLocalDuality.dualRepresentation V)).homology 2)
    (b' : (localCochains wholeProjection wholeQuotientCovering V).homology 2) :
    geoPairingBoundary V
      ((RelativeCochainSequence.restrictionMap
        (geometricBoundaryRestriction (SingularLocalDuality.dualRepresentation V)) 2).hom a')
      ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b') = 0 :=
  geoPairing_restriction V _ boundaryOrientation_class.symm a' b'

/-- The Lagrangian property for the orientation of the boundary fundamental class. -/
theorem geoPairingBoundary_annihilator_iff
    (α : (localBoundaryCochains (SingularLocalDuality.dualRepresentation V)).homology 2) :
    (∀ b' : (localCochains wholeProjection wholeQuotientCovering V).homology 2,
      geoPairingBoundary V α
        ((RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) 2).hom b') = 0) ↔
    α ∈ LinearMap.range (RelativeCochainSequence.restrictionMap
      (geometricBoundaryRestriction (SingularLocalDuality.dualRepresentation V)) 2).hom :=
  geoPairing_annihilator_iff V _ boundaryOrientation_class.symm α

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
