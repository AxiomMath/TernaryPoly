module

public import TernaryPeriodPolynomials.Topology.DualityEquivariance.TwistedCovering

@[expose] public section


/-!
# `K`-equivariance of the duality, piece (ii)(b): naturality of the cap with the fundamental class

For the twisted pair `(PhiW k, PhiB k)` over `f̄_k` of `TwistedCovering`:

* `relPull k V` is the pullback of relative local cochains
  (`geometricRelativeCochains V ⟶ relCochTw k V`, a `kernel.map` of the pullbacks of the gluing and
  of its boundary; the restriction squares commute by `SingularCoverNaturality.localPullback_comp`);
* `Lspace k V` is the library's covariant map of local chains of the twisted covering to those of
  the bordification;
* `relCap_natural`: the relative cochain cap is natural, on chain-level representatives, for
  the pair of cover maps (the library's `cap_natural` plus the kernel/cokernel bookkeeping);
* `relativeFundamentalCap_twisted_natural`: on homology, using `fundamentalClass_fbar`,
  `relPull_* ≫ relativeFundamentalCapTw ≫ (Lspace)_* = relativeFundamentalCap V`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open CategoryTheory CategoryTheory.Limits TernaryPoly TernaryPoly.SingularLocalCompactCap.Algebra TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularCoverNaturality
  TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.SingularLocalCoefficient HomologicalComplex

variable (k : IntegralGL) (V : Rep.{0} ℚ principalSix)

/-- Pullback of local cochains of the gluing along `k`, from the untwisted to the twisted cover. -/
def phiWStar : localCochains wholeProjection wholeQuotientCovering V ⟶
    localCochains (pTw k) (twisted_whole_covering k) V :=
  localPullback (pTw k) wholeProjection (PhiW k) (fbarW k) (sqW k) (twisted_whole_covering k)
    wholeQuotientCovering (PhiW_equivariant k) V

/-- The same on the boundary covers. -/
def phiBStar : localCochains boundaryProjection boundaryQuotientCovering V ⟶
    localCochains (pbTw k) (twisted_boundary_covering k) V :=
  localPullback (pbTw k) boundaryProjection (PhiB k) (fbarBd k) (sqB k)
    (twisted_boundary_covering k) boundaryQuotientCovering (PhiB_equivariant k) V

/-- Boundary restriction for the twisted covering data. -/
abbrev restrTw : localCochains (pTw k) (twisted_whole_covering k) V ⟶
    localCochains (pbTw k) (twisted_boundary_covering k) V :=
  localPullback (pbTw k) (pTw k) (incTw k) boundaryBaseInclusion (sqTw k)
    (twisted_boundary_covering k) (twisted_whole_covering k) (incTw_equivariant k) V

theorem restr_comm :
    geometricBoundaryRestriction V ≫ phiBStar k V = phiWStar k V ≫ restrTw k V := by
  have e1 := localPullback_comp (pbTw k) boundaryProjection wholeProjection (PhiB k)
    boundaryInclusion (fbarBd k) boundaryBaseInclusion (sqB k) boundary_square
    (twisted_boundary_covering k) boundaryQuotientCovering wholeQuotientCovering
    (PhiB_equivariant k) boundaryInclusion_equivariant V
  have e2 := localPullback_comp (pbTw k) (pTw k) wholeProjection (incTw k) (PhiW k)
    boundaryBaseInclusion (fbarW k) (sqTw k) (sqW k) (twisted_boundary_covering k)
    (twisted_whole_covering k) wholeQuotientCovering (incTw_equivariant k) (PhiW_equivariant k) V
  exact e1.symm.trans e2


/-- The relative local cochains of the twisted covering data. -/
abbrev relCochTw := relativeLocalCochains (pbTw k) (pTw k) (incTw k) boundaryBaseInclusion (sqTw k)
  (twisted_boundary_covering k) (twisted_whole_covering k) (incTw_equivariant k) V

/-- The pullback of relative local cochains along the twisted pair. -/
def relPull : geometricRelativeCochains V ⟶ relCochTw k V :=
  kernel.map (geometricBoundaryRestriction V) (restrTw k V) (phiWStar k V) (phiBStar k V)
    (restr_comm k V)

theorem relPull_ι (n : ℕ) (x : (geometricRelativeCochains V).X n) :
    (kernel.ι (restrTw k V)).f n ((relPull k V).f n x) =
      (phiWStar k V).f n ((kernel.ι (geometricBoundaryRestriction V)).f n x) :=
  by
  have h : relPull k V ≫ kernel.ι (restrTw k V) =
      kernel.ι (geometricBoundaryRestriction V) ≫ phiWStar k V := by simp [relPull]
  exact congrArg (fun g : geometricRelativeCochains V ⟶ localCochains (pTw k)
    (twisted_whole_covering k) V => ConcreteCategory.hom (g.f n) x) h

/-- The map of relative scalar chains of the bordification pair induced by `f̄_k`. -/
def fbarScalar : relativeScalarChains boundaryBaseInclusion ⟶ relativeScalarChains boundaryBaseInclusion :=
  cokernel.map (scalarSpaceMap boundaryBaseInclusion) (scalarSpaceMap boundaryBaseInclusion)
    (scalarSpaceMap (fbarBd k)) (scalarSpaceMap (fbarW k))
    (by rw [← Functor.map_comp, ← Functor.map_comp, sqBase])


/-- The comparison chain map from twisted to untwisted local chains of the bordification. -/
abbrev Lspace : localChains (pTw k) (twisted_whole_covering k) V ⟶ localChains wholeProjection wholeQuotientCovering V :=
  localSpaceMap (PhiW k) (PhiW_equivariant k) V (pTw k) wholeProjection (twisted_whole_covering k)
    wholeQuotientCovering

/-- The relative cap for the twisted covering data. -/
abbrev relCapTw (a b : ℕ) := relativeCochainCap (pbTw k) (pTw k) (incTw k) boundaryBaseInclusion
  (sqTw k) (twisted_boundary_covering k) (twisted_whole_covering k) (incTw_equivariant k) V a b

/-- The relative cap for the untwisted covering data. -/
abbrev relCap (a b : ℕ) := relativeCochainCap boundaryProjection wholeProjection boundaryInclusion
  boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
  boundaryInclusion_equivariant V a b

/-- **Naturality of the relative cap for the twisted pair**, on chain-level representatives. -/
theorem relCap_natural (a b : ℕ) (x : (geometricRelativeCochains V).X a)
    (c : (relativeScalarChains boundaryBaseInclusion).X (a + b)) :
    (Lspace k V).f b (relCapTw k V a b ((relPull k V).f a x) c) =
      relCap V a b x ((fbarScalar k).f (a + b) c) := by
  obtain ⟨c0, rfl⟩ := RelativeAlgebra.projection_surjective (scalarSpaceMap boundaryBaseInclusion)
    (a + b) c
  rw [relCapTw, relCap, relativeCochainCap_projection, relPull_ι]
  have h1 : (fbarScalar k).f (a + b) ((cokernel.π (scalarSpaceMap boundaryBaseInclusion)).f (a + b) c0) =
      (cokernel.π (scalarSpaceMap boundaryBaseInclusion)).f (a + b)
        ((scalarSpaceMap (fbarW k)).f (a + b) c0) := by
    have h : cokernel.π (scalarSpaceMap boundaryBaseInclusion) ≫ fbarScalar k =
        scalarSpaceMap (fbarW k) ≫ cokernel.π (scalarSpaceMap boundaryBaseInclusion) := by
      unfold fbarScalar
      simp [cokernel.map]
    exact congrArg (fun g : scalarChains (TopCat.of BordifiedOrbit) ⟶
      relativeScalarChains boundaryBaseInclusion => ConcreteCategory.hom (g.f (a + b)) c0) h
  have h2 := relativeCochainCap_projection boundaryProjection wholeProjection boundaryInclusion
    boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
    boundaryInclusion_equivariant V a b x ((scalarSpaceMap (fbarW k)).f (a + b) c0)
  rw [h1]
  refine Eq.trans ?_ h2.symm
  exact cap_natural (pTw k) wholeProjection (PhiW k) (fbarW k) (sqW k) (twisted_whole_covering k)
    wholeQuotientCovering (PhiW_equivariant k) V a b
    ((kernel.ι (geometricBoundaryRestriction V)).f a x) c0


/-- Cap with the relative fundamental class for the twisted covering data. -/
def relativeFundamentalCapTw : (relCochTw k V).homology 2 ⟶ (localChains (pTw k) (twisted_whole_covering k) V).homology 3 :=
  ModuleCat.ofHom ((relativeCochainCapHomology (pbTw k) (pTw k) (incTw k) boundaryBaseInclusion
    (sqTw k) (twisted_boundary_covering k) (twisted_whole_covering k) (incTw_equivariant k) V 2 3).flip
      SymmetricSpaceRelativeFundamental.fundamentalClass)

/-- **The cap product with the relative fundamental class is natural for the twisted pair**: `f̄_k`
fixes the fundamental class (`fundamentalClass_fbar`), the cap is natural for the cover maps
(`cap_natural`), hence
`relativeFundamentalCap V = relPull_* ≫ relativeFundamentalCapTw ≫ (localSpaceMap (PhiW k))_*`. -/
theorem relativeFundamentalCap_twisted_natural :
    homologyMap (relPull k V) 2 ≫ relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3 =
      relativeFundamentalCap V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro xx
  obtain ⟨x, rfl⟩ := cochainClass_surjective (geometricRelativeCochains V) 2 xx
  obtain ⟨c, hc⟩ := chainClass_surjective (relativeScalarChains boundaryBaseInclusion) (2 + 3)
    SymmetricSpaceRelativeFundamental.fundamentalClass
  -- the pulled-back cochain cycle and the pushed-forward chain cycle
  let y : Homology.Cycles ((relCochTw k V).sc' (2 - 1) 2 (2 + 1)) :=
    ⟨(relPull k V).f 2 x.val, by
      change (relCochTw k V).d 2 (2 + 1) _ = 0
      erw [complexMap_d]
      have hx : (geometricRelativeCochains V).d 2 (2 + 1) x.val = 0 := x.property
      rw [hx, map_zero]⟩
  let d : Homology.Cycles ((relativeScalarChains boundaryBaseInclusion).sc' (2 + 3 + 1) (2 + 3)
      (2 + 3 - 1)) :=
    ⟨(fbarScalar k).f (2 + 3) c.val, by
      change (relativeScalarChains boundaryBaseInclusion).d (2 + 3) (2 + 3 - 1) _ = 0
      erw [complexMap_d]
      have hc' : (relativeScalarChains boundaryBaseInclusion).d (2 + 3) (2 + 3 - 1) c.val = 0 :=
        c.property
      rw [hc', map_zero]⟩
  have hfc : homologyMap (fbarScalar k) (2 + 3) SymmetricSpaceRelativeFundamental.fundamentalClass =
      SymmetricSpaceRelativeFundamental.fundamentalClass := fundamentalClass_fbar k
  have hd : homologyMap (fbarScalar k) (2 + 3) (Descent.chainClass _ (2 + 3) c) =
      Descent.chainClass _ (2 + 3) d := chainClass_natural (fbarScalar k) (2 + 3) c d rfl
  rw [hc] at hd
  rw [hfc] at hd
  have e1 : homologyMap (relPull k V) 2 (Descent.cochainClass _ 2 x) = Descent.cochainClass _ 2 y :=
    cochainClass_natural (relPull k V) 2 x y rfl
  change homologyMap (Lspace k V) 3 (relativeCochainCapHomology (pbTw k) (pTw k) (incTw k)
      boundaryBaseInclusion (sqTw k) (twisted_boundary_covering k) (twisted_whole_covering k)
      (incTw_equivariant k) V 2 3 (homologyMap (relPull k V) 2 (Descent.cochainClass _ 2 x))
      SymmetricSpaceRelativeFundamental.fundamentalClass) =
    relativeCochainCapHomology boundaryProjection wholeProjection boundaryInclusion
      boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
      boundaryInclusion_equivariant V 2 3 (Descent.cochainClass _ 2 x)
      SymmetricSpaceRelativeFundamental.fundamentalClass
  conv_lhs => rw [← hc]
  conv_rhs => rw [hd]
  rw [e1, relativeCochainCapHomology_representatives]
  have h2 := relativeCochainCapHomology_representatives boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 3 x d
  refine Eq.trans ?_ h2.symm
  exact chainClass_natural (Lspace k V) 3 _ _ (relCap_natural k V 2 3 x.val c.val).symm

theorem fbarScalar_eq_fbarRel : fbarScalar k = fbarRel k := rfl

end TernaryPeriodPolynomials.Argument.DualityEquivariance
