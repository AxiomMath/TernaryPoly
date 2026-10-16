module

public import TernaryPeriodPolynomials.Topology.DualityEquivariance.CapNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonCap

@[expose] public section


/-!
# `K`-equivariance of the duality, piece (ii)(b) in the Hom model

The library's identification of relative Hom cohomology of the upstairs pair with geometric relative
cohomology, `relativeHomGeometricIso = relativeHomKernelIso ≪≫ boundaryGeometricIso`, is natural
for the twisted pair: the twisted analogues (`relativeHomKernelIsoTw`, `boundaryGeometricIsoTw`)
are built from the same cokernel/kernel and `cochainIso` constructions, the pulled-back cochains
(`relHomPull`, pullback along `relChainMap`, the map of relative chains induced by `chainPhiW`,
`chainPhiB`) commute with them (`relHomGeom_natural`, from the library's `cochainIso_pullback`), and
together with `relativeFundamentalCap_twisted_natural` this gives the naturality of the whole
cap isomorphism `S2⁻¹ = relativeHomCapIso` (`relativeHomCap_twisted_natural`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open CategoryTheory CategoryTheory.Limits TernaryPoly TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularCoverNaturality
  TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.SingularLocalCoefficient
  HomologicalComplex TernaryPoly.EquivariantSingularResolution
  TernaryPoly.EquivariantSingularCohomology TernaryPoly.EquivariantSingularSmall
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology

variable (k : IntegralGL) (V : Rep.{0} ℚ principalSix)

/-- Equivariant singular chains of the twisted gluing. -/
abbrev ambientChainsTw := equivariantChains principalSix (TopCat.of (GluedTw k))

/-- Equivariant singular chains of the twisted boundary cover. -/
abbrev boundaryChainsTw := equivariantChains principalSix (TopCat.of (BoundaryTw k))

/-- The twisted analogue of `upstairsBoundaryChainMap`. -/
abbrev upstairsBoundaryChainMapTw : boundaryChainsTw k ⟶ ambientChainsTw k :=
  chainMap (incTw k) (incTw_equivariant k)

/-- The twisted analogue of `upstairsRelativeChains`. -/
abbrev upstairsRelativeChainsTw := cokernel (upstairsBoundaryChainMapTw k)

/-- Action of `k` on equivariant singular chains, from the twisted gluing to the gluing. -/
abbrev chainPhiW : ambientChainsTw k ⟶ equivariantChains principalSix (TopCat.of Glued) :=
  chainMap (PhiW k) (PhiW_equivariant k)

/-- The same on the boundary covers. -/
abbrev chainPhiB : boundaryChainsTw k ⟶ boundaryChains := chainMap (PhiB k) (PhiB_equivariant k)

theorem chainMap_congr {E E' : TopCat.{0}} [MulAction principalSix E] [ContinuousConstSMul principalSix E]
    [MulAction principalSix E'] [ContinuousConstSMul principalSix E'] {F F' : E ⟶ E'}
    (h : F = F') (hF : ∀ (g : principalSix) (x : E), F (g • x) = g • F x)
    (hF' : ∀ (g : principalSix) (x : E), F' (g • x) = g • F' x) :
    chainMap F hF = chainMap F' hF' := by
  subst h; rfl

theorem chain_square :
    upstairsBoundaryChainMapTw k ≫ chainPhiW k = chainPhiB k ≫ upstairsBoundaryChainMap :=
  (chainMap_comp (incTw k) (PhiW k) (incTw_equivariant k) (PhiW_equivariant k)).symm.trans
    ((chainMap_congr (sqInc k) _ _).trans
      (chainMap_comp (PhiB k) boundaryInclusion (PhiB_equivariant k) boundaryInclusion_equivariant))

/-- The induced map of relative representation chains. -/
def relChainMap : upstairsRelativeChainsTw k ⟶ upstairsRelativeChains :=
  cokernel.map _ _ (chainPhiB k) (chainPhiW k) (chain_square k)

/-- Pullback of relative Hom cochains along the twisted pair. -/
def relHomPull : homCochains upstairsRelativeChains V ⟶ homCochains (upstairsRelativeChainsTw k) V :=
  homPullback (relChainMap k) V

/-- Boundary restriction of Hom cochains of the twisted covering data. -/
abbrev boundaryRestrictionTw : cochains principalSix (TopCat.of (GluedTw k)) V ⟶
    cochains principalSix (TopCat.of (BoundaryTw k)) V :=
  cochainPullback (incTw k) (incTw_equivariant k) V

/-- Relative Hom cochains of the twisted covering data. -/
abbrev relativeCochainsTw := kernel (boundaryRestrictionTw k V)

theorem upstairsHomPullbackTw_eq : homPullback (upstairsBoundaryChainMapTw k) V = boundaryRestrictionTw k V := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- The twisted analogue of `relativeHomKernelIso`. -/
def relativeHomKernelIsoTw : homCochains (upstairsRelativeChainsTw k) V ≅ relativeCochainsTw k V :=
  HomCokernelKernel.cochainIso (upstairsBoundaryChainMapTw k) V ≪≫
    kernelIsoOfEq (upstairsHomPullbackTw_eq k V)

/-- The twisted analogue of `boundaryGeometricIso`. -/
def boundaryGeometricIsoTw : relativeCochainsTw k V ≅ relCochTw k V :=
  kernel.mapIso (boundaryRestrictionTw k V) (restrTw k V)
    (cochainIso (pTw k) (twisted_whole_covering k) V)
    (cochainIso (pbTw k) (twisted_boundary_covering k) V)
    (cochainIso_pullback (pbTw k) (pTw k) (incTw k) boundaryBaseInclusion (sqTw k)
      (twisted_boundary_covering k) (twisted_whole_covering k) (incTw_equivariant k) V)

/-- The twisted analogue of `relativeHomGeometricIso`. -/
def relativeHomGeometricIsoTw : homCochains (upstairsRelativeChainsTw k) V ≅ relCochTw k V :=
  relativeHomKernelIsoTw k V ≪≫ boundaryGeometricIsoTw k V


theorem boundaryGeometricIsoTw_ι :
    (boundaryGeometricIsoTw k V).hom ≫ kernel.ι (restrTw k V) =
      kernel.ι (boundaryRestrictionTw k V) ≫ (cochainIso (pTw k) (twisted_whole_covering k) V).hom := by
  unfold boundaryGeometricIsoTw
  erw [kernel.lift_ι]

theorem relHomGeomTw_ι :
    (relativeHomGeometricIsoTw k V).hom ≫ kernel.ι (restrTw k V) =
      homPullback (cokernel.π (upstairsBoundaryChainMapTw k)) V ≫
        (cochainIso (pTw k) (twisted_whole_covering k) V).hom := by
  unfold relativeHomGeometricIsoTw
  rw [Iso.trans_hom, Category.assoc, boundaryGeometricIsoTw_ι]
  unfold relativeHomKernelIsoTw
  rw [Iso.trans_hom, Category.assoc, kernelIsoOfEq_hom_comp_ι_assoc,
    ← Category.assoc, HomCokernelKernel.cochainIso_hom_inclusion]

theorem relHomGeom_ι :
    (relativeHomGeometricIso V).hom ≫ kernel.ι (geometricBoundaryRestriction V) =
      homPullback (cokernel.π upstairsBoundaryChainMap) V ≫
        (cochainIso wholeProjection wholeQuotientCovering V).hom := by
  unfold relativeHomGeometricIso
  rw [Iso.trans_hom, Category.assoc, CompactInteriorRelativeBoundary.boundaryGeometricIso_inclusion]
  unfold relativeHomKernelIso
  rw [Iso.trans_hom, Category.assoc, kernelIsoOfEq_hom_comp_ι_assoc,
    ← Category.assoc, HomCokernelKernel.cochainIso_hom_inclusion]


theorem relChainMap_π :
    cokernel.π (upstairsBoundaryChainMapTw k) ≫ relChainMap k = chainPhiW k ≫ cokernel.π upstairsBoundaryChainMap := by
  unfold relChainMap
  simp [cokernel.map]

/-- **Naturality of the Hom-model/geometric comparison for the twisted pair.** -/
theorem relHomGeom_natural :
    relHomPull k V ≫ (relativeHomGeometricIsoTw k V).hom =
      (relativeHomGeometricIso V).hom ≫ relPull k V := by
  apply (cancel_mono (kernel.ι (restrTw k V))).mp
  have hι : relPull k V ≫ kernel.ι (restrTw k V) =
      kernel.ι (geometricBoundaryRestriction V) ≫ phiWStar k V := by simp [relPull]
  have hc : cochainPullback (PhiW k) (PhiW_equivariant k) V ≫
      (cochainIso (pTw k) (twisted_whole_covering k) V).hom =
      (cochainIso wholeProjection wholeQuotientCovering V).hom ≫ phiWStar k V :=
    cochainIso_pullback (pTw k) wholeProjection (PhiW k) (fbarW k) (sqW k)
      (twisted_whole_covering k) wholeQuotientCovering (PhiW_equivariant k) V
  have hp : relHomPull k V ≫ homPullback (cokernel.π (upstairsBoundaryChainMapTw k)) V =
      homPullback (cokernel.π upstairsBoundaryChainMap) V ≫ cochainPullback (PhiW k) (PhiW_equivariant k) V := by
    unfold relHomPull
    rw [← homPullback_comp, relChainMap_π, homPullback_comp]
    rfl
  rw [Category.assoc, Category.assoc, relHomGeomTw_ι, hι, ← Category.assoc ((relativeHomGeometricIso V).hom),
    relHomGeom_ι, Category.assoc, ← hc, ← Category.assoc, ← Category.assoc, hp]


/-- The cap-product isomorphism `S2⁻¹` in the Hom model, for the twisted covering data. -/
def relativeHomCapTw : (homCochains (upstairsRelativeChainsTw k) V).homology 2 ⟶
    (localChains (pTw k) (twisted_whole_covering k) V).homology 3 :=
  homologyMap (relativeHomGeometricIsoTw k V).hom 2 ≫ relativeFundamentalCapTw k V

/-- **Piece (ii) of the `K`-equivariance of `Θ = S3 ∘ S2⁻¹ ∘ S1`.** The cap isomorphism
`relativeHomCapIso` (relative Hom cohomology of the upstairs pair → bordified `H₃`) is natural for the
twisted pair over `f̄_k`:
`(relHomPull)_* ≫ relativeHomCapTw ≫ (Lspace)_* = (relativeHomCapIso V).hom`. -/
theorem relativeHomCap_twisted_natural :
    homologyMap (relHomPull k V) 2 ≫ relativeHomCapTw k V ≫ homologyMap (Lspace k V) 3 =
      (OrdinaryTopBoundaryComparison.relativeHomCapIso V).hom := by
  have h1 := relativeFundamentalCap_twisted_natural k V
  have h2 : homologyMap (relHomPull k V) 2 ≫ homologyMap (relativeHomGeometricIsoTw k V).hom 2 =
      homologyMap (relativeHomGeometricIso V).hom 2 ≫ homologyMap (relPull k V) 2 := by
    rw [← homologyMap_comp, ← homologyMap_comp, relHomGeom_natural]
  unfold relativeHomCapTw
  have e1 : homologyMap (relHomPull k V) 2 ≫ (homologyMap (relativeHomGeometricIsoTw k V).hom 2 ≫
        relativeFundamentalCapTw k V) ≫ homologyMap (Lspace k V) 3 =
      (homologyMap (relHomPull k V) 2 ≫ homologyMap (relativeHomGeometricIsoTw k V).hom 2) ≫
        relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3 := by simp only [Category.assoc]
  have e2 : (homologyMap (relHomPull k V) 2 ≫ homologyMap (relativeHomGeometricIsoTw k V).hom 2) ≫
        relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3 =
      (homologyMap (relativeHomGeometricIso V).hom 2 ≫ homologyMap (relPull k V) 2) ≫
        relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3 := by rw [h2]
  have e3 : (homologyMap (relativeHomGeometricIso V).hom 2 ≫ homologyMap (relPull k V) 2) ≫
        relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3 =
      homologyMap (relativeHomGeometricIso V).hom 2 ≫ (homologyMap (relPull k V) 2 ≫
        relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3) := by simp only [Category.assoc]
  have e4 : homologyMap (relativeHomGeometricIso V).hom 2 ≫ (homologyMap (relPull k V) 2 ≫
        relativeFundamentalCapTw k V ≫ homologyMap (Lspace k V) 3) =
      homologyMap (relativeHomGeometricIso V).hom 2 ≫ relativeFundamentalCap V :=
    congrArg (fun m => homologyMap (relativeHomGeometricIso V).hom 2 ≫ m) h1
  exact e1.trans (e2.trans (e3.trans (e4.trans
    (OrdinaryTopBoundaryComparison.relativeHomCapIso_hom V).symm)))

end TernaryPeriodPolynomials.Argument.DualityEquivariance
