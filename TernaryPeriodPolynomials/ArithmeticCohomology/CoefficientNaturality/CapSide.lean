module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonCap
public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsComplexNaturality
public import TernaryPeriodPolynomials.Topology.GroupSingularCoefficientComparisonNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coefficients
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.EvalSide

@[expose] public section


/-!
# Coefficient naturality of the relative cap isomorphism

For a morphism `φ : V ⟶ W` of rational representations of the principal-six group, the Hom
cochains of the arithmetic relative chains, the geometric relative cochains of the boundary pair, and
the bordified local chains are all functorial in the coefficients by literal postcomposition (on
fiber coefficients).  The cap product against the relative fundamental class commutes with these
maps (`relativeFundamentalCap_natural`, from `relativeCochainCap_natural`, which in turn comes from
`cap_vertexMap` and the general descent statement `descentHomology_natural`), the identification of
Hom cochains with geometric relative cochains does too (`relativeHomGeometricIso_natural`), and so
does the composite `relativeHomCapIso` (`relativeHomCapIso_natural`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CoefficientNaturality

open TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCompactCap.Algebra
  TernaryPoly.RationalHomologyCoefficients

/-- A cap-type pairing that is compatible with chain maps in the cochain and local-chain variables
induces compatible maps on the descended homology pairings. -/
theorem descentHomology_natural {C C' : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L L' : ChainComplex (ModuleCat.{0} ℚ) ℕ} (fC : C ⟶ C') (fL : L ⟶ L')
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b) (hβ : Descent.Leibniz C K L β)
    (β' : ∀ a b, C'.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L'.X b) (hβ' : Descent.Leibniz C' K L' β')
    (h : ∀ a b x c, (fL.f b).hom (β a b x c) = β' a b ((fC.f a).hom x) c)
    (a b : ℕ) (x : C.homology a) (c : K.homology (a+b)) :
    homologyMap fL b (Descent.homology C K L β hβ a b x c) =
      Descent.homology C' K L' β' hβ' a b (homologyMap fC a x) c := by
  obtain ⟨x, rfl⟩ := cochainClass_surjective C a x
  obtain ⟨c, rfl⟩ := chainClass_surjective K (a+b) c
  rw [cochainClass_natural fC a x (mapComplexCycle fC (a-1) a (a+1) x) rfl,
    Descent.homology_representatives, Descent.homology_representatives]
  exact chainClass_natural fL b _ _ (h a b x.val c.val).symm

section Pairing

open TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology
  TernaryPoly.SingularCoverNaturality SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) {V W : Rep.{0} ℚ G} (φ : V ⟶ W)

omit [ContinuousConstSMul G E'] [IsCancelSMul G E'] in
/-- Cap with a fixed chain is natural in the coefficient morphism. -/
theorem cap_vertexMap (a b : ℕ) (ψ : VertexCochain p' hp' V a)
    (c : singularChainGroup ℚ B' (a+b)) :
    TernaryPoly.SingularLocalCap.cap p' hp' W a b (vertexMap p' hp' φ a ψ) c =
      vertexCoefficientMap p' hp' φ b (TernaryPoly.SingularLocalCap.cap p' hp' V a b ψ c) := by
  have h : TernaryPoly.SingularLocalCap.cap p' hp' W a b (vertexMap p' hp' φ a ψ) =
      (vertexCoefficientMap p' hp' φ b).comp (TernaryPoly.SingularLocalCap.cap p' hp' V a b ψ) := by
    apply TernaryPoly.SingularLocalCap.scalarChain_ext
    intro σ
    simp only [LinearMap.comp_apply, TernaryPoly.SingularLocalCap.cap_generator,
      TernaryPoly.SingularLocalCap.capSimplex_apply]
    erw [vertexCoefficientMap_single]
    rfl
  exact congrArg (fun m => m c) h

omit [IsCancelSMul G E] [IsCancelSMul G E'] in
/-- Coefficient maps commute with the geometric cochain pullback along a map of covers. -/
theorem localPullback_localCochainMap :
    localCochainMap p' hp' φ ≫ localPullback p p' F f hsquare hp hp' hF W =
      localPullback p p' F f hsquare hp hp' hF V ≫ localCochainMap p hp φ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- The coefficient map on the geometric relative cochain complexes. -/
def relativeLocalCochainMap : relativeLocalCochains p p' F f hsquare hp hp' hF V ⟶
    relativeLocalCochains p p' F f hsquare hp hp' hF W :=
  kernel.map (localPullback p p' F f hsquare hp hp' hF V) (localPullback p p' F f hsquare hp hp' hF W)
    (localCochainMap p' hp' φ) (localCochainMap p hp φ)
    (localPullback_localCochainMap p p' F f hsquare hp hp' hF φ)

omit [IsCancelSMul G E] [IsCancelSMul G E'] in
theorem relativeLocalCochainMap_ι :
    relativeLocalCochainMap p p' F f hsquare hp hp' hF φ ≫
        kernel.ι (localPullback p p' F f hsquare hp hp' hF W) =
      kernel.ι (localPullback p p' F f hsquare hp hp' hF V) ≫ localCochainMap p' hp' φ := by
  simp [relativeLocalCochainMap]

/-- The relative cap is natural in the coefficient morphism. -/
theorem relativeCochainCap_natural (a b : ℕ)
    (x : (relativeLocalCochains p p' F f hsquare hp hp' hF V).X a)
    (c : (relativeScalarChains f).X (a+b)) :
    ((localCoefficientMap p' hp' φ).f b).hom
        (TernaryPoly.SingularLocalCap.relativeCochainCap p p' F f hsquare hp hp' hF V a b x c) =
      TernaryPoly.SingularLocalCap.relativeCochainCap p p' F f hsquare hp hp' hF W a b
        ((relativeLocalCochainMap p p' F f hsquare hp hp' hF φ).f a x) c := by
  obtain ⟨c, rfl⟩ := TernaryPoly.SingularLocalCap.RelativeAlgebra.projection_surjective
    (scalarSpaceMap f) (a+b) c
  have h1 : (kernel.ι (localPullback p p' F f hsquare hp hp' hF W)).f a
      ((relativeLocalCochainMap p p' F f hsquare hp hp' hF φ).f a x) =
      vertexMap p' hp' φ a ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a x) :=
    congrArg (fun m => m.hom x)
      (HomologicalComplex.congr_hom (relativeLocalCochainMap_ι p p' F f hsquare hp hp' hF φ) a)
  rw [TernaryPoly.SingularLocalCap.relativeCochainCap_projection,
    TernaryPoly.SingularLocalCap.relativeCochainCap_projection, h1]
  exact (LinearMap.congr_fun (localCoefficientMap_f p' hp' φ b) _).trans
    (cap_vertexMap p' hp' φ a b _ c).symm

end Pairing

section Boundary

open TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.CompactInteriorRelativeBoundary
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceRationalGluing

variable {V W : Rep.{0} ℚ principalSix} (φ : V ⟶ W)

/-- The coefficient map on the actual geometric relative cochains of the boundary pair. -/
def geometricRelativeCochainMap : geometricRelativeCochains V ⟶ geometricRelativeCochains W :=
  relativeLocalCochainMap boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
    boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant φ

/-- The fixed-fundamental-class cap on relative cohomology is natural in the coefficients. -/
theorem relativeFundamentalCap_natural :
    relativeFundamentalCap V ≫ homologyMap (localCoefficientMap bordifiedProjection
      bordifiedProjection_quotientCovering φ) 3 =
      homologyMap (geometricRelativeCochainMap φ) 2 ≫ relativeFundamentalCap W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := descentHomology_natural (geometricRelativeCochainMap φ)
    (localCoefficientMap bordifiedProjection bordifiedProjection_quotientCovering φ)
    (TernaryPoly.SingularLocalCap.relativeCochainCap boundaryProjection wholeProjection
      boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
      wholeQuotientCovering boundaryInclusion_equivariant V)
    (TernaryPoly.SingularLocalCap.relativeCochainCap_leibniz boundaryProjection wholeProjection
      boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
      wholeQuotientCovering boundaryInclusion_equivariant V)
    (TernaryPoly.SingularLocalCap.relativeCochainCap boundaryProjection wholeProjection
      boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
      wholeQuotientCovering boundaryInclusion_equivariant W)
    (TernaryPoly.SingularLocalCap.relativeCochainCap_leibniz boundaryProjection wholeProjection
      boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
      wholeQuotientCovering boundaryInclusion_equivariant W)
    (fun a b x c => relativeCochainCap_natural boundaryProjection wholeProjection boundaryInclusion
      boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
      boundaryInclusion_equivariant φ a b x c) 2 3 x
    TernaryPoly.SymmetricSpaceRelativeFundamental.fundamentalClass
  exact h

/-- The comparison of Hom cochains with the geometric relative cochains includes as precomposition
with the quotient map, followed by the geometric cochain isomorphism. -/
theorem relativeHomGeometricIso_ι :
    (relativeHomGeometricIso V).hom ≫ kernel.ι (geometricBoundaryRestriction V) =
      homPullback (cokernel.π upstairsBoundaryChainMap) V ≫
        (TernaryPoly.SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering V).hom := by
  unfold relativeHomGeometricIso relativeHomKernelIso
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, boundaryGeometricIso_inclusion,
    ← Category.assoc (kernelIsoOfEq _).hom, kernelIsoOfEq_hom_comp_ι,
    ← Category.assoc, TernaryPoly.HomCokernelKernel.cochainIso_hom_inclusion]

/-- The identification of Hom cochains with the geometric relative cochains is natural in the
coefficients. -/
theorem relativeHomGeometricIso_natural :
    (relativeHomGeometricIso V).hom ≫ geometricRelativeCochainMap φ =
      coefHomPost upstairsRelativeChains φ ≫ (relativeHomGeometricIso W).hom := by
  have hι : geometricRelativeCochainMap φ ≫ kernel.ι (geometricBoundaryRestriction W) =
      kernel.ι (geometricBoundaryRestriction V) ≫
        TernaryPoly.SingularLocalCoefficient.localCochainMap wholeProjection
          wholeQuotientCovering φ :=
    relativeLocalCochainMap_ι boundaryProjection wholeProjection boundaryInclusion
      boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
      boundaryInclusion_equivariant φ
  have hpost : homPullback (cokernel.π upstairsBoundaryChainMap) V ≫
      TernaryPoly.EquivariantSingularCohomology.cochainMap principalSix (TopCat.of Glued) φ =
      coefHomPost (cokernel upstairsBoundaryChainMap) φ ≫
        homPullback (cokernel.π upstairsBoundaryChainMap) W := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact Category.assoc (obj := Rep.{0} ℚ principalSix) _ _ _
  rw [← cancel_mono (kernel.ι (geometricBoundaryRestriction W))]
  simp only [Category.assoc]
  calc (relativeHomGeometricIso V).hom ≫ geometricRelativeCochainMap φ ≫
        kernel.ι (geometricBoundaryRestriction W)
      = (relativeHomGeometricIso V).hom ≫ kernel.ι (geometricBoundaryRestriction V) ≫
        TernaryPoly.SingularLocalCoefficient.localCochainMap wholeProjection wholeQuotientCovering φ := by
        rw [hι]
    _ = (homPullback (cokernel.π upstairsBoundaryChainMap) V ≫
          (TernaryPoly.SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering V).hom) ≫
        TernaryPoly.SingularLocalCoefficient.localCochainMap wholeProjection wholeQuotientCovering φ := by
        rw [← Category.assoc, relativeHomGeometricIso_ι]
    _ = homPullback (cokernel.π upstairsBoundaryChainMap) V ≫
          TernaryPoly.EquivariantSingularCohomology.cochainMap principalSix (TopCat.of Glued) φ ≫
          (TernaryPoly.SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering W).hom := by
        rw [Category.assoc,
          ← TernaryPoly.SingularLocalCoefficient.cochainIso_natural wholeProjection
            wholeQuotientCovering φ]
    _ = (coefHomPost (cokernel upstairsBoundaryChainMap) φ ≫
          homPullback (cokernel.π upstairsBoundaryChainMap) W) ≫
          (TernaryPoly.SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering W).hom := by
        rw [← Category.assoc, hpost]
    _ = coefHomPost upstairsRelativeChains φ ≫ (relativeHomGeometricIso W).hom ≫
        kernel.ι (geometricBoundaryRestriction W) := by
        rw [relativeHomGeometricIso_ι, Category.assoc]

/-- The actual cap isomorphism from relative Hom cohomology to bordified `H₃` is natural in the
coefficients. -/
theorem relativeHomCapIso_natural :
    (relativeHomCapIso V).hom ≫ homologyMap (localCoefficientMap bordifiedProjection
      bordifiedProjection_quotientCovering φ) 3 =
      homologyMap (coefHomPost upstairsRelativeChains φ) 2 ≫ (relativeHomCapIso W).hom := by
  rw [relativeHomCapIso_hom, relativeHomCapIso_hom, Category.assoc, relativeFundamentalCap_natural,
    ← Category.assoc, ← Category.assoc, ← homologyMap_comp, ← homologyMap_comp,
    relativeHomGeometricIso_natural]

end Boundary

end TernaryPeriodPolynomials.Argument.CoefficientNaturality

