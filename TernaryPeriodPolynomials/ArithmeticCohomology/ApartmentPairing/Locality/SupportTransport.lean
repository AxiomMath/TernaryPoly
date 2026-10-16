module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SpaceCover
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.HomEvaluation
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityHomeomorphSupportCap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapOpen
public import TernaryPeriodPolynomials.Topology.Singular.CoverPullbackComposition
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapComparison

@[expose] public section


/-!
# Lemma 3.3, G3: transport of a compactly supported class to the orbit bordification

For a compact `K` of the interior base `↥(boundary principalSix)ᶜ` and a class `y` in the degree-two
cohomology of the cochains of `pS` supported in `K`, `exists_transport` produces compatible cocycle
representatives upstairs and downstairs.  The cocycle `φh` of the geometric local cochains of the compact
bordification (supported in the image `Kb` of `K`) and the cocycle `φ` of the symmetric space satisfy:

* `φ` represents `y`;
* on every singular two-simplex `τ` of the symmetric space, the geometric coefficient of `φ` equals the
  geometric coefficient of `φh` at the simplex `projection upstairs 2 τ`
  (`vertexToFunction_transport` is the underlying cochain-level naturality);
* the relative cap of the class of `φh` equals the image, under the chain map `spaceChainMap` of the
  equivariant covering square `(upstairs, interior base ⊆ orbit bordification)`, of the compact cap of `y`
  (`capTransport` is the cap naturality for the cover homeomorphism `spaceCoverHomeomorph` between `pS`
  and the restriction of the bordified cover to the interior).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.SymmetricSpaceBordifiedCohomology
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SymmetricSpaceBordifiedContractible TernaryPoly.SymmetricSpaceRelativeCap
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SingularLocalHomology
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCoefficient
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceRelativeFundamental

/-- The symmetric space as the preimage of the interior complement in the bordification. -/
def spaceTotal : Space ≃ₜ ↥(wholeProjection ⁻¹' (boundary principalSix)ᶜ) :=
  embedding_isOpenEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (projection_preimage_arithmeticInterior.symm.trans
      preimage_interior_eq.symm))

/-- The equivariant cover homeomorphism between the covering `pS` of the interior base by the symmetric
space and the restriction of the bordified cover to the interior; the base map is the identity. -/
def spaceCoverHomeomorph : CoverHomeomorph (G := principalSix) pS interiorProjection where
  total := spaceTotal
  base := Homeomorph.refl _
  square := by ext x; rfl
  equivariant g x := Subtype.ext (embedding_equivariant principalSix g x)

/-- Composition of the geometric local-chain maps of equivariant covering squares. -/
theorem localSpaceMap_comp {G : Type} [Group G] {E E' E'' B B' B'' : TopCat.{0}}
    [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
    [MulAction G E''] [ContinuousConstSMul G E''] [IsCancelSMul G E] [IsCancelSMul G E']
    [IsCancelSMul G E'']
    (F : E ⟶ E') (H : E' ⟶ E'') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x) (V : Rep.{0} ℚ G)
    (p : E ⟶ B) (p' : E' ⟶ B') (p'' : E'' ⟶ B'') (hp : IsQuotientCoveringMap p G)
    (hp' : IsQuotientCoveringMap p' G) (hp'' : IsQuotientCoveringMap p'' G) :
    localSpaceMap F hF V p p' hp hp' ≫ localSpaceMap H hH V p' p'' hp' hp'' =
      localSpaceMap (F ≫ H) (fun g x => by change H (F (g • x)) = g • H (F x); rw [hF, hH])
        V p p'' hp hp'' := by
  unfold localSpaceMap coinvariantSpaceMap
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc]
  rw [SingularCoverNaturality.chainMap_comp F H hF hH]


/-- The chain map of geometric local chains induced by the equivariant covering square
`(upstairs, interior base ⊆ bordified orbit space)`. -/
def spaceChainMap (W : Rep.{0} ℚ principalSix) :
    localChains pS pS_isQuotientCovering W ⟶
      localChains wholeProjection wholeQuotientCovering W :=
  localSpaceMap upstairs upstairs_equivariant W pS wholeProjection pS_isQuotientCovering
    wholeQuotientCovering

/-- The geometric local-chain map only depends on the underlying equivariant map. -/
theorem localSpaceMap_congr {G : Type} [Group G] {E E' B B' : TopCat.{0}}
    [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
    [IsCancelSMul G E] [IsCancelSMul G E']
    (F F' : E ⟶ E') (h : F = F') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hF' : ∀ (g : G) (x : E), F' (g • x) = g • F' x) (V : Rep.{0} ℚ G)
    (p : E ⟶ B) (p' : E' ⟶ B') (hp : IsQuotientCoveringMap p G)
    (hp' : IsQuotientCoveringMap p' G) :
    localSpaceMap F hF V p p' hp hp' = localSpaceMap F' hF' V p p' hp hp' := by
  subst h
  rfl

/-- The cover homeomorphism followed by the inclusion of the interior preimage is `upstairs`. -/
theorem upstairs_factor : (TopCat.isoOfHomeo spaceCoverHomeomorph.total).hom ≫
    SphereOddDegree.sInclusion (wholeProjection ⁻¹' (boundary principalSix)ᶜ) = upstairs := by
  ext x
  rfl

/-- The chain map of the covering square factors through the cover homeomorphism. -/
theorem spaceChainMap_eq (W : Rep.{0} ℚ principalSix) :
    spaceChainMap W = coveringChainMap spaceCoverHomeomorph W ≫
      openLocalChainMap wholeProjection W (boundary principalSix)ᶜ := by
  have h := localSpaceMap_comp (TopCat.isoOfHomeo spaceCoverHomeomorph.total).hom
    (SphereOddDegree.sInclusion (wholeProjection ⁻¹' (boundary principalSix)ᶜ)) spaceCoverHomeomorph.equivariant
    (fun _ _ => rfl) W pS interiorProjection wholeProjection pS_isQuotientCovering
    (restrictedQuotientCovering wholeProjection (boundary principalSix)ᶜ) wholeQuotientCovering
  unfold spaceChainMap
  exact (localSpaceMap_congr _ _ upstairs_factor.symm _ _ _ _ _ _ _).trans h.symm

/-- The local chain isomorphism of the identity homeomorphism is the identity. -/
theorem homeomorphLocalIso_refl {X : Type} [TopologicalSpace X] (x : X) :
    (RationalLocalChartHomology.homeomorphLocalIso (Homeomorph.refl X) x).hom =
      𝟙 (RationalLocalChartHomology.localChains x) := by
  unfold RationalLocalChartHomology.homeomorphLocalIso RationalRelativeSingular.relativeHomeomorphIso
  apply (cancel_epi (Limits.cokernel.π (RationalRelativeSingular.inclusion ({x}ᶜ : Set X)))).mp
  simp [Limits.cokernel.mapIso, RationalRelativeSingular.chainHomeomorphIso]
  exact (Category.comp_id _).symm

/-- The point homology isomorphism of the identity homeomorphism is the identity. -/
theorem pointHomologyIso_refl_apply {X : Type} [TopologicalSpace X] (x : X) (k : ℕ)
    (c : (RationalLocalChartHomology.localChains x).homology k) :
    (RationalLocalOrientation.pointHomologyIso (Homeomorph.refl X) x k).hom c = c := by
  have key : ∀ (f : RationalLocalChartHomology.localChains x ⟶
      RationalLocalChartHomology.localChains ((Homeomorph.refl X) x)), f = 𝟙 _ →
      ∀ c : (RationalLocalChartHomology.localChains x).homology k, homologyMap f k c = c := by
    intro f hf c
    subst hf
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (homologyMap_id (RationalLocalChartHomology.localChains x) k)) c
  exact key _ (homeomorphLocalIso_refl x) c

/-- Cap naturality for the cover homeomorphism `spaceCoverHomeomorph`. -/
theorem capTransport (W : Rep.{0} ℚ principalSix) (K : Compacts ↥(boundary principalSix)ᶜ) :
    homologyMap (coveringSupportIso spaceCoverHomeomorph W (K : Set _)).hom 2 ≫
      compactCapAt (H := SymmetricSpaceCharts.Coordinates) pS W 3 interiorEuclidean interiorOrientation
        (SingularLocalCapHomeomorph.compactOrderIso spaceCoverHomeomorph.base K) 2 3 rfl ≫
      homologyMap (coveringChainMap spaceCoverHomeomorph W) 3 =
    compactCapAt (H := SymmetricSpaceCharts.Coordinates) interiorProjection W 3 interiorEuclidean
      interiorOrientation K 2 3 rfl := by
  have ho : SingularLocalCapHomeomorph.OrientationCompatible spaceCoverHomeomorph.base 3
      interiorOrientation interiorOrientation := fun x => pointHomologyIso_refl_apply _ _ _
  exact coveringCompactCapAt_natural (HX := SymmetricSpaceCharts.Coordinates)
    (HY := SymmetricSpaceCharts.Coordinates) spaceCoverHomeomorph W 3
    interiorEuclidean interiorEuclidean interiorOrientation interiorOrientation ho K 2 3 rfl


open TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCoefficient
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalHomology
  TernaryPoly.SingularLocalCap.Descent TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.CompactInteriorRelativeBoundary
  TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Homology
  TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.EquivariantSingularCohomology TernaryPoly.RationalHomologyCoefficients

/-- Geometric coefficients: pulling back along the cover homeomorphism after restricting to the interior
evaluates at the simplex pushed forward by `upstairs`. -/
theorem vertexToFunction_transport (W : Rep.{0} ℚ principalSix)
    (x : (localCochains wholeProjection wholeQuotientCovering W).X 2)
    (τ : SingularSimplex (TopCat.of Space) 2) :
    vertexToFunction pS pS_isQuotientCovering
        ((coveringCochainMap spaceCoverHomeomorph W).f 2
          ((localRestriction wholeProjection (boundary principalSix)ᶜ W).f 2 x)) τ =
      vertexToFunction wholeProjection wholeQuotientCovering x (projection upstairs 2 τ) := by
  have h1 := vertexToFunction_pullback pS interiorProjection
    (TopCat.isoOfHomeo spaceCoverHomeomorph.total).hom
    (TopCat.isoOfHomeo spaceCoverHomeomorph.base).hom spaceCoverHomeomorph.square
    pS_isQuotientCovering (restrictedQuotientCovering wholeProjection (boundary principalSix)ᶜ)
    spaceCoverHomeomorph.equivariant W 2 ((localRestriction wholeProjection (boundary principalSix)ᶜ W).f 2 x) τ
  have h2 := vertexToFunction_pullback _ _ _ _
    (restricted_square wholeProjection (boundary principalSix)ᶜ)
    (restrictedQuotientCovering wholeProjection (boundary principalSix)ᶜ) wholeQuotientCovering
    (fun _ _ => rfl) W 2 x (projection (TopCat.isoOfHomeo spaceCoverHomeomorph.total).hom 2 τ)
  exact h1.trans (h2.trans rfl)

/-- Compatible cocycle representatives of a compactly supported class of `pS` upstairs and on the compact
bordification, with the cochain-level and cap compatibilities (see the module docstring).  Here
`openCompactImage boundaryComplementOpen K` is the image of `K` under `Subtype.val`. -/
theorem exists_transport (W : Rep.{0} ℚ principalSix) (K : Compacts ↥(boundary principalSix)ᶜ)
    (y : (supportCochains pS W (K : Set ↥(boundary principalSix)ᶜ)).homology 2) :
    ∃ (φh : Cycles ((supportCochains wholeProjection W
        ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
          Set BordifiedOrbit)).sc' (2 - 1) 2 (2 + 1)))
      (φ : Cycles ((supportCochains pS W (K : Set ↥(boundary principalSix)ᶜ)).sc'
        (2 - 1) 2 (2 + 1))),
      cochainClass (supportCochains pS W (K : Set ↥(boundary principalSix)ᶜ)) 2 φ = y ∧
      (∀ τ : SingularSimplex (TopCat.of Space) 2,
        vertexToFunction pS pS_isQuotientCovering
            ((supportInclusion pS W (K : Set ↥(boundary principalSix)ᶜ)).f 2 φ.val) τ =
          vertexToFunction wholeProjection wholeQuotientCovering
            ((supportInclusion wholeProjection W
              ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
                Set BordifiedOrbit)).f 2 φh.val) (projection upstairs 2 τ)) ∧
      relativeCapMap W 2 3 rfl
          (homologyMap (supportMap wholeProjection W
            ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
              Set BordifiedOrbit) (boundary principalSix)ᶜ
            (openCompactImage_subset boundaryComplementOpen K)) 2
            (cochainClass (supportCochains wholeProjection W
              ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
                Set BordifiedOrbit)) 2 φh)) =
        homologyMap (spaceChainMap W) 3
          (compactCapMap (H := SymmetricSpaceCharts.Coordinates) pS W 3 interiorEuclidean
            interiorOrientation 2 3 rfl
            (compactClassMap pS W K 2 y)) := by
  classical
  let e1 := coveringSupportIso spaceCoverHomeomorph W (K : Set ↥(boundary principalSix)ᶜ)
  let e2 := openSupportIso wholeProjection W boundaryComplementOpen K 2
  let y1 : (supportCochains interiorProjection W (K : Set ↥(boundary principalSix)ᶜ)).homology 2 :=
    homologyMap e1.inv 2 y
  obtain ⟨φh, hφh⟩ := Algebra.cochainClass_surjective
    (supportCochains wholeProjection W
      ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) : Set BordifiedOrbit))
    2 (e2.inv y1)
  let ψ := mapComplexCycle (openRestrictionMap wholeProjection W boundaryComplementOpen K)
    (2 - 1) 2 (2 + 1) φh
  let φ := mapComplexCycle e1.hom (2 - 1) 2 (2 + 1) ψ
  have hψ : homologyMap (openRestrictionMap wholeProjection W boundaryComplementOpen K) 2
      (cochainClass _ 2 φh) = cochainClass _ 2 ψ := Algebra.cochainClass_natural _ 2 φh ψ rfl
  have hφ : homologyMap e1.hom 2 (cochainClass _ 2 ψ) = cochainClass _ 2 φ :=
    Algebra.cochainClass_natural _ 2 ψ φ rfl
  have hy1 : homologyMap e1.hom 2 y1 = y := by
    change (homologyMap e1.inv 2 ≫ homologyMap e1.hom 2) y = y
    rw [← homologyMap_comp, Iso.inv_hom_id, homologyMap_id]
    rfl
  have h2 : homologyMap (openRestrictionMap wholeProjection W boundaryComplementOpen K) 2
      (cochainClass _ 2 φh) = y1 := by
    rw [hφh]
    exact Iso.inv_hom_id_apply e2 y1
  refine ⟨φh, φ, ?_, ?_, ?_⟩
  · have hcl : cochainClass _ 2 ψ = y1 := hψ.symm.trans h2
    exact hφ.symm.trans ((congrArg (fun z => homologyMap e1.hom 2 z) hcl).trans hy1)
  · intro τ
    have a := congrArg (fun f => f.f 2 ψ.val)
      (coveringSupportIso_inclusion spaceCoverHomeomorph W (K : Set ↥(boundary principalSix)ᶜ))
    change (supportInclusion pS W _).f 2 (e1.hom.f 2 ψ.val) =
      (coveringCochainMap spaceCoverHomeomorph W).f 2
        ((supportInclusion interiorProjection W _).f 2 ψ.val) at a
    have b := congrArg (fun f => f.f 2 φh.val)
      (openRestrictionMap_inclusion wholeProjection W boundaryComplementOpen K)
    change (supportInclusion (restrictedProjection wholeProjection _) W _).f 2
        ((openRestrictionMap wholeProjection W boundaryComplementOpen K).f 2 φh.val) =
      (localRestriction wholeProjection _ W).f 2
        ((supportInclusion wholeProjection W _).f 2 φh.val) at b
    have hi1 := a.trans (congrArg _ b)
    refine Eq.trans ?_ (vertexToFunction_transport W
      ((supportInclusion wholeProjection W
        ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
          Set BordifiedOrbit)).f 2 φh.val) τ)
    exact congrArg (fun z => vertexToFunction pS pS_isQuotientCovering z τ) hi1
  · have hcls := classInOpen_cap W (openCompactImage boundaryComplementOpen K)
      (openCompactImage_subset boundaryComplementOpen K) 2 3 rfl
    have hL : relativeCapMap W 2 3 rfl
        (homologyMap (supportMap wholeProjection W
          ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
            Set BordifiedOrbit) (boundary principalSix)ᶜ
          (openCompactImage_subset boundaryComplementOpen K)) 2
          (cochainClass (supportCochains wholeProjection W
            ((openCompactImage boundaryComplementOpen K : Compacts BordifiedOrbit) :
              Set BordifiedOrbit)) 2 φh)) =
        interiorCapToBordified W 2 3 rfl
          (classInOpen wholeProjection W boundaryComplementOpen
            (openCompactImage boundaryComplementOpen K)
            (openCompactImage_subset boundaryComplementOpen K) 2 (cochainClass _ 2 φh)) :=
      (congrArg (fun f => f (cochainClass _ 2 φh)) hcls).symm
    have hM : classInOpen wholeProjection W boundaryComplementOpen
        (openCompactImage boundaryComplementOpen K)
        (openCompactImage_subset boundaryComplementOpen K) 2 (cochainClass _ 2 φh) =
        compactClassMap interiorProjection W K 2 y1 := by
      refine (congrArg (fun f => f (cochainClass _ 2 φh))
        (classInOpen_image wholeProjection W boundaryComplementOpen K 2)).trans ?_
      exact congrArg (fun z => compactClassMap interiorProjection W K 2 z) h2
    have hP : compactCapAt (H := SymmetricSpaceCharts.Coordinates) interiorProjection W 3
        interiorEuclidean interiorOrientation K 2 3 rfl y1 =
        homologyMap (coveringChainMap spaceCoverHomeomorph W) 3
          (compactCapAt (H := SymmetricSpaceCharts.Coordinates) pS W 3 interiorEuclidean
            interiorOrientation K 2 3 rfl y) := by
      have := congrArg (fun f => f y1) (capTransport W K)
      refine this.symm.trans ?_
      exact congrArg (fun z => homologyMap (coveringChainMap spaceCoverHomeomorph W) 3
        (compactCapAt (H := SymmetricSpaceCharts.Coordinates) pS W 3 interiorEuclidean
          interiorOrientation K 2 3 rfl z)) hy1
    have hN : compactCapMap (H := SymmetricSpaceCharts.Coordinates) interiorProjection W 3
        interiorEuclidean interiorOrientation 2 3 rfl (compactClassMap interiorProjection W K 2 y1) =
        compactCapAt (H := SymmetricSpaceCharts.Coordinates) interiorProjection W 3
          interiorEuclidean interiorOrientation K 2 3 rfl y1 :=
      congrArg (fun f => f y1) (compactCapMap_classMap interiorProjection W 3 interiorEuclidean
        interiorOrientation K 2 3 rfl)
    have hQ : compactCapMap (H := SymmetricSpaceCharts.Coordinates) pS W 3 interiorEuclidean
        interiorOrientation 2 3 rfl (compactClassMap pS W K 2 y) =
        compactCapAt (H := SymmetricSpaceCharts.Coordinates) pS W 3 interiorEuclidean
          interiorOrientation K 2 3 rfl y :=
      congrArg (fun f => f y) (compactCapMap_classMap pS W 3 interiorEuclidean
        interiorOrientation K 2 3 rfl)
    refine hL.trans ?_
    rw [hM]
    have hI : interiorCapToBordified W 2 3 rfl (compactClassMap interiorProjection W K 2 y1) =
        homologyMap (openLocalChainMap wholeProjection W (boundary principalSix)ᶜ) 3
          (compactCapMap (H := SymmetricSpaceCharts.Coordinates) interiorProjection W 3
            interiorEuclidean interiorOrientation 2 3 rfl
            (compactClassMap interiorProjection W K 2 y1)) := rfl
    rw [hI, hN, hP, hQ, spaceChainMap_eq, homologyMap_comp]
    rfl

/-- `exists_transport` for an arbitrary ambient compact `Kb` whose underlying set is the image of `K`. -/
theorem exists_transport_of_image (W : Rep.{0} ℚ principalSix)
    (K : Compacts ↥(boundary principalSix)ᶜ) (Kb : Compacts BordifiedOrbit)
    (hKb : (Kb : Set BordifiedOrbit) = Subtype.val '' (K : Set ↥(boundary principalSix)ᶜ))
    (hKA : (Kb : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (y : (supportCochains pS W (K : Set ↥(boundary principalSix)ᶜ)).homology 2) :
    ∃ (φh : Cycles ((supportCochains wholeProjection W (Kb : Set BordifiedOrbit)).sc'
        (2 - 1) 2 (2 + 1)))
      (φ : Cycles ((supportCochains pS W (K : Set ↥(boundary principalSix)ᶜ)).sc'
        (2 - 1) 2 (2 + 1))),
      cochainClass (supportCochains pS W (K : Set ↥(boundary principalSix)ᶜ)) 2 φ = y ∧
      (∀ τ : SingularSimplex (TopCat.of Space) 2,
        vertexToFunction pS pS_isQuotientCovering
            ((supportInclusion pS W (K : Set ↥(boundary principalSix)ᶜ)).f 2 φ.val) τ =
          vertexToFunction wholeProjection wholeQuotientCovering
            ((supportInclusion wholeProjection W (Kb : Set BordifiedOrbit)).f 2 φh.val)
            (projection upstairs 2 τ)) ∧
      relativeCapMap W 2 3 rfl
          (homologyMap (supportMap wholeProjection W (Kb : Set BordifiedOrbit)
            (boundary principalSix)ᶜ hKA) 2
            (cochainClass (supportCochains wholeProjection W (Kb : Set BordifiedOrbit)) 2 φh)) =
        homologyMap (spaceChainMap W) 3
          (compactCapMap pS W 3 interiorEuclidean interiorOrientation 2 3 rfl
            (compactClassMap pS W K 2 y)) := by
  have hKb' : Kb = openCompactImage boundaryComplementOpen K := SetLike.coe_injective hKb
  subst hKb'
  exact exists_transport W K y

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
