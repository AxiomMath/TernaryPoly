module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallSubspace
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisBiprod

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularSmall
open CategoryTheory HomologicalComplex EquivariantSingularResolution SingularCoverNaturality
open SphereOddDegree EquivariantSingularMayerVietoris

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (S T : Set E) [MulAction G S] [ContinuousConstSMul G S] [MulAction G T] [ContinuousConstSMul G T]
  (hS : InvariantSet G E S) (hT : InvariantSet G E T)
  (hincS : ∀ (g : G) (x : S), (g • x).val = g • x.val)
  (hincT : ∀ (g : G) (x : T), (g • x).val = g • x.val) (hST : S ⊆ T)

/-- The literal continuous inclusion of two nested subspaces. -/
def subspaceInclusion : TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun x => ⟨x.val,hST x.property⟩,continuous_subtype_val.subtype_mk _⟩

omit [ContinuousConstSMul G E] [ContinuousConstSMul G S] [ContinuousConstSMul G T] in
include hincS hincT in
/-- The nested subspace inclusion respects their actual restricted actions. -/
theorem subspaceInclusion_equivariant (g : G) (x : S) :
    subspaceInclusion E S T hST (g • x) = g • subspaceInclusion E S T hST x := by
  apply Subtype.ext
  exact (hincS g x).trans (hincT g (subspaceInclusion E S T hST x)).symm

/-- The actual subspace comparisons commute with each literal nested inclusion. -/
theorem subspaceCorestrict_naturality :
    subspaceCorestrict G E S hS hincS ≫ subordinateMap G E S T hS hT hST =
      chainMap (subspaceInclusion E S T hST) (subspaceInclusion_equivariant G E S T hincS hincT hST) ≫
        subspaceCorestrict G E T hT hincT := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  apply Subtype.ext
  have h : subspaceInclusion E S T hST ≫ sInclusion T = sInclusion S := rfl
  exact (congrArg (fun f => (f.f n).hom c)
    ((Functor.map_comp _ _ _).symm.trans (congrArg
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map) h))).symm

/-- Genuine subordinate cochains identify with actual singular cochains of the subspace. -/
def subspaceCochainIso (W : Rep.{0} ℚ G) :
    homCochains (subordinateComplex G E S hS) W ≅
      EquivariantSingularCohomology.cochains G (TopCat.of S) W :=
  homIso (subspaceIso G E S hS hincS) W

/-- The actual cochain comparison preserves ambient restriction. -/
theorem subspaceCochainIso_inclusion (W : Rep.{0} ℚ G) :
    homPullback (subordinateInclusion G E S hS) W ≫ (subspaceCochainIso G E S hS hincS W).hom =
      cochainPullback (sInclusion S) hincS W := by
  change homPullback (subordinateInclusion G E S hS) W ≫
    homPullback (subspaceCorestrict G E S hS hincS) W = _
  rw [← homPullback_comp, subspaceCorestrict_inclusion]
  rfl

/-- The actual subordinate restriction agrees with literal subspace pullback. -/
theorem subspaceCochainIso_naturality (W : Rep.{0} ℚ G) :
    homPullback (subordinateMap G E S T hS hT hST) W ≫ (subspaceCochainIso G E S hS hincS W).hom =
      (subspaceCochainIso G E T hT hincT W).hom ≫
        cochainPullback (subspaceInclusion E S T hST)
          (subspaceInclusion_equivariant G E S T hincS hincT hST) W := by
  change homPullback (subordinateMap G E S T hS hT hST) W ≫
    homPullback (subspaceCorestrict G E S hS hincS) W =
      homPullback (subspaceCorestrict G E T hT hincT) W ≫ homPullback _ W
  rw [← homPullback_comp, subspaceCorestrict_naturality, homPullback_comp]

end TernaryPoly.EquivariantSingularSmall
