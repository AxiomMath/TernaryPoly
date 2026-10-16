module

public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationHomology
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVComplete

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open CategoryTheory Limits EquivariantSingularResolution FreeActionLinearization
open OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryMV SingularBoundaryRestriction IntegralGL3Congruence
open scoped MonoidAlgebra

instance lineLabelAction : MulAction principalSix Line where
  smul g L := OrdinaryFullAction.lineAction (OrdinaryFullAction.integral g.val) L
  one_smul L := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral (1 : ModThreeGoodAction.IntegralGL)) L.val=L.val
    rw [map_one,OrdinaryFullAction.subspaceAction_one]
  mul_smul g h L := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral (g.val*h.val)) L.val=_
    rw [map_mul]
    exact OrdinaryFullAction.subspaceAction_mul _ _ _

instance planeLabelAction : MulAction principalSix Plane where
  smul g P := OrdinaryFullAction.planeAction (OrdinaryFullAction.integral g.val) P
  one_smul P := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral (1 : ModThreeGoodAction.IntegralGL)) P.val=P.val
    rw [map_one,OrdinaryFullAction.subspaceAction_one]
  mul_smul g h P := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral (g.val*h.val)) P.val=_
    rw [map_mul]
    exact OrdinaryFullAction.subspaceAction_mul _ _ _

instance flagLabelAction : MulAction principalSix Flag where
  smul g F := flagAction g F
  one_smul F := Subtype.ext (Prod.ext (one_smul principalSix F.val.1) (one_smul principalSix F.val.2))
  mul_smul g h F := Subtype.ext (Prod.ext (mul_smul g h F.val.1) (mul_smul g h F.val.2))

local instance lineLabelTopology : TopologicalSpace Line := ⊥
local instance planeLabelTopology : TopologicalSpace Plane := ⊥
local instance flagLabelTopology : TopologicalSpace Flag := ⊥
local instance lineLabelDiscrete : DiscreteTopology Line := ⟨rfl⟩
local instance planeLabelDiscrete : DiscreteTopology Plane := ⟨rfl⟩
local instance flagLabelDiscrete : DiscreteTopology Flag := ⟨rfl⟩

instance flagFace_contractible (F : Flag) : ContractibleSpace (flagFace F) :=
  (flagCoordinates F).symm.contractibleSpace

theorem lineLabel_equivariant (g : principalSix) (x : LineFaceSum) : (g • x).1=g • x.1 :=
  lineFaceSum_smul_label g x

theorem planeLabel_equivariant (g : principalSix) (x : PlaneFaceSum) : (g • x).1=g • x.1 :=
  planeFaceSum_smul_label g x

theorem flagLabel_equivariant (g : principalSix) (x : CornerFaceSum) : (g • x).1=g • x.1 :=
  cornerFaceSum_smul_label g x

instance lineSumFree : IsCancelSMul principalSix LineFaceSum where
  right_cancel' g h x he := by
    have hh := congrArg lineFaceSumHomeomorph he
    rw [lineFaceSumHomeomorph_equivariant,lineFaceSumHomeomorph_equivariant] at hh
    exact IsCancelSMul.right_cancel g h (lineFaceSumHomeomorph x).val
      (congrArg (fun y : lineSide => y.val) hh)

instance planeSumFree : IsCancelSMul principalSix PlaneFaceSum where
  right_cancel' g h x he := by
    have hh := congrArg planeFaceSumHomeomorph he
    rw [planeFaceSumHomeomorph_equivariant,planeFaceSumHomeomorph_equivariant] at hh
    exact IsCancelSMul.right_cancel g h (planeFaceSumHomeomorph x).val
      (congrArg (fun y : planeSide => y.val) hh)

instance flagSumFree : IsCancelSMul principalSix CornerFaceSum where
  right_cancel' g h x he := by
    have hh := congrArg cornerFaceSumHomeomorph he
    rw [cornerFaceSumHomeomorph_equivariant,cornerFaceSumHomeomorph_equivariant] at hh
    exact IsCancelSMul.right_cancel g h (cornerFaceSumHomeomorph x).val
      (congrArg (fun y : cornerLocus => y.val) hh)

abbrev lineFamily (L : Line) : Type := lineFace L
abbrev planeFamily (P : Plane) : Type := planeFace P
abbrev flagFamily (F : Flag) : Type := flagFace F

abbrev lineChains := equivariantChains principalSix (TopCat.of LineFaceSum)
abbrev lineLabels := Rep.ofMulAction ℚ principalSix Line

def lineDegreeFree (n : ℕ) : (lineChains.X n) ≅
    Rep.free ℚ principalSix (Orbits principalSix (SingularSimplex (TopCat.of LineFaceSum) n)) :=
  (degreeRepIso principalSix (TopCat.of LineFaceSum) n).symm ≪≫
    singularPermutationIsoFree ℚ principalSix (TopCat.of LineFaceSum) n

def lineAugmentation : lineChains.X 0 ⟶ lineLabels :=
  SingularComponentAugmentation.augmentation lineFamily principalSix lineLabel_equivariant

def lineAugmentationChain : lineChains ⟶ (ChainComplex.single₀ (Rep ℚ principalSix)).obj lineLabels :=
  SingularComponentAugmentation.augmentationChain lineFamily principalSix lineLabel_equivariant

def lineResolution : ProjectiveResolution lineLabels :=
  SingularComponentAugmentation.projectiveResolution lineFamily principalSix lineLabel_equivariant

def lineH0Iso : lineChains.homology 0 ≅ lineLabels :=
  SingularComponentAugmentation.homologyZeroIso lineFamily principalSix lineLabel_equivariant

theorem linePositiveHomology (n : ℕ) (hn : n≠0) : IsZero (lineChains.homology n) :=
  SingularComponentAugmentation.positive_equivariant_homology_isZero lineFamily principalSix n hn

theorem lineAugmentation_single (simplex : SingularSimplex (TopCat.of LineFaceSum) 0) (r : ℚ) :
    lineAugmentation (degreeLinearEquiv (TopCat.of LineFaceSum) 0 (MonoidAlgebra.single simplex r))=
      MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  SingularComponentAugmentation.augmentation_single lineFamily principalSix lineLabel_equivariant simplex r

theorem lineH0Iso_single (simplex : SingularSimplex (TopCat.of LineFaceSum) 0) (r : ℚ) :
    lineH0Iso.hom (SingularComponentAugmentation.zeroClassMap lineFamily principalSix
      (degreeLinearEquiv (TopCat.of LineFaceSum) 0 (MonoidAlgebra.single simplex r)))=
        MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  SingularComponentAugmentation.homologyZeroIso_single lineFamily principalSix lineLabel_equivariant simplex r

abbrev planeChains := equivariantChains principalSix (TopCat.of PlaneFaceSum)
abbrev planeLabels := Rep.ofMulAction ℚ principalSix Plane

def planeDegreeFree (n : ℕ) : (planeChains.X n) ≅
    Rep.free ℚ principalSix (Orbits principalSix (SingularSimplex (TopCat.of PlaneFaceSum) n)) :=
  (degreeRepIso principalSix (TopCat.of PlaneFaceSum) n).symm ≪≫
    singularPermutationIsoFree ℚ principalSix (TopCat.of PlaneFaceSum) n

def planeAugmentation : planeChains.X 0 ⟶ planeLabels :=
  SingularComponentAugmentation.augmentation planeFamily principalSix planeLabel_equivariant

def planeAugmentationChain : planeChains ⟶ (ChainComplex.single₀ (Rep ℚ principalSix)).obj planeLabels :=
  SingularComponentAugmentation.augmentationChain planeFamily principalSix planeLabel_equivariant

def planeResolution : ProjectiveResolution planeLabels :=
  SingularComponentAugmentation.projectiveResolution planeFamily principalSix planeLabel_equivariant

def planeH0Iso : planeChains.homology 0 ≅ planeLabels :=
  SingularComponentAugmentation.homologyZeroIso planeFamily principalSix planeLabel_equivariant

theorem planePositiveHomology (n : ℕ) (hn : n≠0) : IsZero (planeChains.homology n) :=
  SingularComponentAugmentation.positive_equivariant_homology_isZero planeFamily principalSix n hn

theorem planeAugmentation_single (simplex : SingularSimplex (TopCat.of PlaneFaceSum) 0) (r : ℚ) :
    planeAugmentation (degreeLinearEquiv (TopCat.of PlaneFaceSum) 0 (MonoidAlgebra.single simplex r))=
      MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  SingularComponentAugmentation.augmentation_single planeFamily principalSix planeLabel_equivariant simplex r

theorem planeH0Iso_single (simplex : SingularSimplex (TopCat.of PlaneFaceSum) 0) (r : ℚ) :
    planeH0Iso.hom (SingularComponentAugmentation.zeroClassMap planeFamily principalSix
      (degreeLinearEquiv (TopCat.of PlaneFaceSum) 0 (MonoidAlgebra.single simplex r)))=
        MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  SingularComponentAugmentation.homologyZeroIso_single planeFamily principalSix planeLabel_equivariant simplex r

abbrev flagChains := equivariantChains principalSix (TopCat.of CornerFaceSum)
abbrev flagLabels := Rep.ofMulAction ℚ principalSix Flag

def flagDegreeFree (n : ℕ) : (flagChains.X n) ≅
    Rep.free ℚ principalSix (Orbits principalSix (SingularSimplex (TopCat.of CornerFaceSum) n)) :=
  (degreeRepIso principalSix (TopCat.of CornerFaceSum) n).symm ≪≫
    singularPermutationIsoFree ℚ principalSix (TopCat.of CornerFaceSum) n

def flagAugmentation : flagChains.X 0 ⟶ flagLabels :=
  SingularComponentAugmentation.augmentation flagFamily principalSix flagLabel_equivariant

def flagAugmentationChain : flagChains ⟶ (ChainComplex.single₀ (Rep ℚ principalSix)).obj flagLabels :=
  SingularComponentAugmentation.augmentationChain flagFamily principalSix flagLabel_equivariant

def flagResolution : ProjectiveResolution flagLabels :=
  SingularComponentAugmentation.projectiveResolution flagFamily principalSix flagLabel_equivariant

def flagH0Iso : flagChains.homology 0 ≅ flagLabels :=
  SingularComponentAugmentation.homologyZeroIso flagFamily principalSix flagLabel_equivariant

theorem flagPositiveHomology (n : ℕ) (hn : n≠0) : IsZero (flagChains.homology n) :=
  SingularComponentAugmentation.positive_equivariant_homology_isZero flagFamily principalSix n hn

theorem flagAugmentation_single (simplex : SingularSimplex (TopCat.of CornerFaceSum) 0) (r : ℚ) :
    flagAugmentation (degreeLinearEquiv (TopCat.of CornerFaceSum) 0 (MonoidAlgebra.single simplex r))=
      MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  SingularComponentAugmentation.augmentation_single flagFamily principalSix flagLabel_equivariant simplex r

theorem flagH0Iso_single (simplex : SingularSimplex (TopCat.of CornerFaceSum) 0) (r : ℚ) :
    flagH0Iso.hom (SingularComponentAugmentation.zeroClassMap flagFamily principalSix
      (degreeLinearEquiv (TopCat.of CornerFaceSum) 0 (MonoidAlgebra.single simplex r)))=
        MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  SingularComponentAugmentation.homologyZeroIso_single flagFamily principalSix flagLabel_equivariant simplex r

end TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
