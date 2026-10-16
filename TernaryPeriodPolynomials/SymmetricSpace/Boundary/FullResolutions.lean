module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullFaces

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex ModThreeGoodAction IntegralGL3Congruence
open OrdinaryIncidence SymmetricSpaceBoundaryMV EquivariantSingularResolution
open SymmetricSpaceBoundaryFullTransfer

local instance fullLineLabelTopology : TopologicalSpace Line := ⊥
local instance fullPlaneLabelTopology : TopologicalSpace Plane := ⊥
local instance fullFlagLabelTopology : TopologicalSpace Flag := ⊥
local instance fullLineLabelDiscrete : DiscreteTopology Line := ⟨rfl⟩
local instance fullPlaneLabelDiscrete : DiscreteTopology Plane := ⟨rfl⟩
local instance fullFlagLabelDiscrete : DiscreteTopology Flag := ⟨rfl⟩

abbrev fullLineChains := equivariantChains IntegralGL (TopCat.of LineFaceSum)
abbrev fullLineLabels := Rep.ofMulAction ℚ IntegralGL Line

/-- The full line-face singular resolution restricts to the actual cover resolution. -/
def lineChainRestrictionIso : restrictedComplex principalSix fullLineChains ≅
    SymmetricSpaceBoundaryFaceAugmentation.lineChains :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by rfl)

instance fullLineChain_projective (n : ℕ) : Projective (fullLineChains.X n) := by
  let : Projective (Rep.res principalSix.subtype (fullLineChains.X n)) :=
    EquivariantSingularResolution.chainRep_projective principalSix (TopCat.of LineFaceSum) n
  exact projective_of_restriction principalSix _

/-- The augmentation resolves every actual full integral line label. -/
def fullLineAugmentation : fullLineChains ⟶
    (ChainComplex.single₀ (Rep ℚ IntegralGL)).obj fullLineLabels :=
  SingularComponentAugmentation.augmentationChain
    SymmetricSpaceBoundaryFaceAugmentation.lineFamily IntegralGL fullLineSum_label

/-- Actual projective resolution, obtained from contractible faces and rational finite-index descent. -/
def fullLineResolution : ProjectiveResolution fullLineLabels where
  complex := fullLineChains
  projective := fullLineChain_projective
  π := fullLineAugmentation
  quasiIso := SingularComponentAugmentation.augmentationChain_quasiIso
    SymmetricSpaceBoundaryFaceAugmentation.lineFamily IntegralGL fullLineSum_label

abbrev fullPlaneChains := equivariantChains IntegralGL (TopCat.of PlaneFaceSum)
abbrev fullPlaneLabels := Rep.ofMulAction ℚ IntegralGL Plane

/-- The full plane-face singular resolution restricts to the actual cover resolution. -/
def planeChainRestrictionIso : restrictedComplex principalSix fullPlaneChains ≅
    SymmetricSpaceBoundaryFaceAugmentation.planeChains :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by rfl)

instance fullPlaneChain_projective (n : ℕ) : Projective (fullPlaneChains.X n) := by
  let : Projective (Rep.res principalSix.subtype (fullPlaneChains.X n)) :=
    EquivariantSingularResolution.chainRep_projective principalSix (TopCat.of PlaneFaceSum) n
  exact projective_of_restriction principalSix _

/-- The augmentation resolves every actual full integral plane label. -/
def fullPlaneAugmentation : fullPlaneChains ⟶
    (ChainComplex.single₀ (Rep ℚ IntegralGL)).obj fullPlaneLabels :=
  SingularComponentAugmentation.augmentationChain
    SymmetricSpaceBoundaryFaceAugmentation.planeFamily IntegralGL fullPlaneSum_label

/-- Actual projective resolution, obtained from contractible faces and rational finite-index descent. -/
def fullPlaneResolution : ProjectiveResolution fullPlaneLabels where
  complex := fullPlaneChains
  projective := fullPlaneChain_projective
  π := fullPlaneAugmentation
  quasiIso := SingularComponentAugmentation.augmentationChain_quasiIso
    SymmetricSpaceBoundaryFaceAugmentation.planeFamily IntegralGL fullPlaneSum_label

abbrev fullFlagChains := equivariantChains IntegralGL (TopCat.of CornerFaceSum)
abbrev fullFlagLabels := Rep.ofMulAction ℚ IntegralGL Flag

/-- The full flag-face singular resolution restricts to the actual cover resolution. -/
def flagChainRestrictionIso : restrictedComplex principalSix fullFlagChains ≅
    SymmetricSpaceBoundaryFaceAugmentation.flagChains :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by rfl)

instance fullFlagChain_projective (n : ℕ) : Projective (fullFlagChains.X n) := by
  let : Projective (Rep.res principalSix.subtype (fullFlagChains.X n)) :=
    EquivariantSingularResolution.chainRep_projective principalSix (TopCat.of CornerFaceSum) n
  exact projective_of_restriction principalSix _

/-- The augmentation resolves every actual full integral flag label. -/
def fullFlagAugmentation : fullFlagChains ⟶
    (ChainComplex.single₀ (Rep ℚ IntegralGL)).obj fullFlagLabels :=
  SingularComponentAugmentation.augmentationChain
    SymmetricSpaceBoundaryFaceAugmentation.flagFamily IntegralGL fullFlagSum_label

/-- Actual projective resolution, obtained from contractible faces and rational finite-index descent. -/
def fullFlagResolution : ProjectiveResolution fullFlagLabels where
  complex := fullFlagChains
  projective := fullFlagChain_projective
  π := fullFlagAugmentation
  quasiIso := SingularComponentAugmentation.augmentationChain_quasiIso
    SymmetricSpaceBoundaryFaceAugmentation.flagFamily IntegralGL fullFlagSum_label

end TernaryPoly.SymmetricSpaceBoundaryFull
