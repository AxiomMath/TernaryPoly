module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution FreeActionLinearization
open SymmetricSpaceBoundaryMV IntegralGL3Congruence

/-- The component resolutions are literally the actual free singular complexes. -/
theorem resolution_complexes : lineResolution.complex=lineChains ∧
    planeResolution.complex=planeChains ∧ flagResolution.complex=flagChains := ⟨rfl,rfl,rfl⟩

theorem resolution_augmentations : lineResolution.π=lineAugmentationChain ∧
    planeResolution.π=planeAugmentationChain ∧ flagResolution.π=flagAugmentationChain := ⟨rfl,rfl,rfl⟩

/-- Positive homology vanishes for all three actual face sums. -/
theorem all_positive_homology_zero (n : ℕ) (hn : n≠0) :
    IsZero (lineChains.homology n) ∧ IsZero (planeChains.homology n) ∧ IsZero (flagChains.homology n) :=
  ⟨linePositiveHomology n hn,planePositiveHomology n hn,flagPositiveHomology n hn⟩

theorem lineAugmentation_equivariant (g : principalSix) (c : lineChains.X 0) :
    lineAugmentation ((lineChains.X 0).ρ g c)=lineLabels.ρ g (lineAugmentation c) :=
  Rep.hom_comm_apply _ g c

theorem planeAugmentation_equivariant (g : principalSix) (c : planeChains.X 0) :
    planeAugmentation ((planeChains.X 0).ρ g c)=planeLabels.ρ g (planeAugmentation c) :=
  Rep.hom_comm_apply _ g c

theorem flagAugmentation_equivariant (g : principalSix) (c : flagChains.X 0) :
    flagAugmentation ((flagChains.X 0).ρ g c)=flagLabels.ρ g (flagAugmentation c) :=
  Rep.hom_comm_apply _ g c

theorem lineH0Iso_equivariant (g : principalSix) (c : lineChains.homology 0) :
    lineH0Iso.hom ((lineChains.homology 0).ρ g c)=lineLabels.ρ g (lineH0Iso.hom c) :=
  Rep.hom_comm_apply _ g c

theorem planeH0Iso_equivariant (g : principalSix) (c : planeChains.homology 0) :
    planeH0Iso.hom ((planeChains.homology 0).ρ g c)=planeLabels.ρ g (planeH0Iso.hom c) :=
  Rep.hom_comm_apply _ g c

theorem flagH0Iso_equivariant (g : principalSix) (c : flagChains.homology 0) :
    flagH0Iso.hom ((flagChains.homology 0).ρ g c)=flagLabels.ρ g (flagH0Iso.hom c) :=
  Rep.hom_comm_apply _ g c

/-- Both literal full-flag inclusion maps commute with augmentation and induce the exact
label-incidence maps on H0. No derived or Shapiro comparison is asserted here. -/
theorem actual_incidence_naturality :
    lineChainMap.f 0 ≫ lineAugmentation=flagAugmentation ≫ lineIncidence ∧
    planeChainMap.f 0 ≫ planeAugmentation=flagAugmentation ≫ planeIncidence ∧
    homologyMap lineChainMap 0 ≫ lineH0Iso.hom=flagH0Iso.hom ≫ lineIncidence ∧
    homologyMap planeChainMap 0 ≫ planeH0Iso.hom=flagH0Iso.hom ≫ planeIncidence :=
  ⟨lineAugmentation_natural,planeAugmentation_natural,lineH0_natural,planeH0_natural⟩

end TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
