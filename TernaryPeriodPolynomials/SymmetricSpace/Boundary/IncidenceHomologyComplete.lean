module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyCycles

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence OrdinaryIncidence
open SymmetricSpaceBoundaryMV SymmetricSpaceBoundaryFaceAugmentation
open EquivariantMayerVietorisHomology EquivariantSingularResolution
open scoped MonoidAlgebra

/-- This computation uses the singular complex of the entire actual geometric boundary. -/
theorem actual_boundary_complex : boundaryChains=equivariantChains principalSix (TopCat.of SingularBoundaryRestriction.BoundaryCover) := rfl

/-- The incidence differential is literally line minus plane. -/
theorem actual_incidence : incidence=biprod.lift lineIncidence (-planeIncidence) := rfl

/-- The boundary-to-edge map is literally the actual small-chain comparison, MV connecting map,
and corner H0 augmentation, in that order. -/
theorem actual_boundary_edge_map : boundaryEdgeMap=
    (ambientHomologyIso 1).inv ≫ mvShortExact.δ 1 0 rfl ≫ interH0Iso.hom := rfl

/-- Both kernel descriptions preserve the actual MV edge map. -/
theorem actual_h1_comparisons :
    boundaryH1Iso.hom ≫ kernel.ι incidence=boundaryEdgeMap ∧
    boundaryH1OrdinaryCyclesIso.hom ≫ ordinaryCycleInclusion=boundaryEdgeMap :=
  ⟨boundaryH1Iso_edge,boundaryH1OrdinaryCyclesIso_edge⟩

/-- All higher homology groups of the actual boundary vanish. -/
theorem actual_higher_homology (n : ℕ) (hn : 2≤n) : IsZero (boundaryChains.homology n) :=
  boundary_homology_ge_two n hn

/-- H0 is the trivial rational representation through the actual coefficient-sum augmentation. -/
theorem actual_h0_augmentation : boundaryH0Iso.hom=homologyAugmentation principalSix ambient ∧
    boundaryZeroClass ≫ boundaryH0Iso.hom=augmentation principalSix ambient :=
  ⟨boundaryH0Iso_augmentation,boundaryZeroClass_augmentation⟩

/-- The actual overlap map becomes literal signed incidence under the face augmentations. -/
theorem actual_overlap_naturality : homologyMap mvComplex.f 0 ≫ middleH0Iso.hom=
    interH0Iso.hom ≫ incidence := incidence_natural

/-- Each flag has positive line coefficient and negative plane coefficient. -/
theorem actual_flag_singleton (F : Flag) (r : ℚ) :
    scalarVertexIso.hom (incidence (MonoidAlgebra.single F r))=
      Finsupp.single (Sum.inl F.val.1) r-Finsupp.single (Sum.inr F.val.2) r :=
  scalarIncidence_single F r

/-- The fixed ordinary graph boundary has the opposite vertex orientation. -/
theorem actual_ordinary_boundary_sign (c : ℚ[Flag]) : scalarVertexIso.hom (incidence c)=
    -OrdinaryIncidenceChains.boundary (edgeCoefficients c) := scalarIncidence_boundary c

/-- The actual edge map commutes with the geometric principal-six action. -/
theorem boundaryEdgeMap_equivariant (g : principalSix) (c : boundaryChains.homology 1) :
    boundaryEdgeMap ((boundaryChains.homology 1).ρ g c)=flagLabels.ρ g (boundaryEdgeMap c) :=
  Rep.hom_comm_apply _ g c

/-- The cycle isomorphism commutes with the restricted ordinary arithmetic action. -/
theorem boundaryH1OrdinaryCyclesIso_equivariant (g : principalSix) (c : boundaryChains.homology 1) :
    boundaryH1OrdinaryCyclesIso.hom ((boundaryChains.homology 1).ρ g c)=
      ordinaryCyclesRep.ρ g (boundaryH1OrdinaryCyclesIso.hom c) := Rep.hom_comm_apply _ g c

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
