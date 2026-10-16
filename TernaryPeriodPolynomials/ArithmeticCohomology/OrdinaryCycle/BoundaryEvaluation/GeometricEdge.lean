module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConeConnecting
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeComplete

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex Preadditive BoundaryFaceResolutionComparison
open IntegralGL3Congruence SymmetricSpaceBoundaryFaceAugmentation
open SymmetricSpaceBoundaryIncidenceHomology SymmetricSpaceBoundaryGeometricCone

attribute [local instance] flagLabelTopology flagLabelDiscrete

/-- The actual flag-label augmentation annihilates actual boundaries. -/
theorem flagAugmentation_boundary : flagChains.d 1 0 ≫ flagAugmentation = 0 :=
  SingularComponentAugmentation.d_augmentation flagFamily principalSix flagLabel_equivariant

/-- The actual flag H0 isomorphism is the canonical cochain evaluator. -/
theorem flagH0Iso_evaluation : flagH0Iso.hom =
    evaluationOfCochain flagChains flagLabels 0 flagAugmentation flagAugmentation_boundary := by
  apply (cancel_epi (flagChains.homologyπ 0)).mp
  rw [evaluationOfCochain_projection]
  have h := SingularComponentAugmentation.zeroClassMap_homologyZeroIso
    flagFamily principalSix flagLabel_equivariant
  change (flagChains.cycles₀Iso.inv ≫ flagChains.homologyπ 0) ≫ flagH0Iso.hom =
    flagAugmentation at h
  apply (cancel_epi flagChains.cycles₀Iso.inv).mp
  rw [← Category.assoc, h]
  change flagAugmentation = (flagChains.cycles₀Iso.inv ≫ flagChains.cycles₀Iso.hom) ≫ flagAugmentation
  rw [Iso.inv_hom_id, Category.id_comp]

/-- The actual full-face cone detects its shifted flag coordinate by literal label augmentation. -/
def geometricCornerHomology : faceCone.homology 1 ⟶ flagLabels :=
  coneCornerHomology faceArrow flagLabels flagAugmentation flagAugmentation_boundary

/-- Passing through the actual small-chain comparison preserves the genuine MV connecting map. -/
theorem geometricCone_boundary_edge_small :
    homologyMap faceConeToBoundary 1 ≫ boundaryEdgeMap =
      homologyMap faceConeToSmall 1 ≫ mvShortExact.δ 1 0 rfl ≫ interH0Iso.hom := by
  rw [faceConeToBoundary, homologyMap_comp]
  change (homologyMap faceConeToSmall 1 ≫ (ambientHomologyIso 1).hom) ≫
    ((ambientHomologyIso 1).inv ≫ mvShortExact.δ 1 0 rfl ≫ interH0Iso.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual geometric cone-to-boundary map has precisely minus the literal flag-corner edge. -/
theorem geometricCone_boundary_edge :
    homologyMap faceConeToBoundary 1 ≫ boundaryEdgeMap = -geometricCornerHomology := by
  rw [geometricCone_boundary_edge_small]
  let S := ShortComplex.cokernelSequence faceArrow
  let hS := quotientShortExact faceArrow faceRetraction face_f_r
  let q := quotientMap faceArrow mvComplex flagToOpen facesToOpen faceArrow_square
  have hn := HomologySequence.δ_naturality
    (quotientComparison faceArrow mvComplex flagToOpen facesToOpen faceArrow_square)
    hS mvShortExact 1 0 rfl
  change hS.δ 1 0 rfl ≫ homologyMap flagToOpen 0 = homologyMap q 1 ≫ mvShortExact.δ 1 0 rfl at hn
  have haug : homologyMap flagToOpen 0 ≫ interH0Iso.hom = flagH0Iso.hom := by
    rw [flagToOpen_homology]
    change (interFaceHomologyIso 0).inv ≫ ((interFaceHomologyIso 0).hom ≫ flagH0Iso.hom) = _
    rw [Iso.inv_hom_id_assoc]
  change homologyMap (Cone.projection S ≫ q) 1 ≫ mvShortExact.δ 1 0 rfl ≫ interH0Iso.hom = _
  erw [homologyMap_comp, Category.assoc,
    ← Category.assoc (homologyMap q 1), ← hn, Category.assoc, haug, flagH0Iso_evaluation]
  exact coneProjection_connecting_evaluation S hS flagLabels flagAugmentation flagAugmentation_boundary

/-- The literal edge of every represented cone cycle is minus its augmented corner coordinate. -/
theorem geometricCone_boundary_edge_projection :
    faceCone.homologyπ 1 ≫ homologyMap faceConeToBoundary 1 ≫ boundaryEdgeMap =
      -(faceCone.iCycles 1 ≫ CofiberSequence.first faceArrow 0 ≫ flagAugmentation) := by
  rw [geometricCone_boundary_edge, comp_neg]
  exact congrArg Neg.neg (coneCornerHomology_projection faceArrow flagLabels
    flagAugmentation flagAugmentation_boundary)

end TernaryPoly.OrdinaryBoundaryActualEvaluation
