module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.CoordinateApartment
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullStabilizers

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory ModThreeGoodAction GoodApartmentCycles
open OrdinaryTopBoundaryComparison OrdinaryApartmentPresentation OrdinaryCoordinateApartment
open ReferenceCoefficientMatrices SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFaceAugmentation
open SymmetricSpaceBoundaryIncidenceHomology

/-- The standard full-integral flag is literally the coordinate ordinary flag. -/
theorem standardFlag_coordinate : standardFlag = OrdinaryCoordinateFlag.flag := rfl

/-- The column lines used by the ordinary identity frame are the same coordinate lines as the Good apartment. -/
theorem identityColumn_coordinate (j : Fin 3) :
    OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 j.castSucc) =
      OrdinaryIncidence.goodLine (ReferenceApartmentRelations.coordinateLine j) := by
  apply Subtype.ext
  exact IntegralFrameHeightReduction.columnLine_span 1 j

/-- The ordinary identity apartment is literally the included Good reference apartment. -/
theorem identityApartment_reference : identityApartment =
    OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment := by
  rw [identityApartment, frameCycle_apartment]
  apply Subtype.ext
  change apartmentChain (fun _ => True)
    (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 0))
    (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 1))
    (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 2)) =
      inclusion (apartmentChain Good (ReferenceApartmentRelations.coordinateLine 0)
        (ReferenceApartmentRelations.coordinateLine 1) (ReferenceApartmentRelations.coordinateLine 2))
  erw [include_apartment, identityColumn_coordinate 0, identityColumn_coordinate 1, identityColumn_coordinate 2]

/-- The identity apartment has the literal six-flag coordinate expression with the prescribed orientation. -/
theorem identityApartment_hexagon : identityApartment.val =
    OrdinaryCoordinateApartment.segment + OrdinaryIncidenceChains.edgeRepresentation cK OrdinaryCoordinateApartment.segment +
      OrdinaryIncidenceChains.edgeRepresentation cK (OrdinaryIncidenceChains.edgeRepresentation cK OrdinaryCoordinateApartment.segment) := by
  rw [identityApartment_reference]
  exact reference_eq_hexagon

/-- The full integral flag action agrees with the K edge action for the same matrix. -/
theorem fullFlag_action_K (g : K) (F : SymmetricSpaceBoundaryMV.Flag) :
    g.val • F = OrdinaryIncidenceChains.edgeAction g F := rfl

/-- The full action on single flag labels retains exactly the ordinary edge representation. -/
theorem fullFlag_single_edge (g : K) :
    edgeCoefficients (MonoidAlgebra.single (g.val • standardFlag) (1 : ℚ)) =
      OrdinaryIncidenceChains.edgeRepresentation g OrdinaryCoordinateFlag.flagChain := by
  rw [edgeCoefficients_single, fullFlag_action_K, standardFlag_coordinate]
  exact (OrdinaryIncidenceChains.edgeRepresentation_single g OrdinaryCoordinateFlag.flag 1).symm

end TernaryPoly.OrdinaryBoundaryActualEvaluation
