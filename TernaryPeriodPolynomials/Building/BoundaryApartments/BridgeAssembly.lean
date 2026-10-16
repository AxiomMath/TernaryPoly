module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.BoundaryDetection
public import TernaryPeriodPolynomials.Building.BoundaryApartments.IntegralFlagFrames

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

theorem polynomialBoundaryBridge_of_functional_inner {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (functional_property : IsPolynomialFunctional polynomial functional)
    (inner : InnerBoundary degree trivialCharacter .line
      (globalCoordinates degree trivialCharacter
        (pathCocycle functional_property specialPaths_isPathFamily)).2) :
    PolynomialBoundaryBridge polynomial := by
  let cocycle := pathCocycle functional_property specialPaths_isPathFamily
  have realizes := pathCocycle_realizes functional_property specialPaths_isPathFamily
  have pure := specialPathCocycle_pureMixed functional_property
  have coordinate_A := mixedBernoulliCoordinate_binaryA functional_property realizes
  have coordinate_B := mixedBernoulliCoordinate_binaryB realizes
  have coordinate_R := mixedBernoulliCoordinate_binaryR realizes
  refine ⟨functional, specialPaths, cocycle, functional_property, specialPaths_isPathFamily,
    realizes, ?_, pathCocycle_goodBoundaryVanishing functional_property specialPaths_isPathFamily,
    inner, pure, coordinate_A, coordinate_B, coordinate_R, ?_⟩
  · intro other_paths other_cocycle other_paths_good other_realizes
    exact realizesPathClass_class_independent functional_property other_paths_good
      specialPaths_isPathFamily other_realizes realizes
  · exact bernoulliObstruction_of_lineClass_zero degree_positive solution cocycle pure
      coordinate_A coordinate_B coordinate_R

theorem polynomialBoundaryBridge_of_functional {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (functional_property : IsPolynomialFunctional polynomial functional) :
    PolynomialBoundaryBridge polynomial :=
  polynomialBoundaryBridge_of_functional_inner degree_positive solution functional
    functional_property (pathCocycle_innerBoundary degree_positive solution functional_property)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
