module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Boundary
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Boundary

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

theorem pathCoordinatePackage {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    ∃ (paths : rationalLevel → EdgeChains)
      (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)),
      IsPathFamily paths ∧ RealizesPathClass functional paths cocycle ∧
      (∀ other_paths other_cocycle, IsPathFamily other_paths →
        RealizesPathClass functional other_paths other_cocycle →
        classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter) other_cocycle =
          classOf rationalLevel (rationalCoefficientComponent degree trivialCharacter) cocycle) ∧
      GoodBoundaryVanishing degree trivialCharacter
        (globalCoordinates degree trivialCharacter cocycle) ∧
      PureMixedBadLine cocycle ∧
      mixedBernoulliCoordinate cocycle binaryA = -bernoulliObstruction polynomial ∧
      mixedBernoulliCoordinate cocycle binaryB = 0 ∧
      mixedBernoulliCoordinate cocycle binaryR = 0 := by
  refine ⟨specialPaths, pathCocycle functional_property specialPaths_isPathFamily,
    specialPaths_isPathFamily, pathCocycle_realizes functional_property specialPaths_isPathFamily,
    ?_, pathCocycle_goodBoundaryVanishing functional_property specialPaths_isPathFamily,
    specialPathCocycle_pureMixed functional_property,
    mixedBernoulliCoordinate_binaryA functional_property
      (pathCocycle_realizes functional_property specialPaths_isPathFamily),
    mixedBernoulliCoordinate_binaryB
      (pathCocycle_realizes functional_property specialPaths_isPathFamily),
    mixedBernoulliCoordinate_binaryR
      (pathCocycle_realizes functional_property specialPaths_isPathFamily)⟩
  intro other_paths other_cocycle other_paths_good other_realizes
  exact realizesPathClass_class_independent functional_property
    other_paths_good specialPaths_isPathFamily other_realizes
    (pathCocycle_realizes functional_property specialPaths_isPathFamily)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
