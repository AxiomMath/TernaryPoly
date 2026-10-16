module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Paths
public import TernaryPeriodPolynomials.Building.BoundaryApartments.PathIndependence

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous MvPolynomial

theorem bernoulliOperator_zero (degree : ℕ) (parameter : Poly) :
    bernoulliOperator degree parameter 0 = 0 := by
  have derivative_zero : (fun polynomial : Poly => pderiv 0 polynomial) 0 = 0 :=
    map_zero _
  simp [bernoulliOperator, Function.iterate_fixed derivative_zero]

theorem bernoulliObstruction_zero (degree : ℕ) :
    bernoulliObstruction (0 : HomogeneousPoly degree) = 0 := by
  simp [bernoulliObstruction, bernoulliOperator_zero]

theorem zero_isPolynomialFunctional (degree : ℕ) :
    IsPolynomialFunctional (0 : HomogeneousPoly degree) 0 := by
  constructor
  · intro matrix chain _
    simp
  · intro frame _
    simp

theorem goodBoundaryVanishing_zero (degree : ℕ) :
    GoodBoundaryVanishing degree trivialCharacter
      (globalCoordinates degree trivialCharacter 0) := by
  constructor <;>
    refine ⟨restrictionCocycle degree trivialCharacter _ 0, rfl, 0, ?_⟩ <;>
    intro vertices flag _ <;> simp [restrictionCocycle]

theorem innerBoundary_zero (degree : ℕ) (side : Side) :
    InnerBoundary degree trivialCharacter side
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) side)
        (restrictionCocycle degree trivialCharacter side 0)) := by
  refine ⟨restrictionCocycle degree trivialCharacter side 0, rfl, 0, ?_⟩
  intro vertices edge
  simp [restrictionCocycle]

theorem zero_realizesPathClass (degree : ℕ) (paths : rationalLevel → EdgeChains) :
    RealizesPathClass (0 : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) paths 0 := by
  intro first second third
  simp

theorem pureMixedBadLine_zero (degree : ℕ) :
    PureMixedBadLine (0 : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter)) := by
  constructor
  · intro first second third fourth
    rfl
  · intro first second _ _
    rfl

theorem mixedBernoulliCoordinate_zero (degree : ℕ) (matrix : RationalGL3) :
    mixedBernoulliCoordinate (0 : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter)) matrix = 0 := by
  simp [mixedBernoulliCoordinate, mixedBarEdge, bernoulliOperator_zero]

theorem polynomialBoundaryBridge_zero (degree : ℕ) :
    PolynomialBoundaryBridge (0 : HomogeneousPoly degree) := by
  refine ⟨0, goodPaths, 0, zero_isPolynomialFunctional degree,
    goodPaths_isPathFamily, zero_realizesPathClass degree goodPaths, ?_,
    goodBoundaryVanishing_zero degree, innerBoundary_zero degree .line,
    pureMixedBadLine_zero degree, ?_, mixedBernoulliCoordinate_zero degree binaryB,
    mixedBernoulliCoordinate_zero degree binaryR, ?_⟩
  · intro paths cocycle paths_good cocycle_realizes
    exact realizesPathClass_class_independent (zero_isPolynomialFunctional degree)
      paths_good goodPaths_isPathFamily cocycle_realizes
      (zero_realizesPathClass degree goodPaths)
  · rw [mixedBernoulliCoordinate_zero, bernoulliObstruction_zero, neg_zero]
  · intro _
    exact bernoulliObstruction_zero degree

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
