module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseContraction

@[expose] public section


/-! The actual symmetric exterior/contraction square equals the Hodge term at scale one quarter. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham ContinuousAlternatingMap
open scoped ContDiff Matrix.Norms.Elementwise

theorem exteriorOne_smul (c : ℝ) (a : OneCoordinates) : exteriorOne (c • a) = c • exteriorOne a := by
  funext i j
  simp [exteriorOne, smul_sub]

theorem contractionThree_smul (c : ℝ) (a : ThreeCoordinates) : contractionThree (c • a) = c • contractionThree a := by
  funext i j
  simp only [contractionThree, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change tangentWeight k • infinitesimal (tangentFrame k) (c • a k i j) =
    c • (tangentWeight k • infinitesimal (tangentFrame k) (a k i j))
  rw [Derivation.map_smul]
  exact smul_comm (tangentWeight k) c _

/-- The actual algebraic square, formed with the metric's inverse-Gram contraction. -/
def symmetricHodgeTwo (n : ℕ) (x : Coordinates) (a : FormValue n 2) : FormValue n 2 :=
  symmetricExterior n 1 x (symmetricContraction n 1 x a) +
    symmetricContraction n 2 x (symmetricExterior n 2 x a)

theorem baseThreeCoordinates_symmetricExterior (n : ℕ) (a : FormValue n 2) :
    baseThreeCoordinates (symmetricExterior n 2 (coordinateChart basepoint) a) =
      (1/2 : ℝ) • exteriorTwo (baseTwoCoordinates a) := by
  funext i j k
  exact symmetricExterior_two_basepoint n a i j k

theorem baseOneCoordinates_symmetricContraction (n : ℕ) (a : FormValue n 2) :
    (fun i => (symmetricContraction n 1 (coordinateChart basepoint) a ![baseFrame i]).val) =
      (1/2 : ℝ) • contractionTwo (baseTwoCoordinates a) := by
  funext i
  exact symmetricContraction_two_basepoint n a i

/-- Both genuine factors carry one half, so the complete degree-two algebraic Hodge term carries one quarter. -/
theorem symmetricHodgeTwo_basepoint_coordinates (n : ℕ) (a : FormValue n 2) :
    baseTwoCoordinates (symmetricHodgeTwo n (coordinateChart basepoint) a) =
      (1/4 : ℝ) • algebraicHodgeTwo (baseTwoCoordinates a) := by
  funext i j
  change ((symmetricExterior n 1 (coordinateChart basepoint) (symmetricContraction n 1 (coordinateChart basepoint) a)
      + symmetricContraction n 2 (coordinateChart basepoint) (symmetricExterior n 2 (coordinateChart basepoint) a))
      ![baseFrame i, baseFrame j]).val = _
  rw [ContinuousAlternatingMap.add_apply, Submodule.coe_add,
    symmetricExterior_one_basepoint, symmetricContraction_three_basepoint,
    baseOneCoordinates_symmetricContraction, baseThreeCoordinates_symmetricExterior,
    exteriorOne_smul, contractionThree_smul]
  change (1/2 : ℝ) • ((1/2 : ℝ) • exteriorOne (contractionTwo (baseTwoCoordinates a)) i j) +
      (1/2 : ℝ) • ((1/2 : ℝ) • contractionThree (exteriorTwo (baseTwoCoordinates a)) i j) =
      (1/4 : ℝ) • (exteriorOne (contractionTwo (baseTwoCoordinates a)) i j +
        contractionThree (exteriorTwo (baseTwoCoordinates a)) i j)
  module

/-- Literal homogeneous-coordinate intertwining, without assuming an inverse to baseTwoForm. -/
theorem baseTwoForm_symmetricHodgeTwo (n : ℕ) (a : FormValue n 2) :
    baseTwoForm n (symmetricHodgeTwo n (coordinateChart basepoint) a) =
      (1/4 : ℝ) • homogeneousHodgeTwo n (baseTwoForm n a) := by
  apply Subtype.ext
  exact symmetricHodgeTwo_basepoint_coordinates n a

end TernaryPoly.PolynomialFormGeometricEnergy
