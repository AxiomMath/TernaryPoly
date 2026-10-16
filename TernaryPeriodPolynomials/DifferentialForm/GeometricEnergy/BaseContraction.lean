module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Contraction

@[expose] public section


/-! Exact orthogonal-frame formulas for the actual metric contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham ContinuousAlternatingMap
open scoped ContDiff Matrix.Norms.Elementwise

theorem symmetricContraction_basepoint_apply (n k : ℕ) (a : FormValue n (k + 1))
    (v : Fin k → Coordinates) :
    symmetricContraction n k (coordinateChart basepoint) a v = ∑ i : Fin 5, tangentWeight i •
      ((1/2 : ℝ) • coefficientInfinitesimal n (tangentFrame i) (a (vecCons (baseFrame i) v))) := by
  rw [symmetricContraction_basepoint_frame]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change tangentWeight i • symmetricPart n (coordinateChart basepoint) (baseFrame i)
    (a (vecCons (baseFrame i) v)) = _
  rw [symmetricPart_baseFrame]
  rfl

/-- The actual metric contraction from degree two to one has exactly the same half scale. -/
theorem symmetricContraction_two_basepoint (n : ℕ) (a : FormValue n 2) (i : Fin 5) :
    (symmetricContraction n 1 (coordinateChart basepoint) a ![baseFrame i]).val =
      (1/2 : ℝ) • contractionTwo (baseTwoCoordinates a) i := by
  rw [symmetricContraction_basepoint_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, coefficientInfinitesimal_apply,
    contractionTwo, baseTwoCoordinates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  module

def baseThreeCoordinates {n : ℕ} (a : FormValue n 3) : ThreeCoordinates :=
  fun i j k => (a ![baseFrame i, baseFrame j, baseFrame k]).val

/-- The actual degree-three contraction agrees with the algebraic contraction at scale one half. -/
theorem symmetricContraction_three_basepoint (n : ℕ) (a : FormValue n 3) (i j : Fin 5) :
    (symmetricContraction n 2 (coordinateChart basepoint) a ![baseFrame i, baseFrame j]).val =
      (1/2 : ℝ) • contractionThree (baseThreeCoordinates a) i j := by
  rw [symmetricContraction_basepoint_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, coefficientInfinitesimal_apply,
    contractionThree, baseThreeCoordinates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  module

end TernaryPoly.PolynomialFormGeometricEnergy
