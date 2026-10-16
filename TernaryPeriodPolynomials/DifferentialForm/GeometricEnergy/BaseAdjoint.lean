module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseMetric

@[expose] public section


/-! Actual basepoint adjoints for symmetric exterior multiplication and metric contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric
open SymmetricSpaceCharts SymmetricSpaceCovering

theorem onePairing_smul_left (c : ℝ) (a b : OneCoordinates) :
    onePairing (c • a) b = c * onePairing a b := by
  simp [onePairing, Finset.mul_sum, mul_left_comm]

theorem onePairing_smul_right (c : ℝ) (a b : OneCoordinates) :
    onePairing a (c • b) = c * onePairing a b := by
  simp [onePairing, Finset.mul_sum, mul_left_comm]

theorem twoPairing_smul_right (c : ℝ) (a b : TwoCoordinates) :
    twoPairing a (c • b) = c * twoPairing a b := by
  rw [twoPairing_symmetric, twoPairing_smul_left, twoPairing_symmetric b a]

theorem threePairing_smul_left (c : ℝ) (a b : ThreeCoordinates) :
    threePairing (c • a) b = c * threePairing a b := by
  simp [threePairing, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem threePairing_smul_right (c : ℝ) (a b : ThreeCoordinates) :
    threePairing a (c • b) = c * threePairing a b := by
  simp [threePairing, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem baseThreeCoordinates_alternating {n : ℕ} (a : FormValue n 3) :
    IsAlternatingThree (baseThreeCoordinates a) := by
  constructor
  · intro i j k
    have h := a.toAlternatingMap.map_swap ![baseFrame j,baseFrame i,baseFrame k]
      (show (0 : Fin 3) ≠ 1 by decide)
    have he : (![baseFrame j,baseFrame i,baseFrame k] ∘ Equiv.swap (0 : Fin 3) 1) =
        ![baseFrame i,baseFrame j,baseFrame k] := by
      funext r; fin_cases r <;> rfl
    rw [he] at h
    exact congrArg Subtype.val h
  · intro i j k
    have h := a.toAlternatingMap.map_swap ![baseFrame i,baseFrame j,baseFrame k]
      (show (0 : Fin 3) ≠ 2 by decide)
    have he : (![baseFrame i,baseFrame j,baseFrame k] ∘ Equiv.swap (0 : Fin 3) 2) =
        ![baseFrame k,baseFrame j,baseFrame i] := by
      funext r; fin_cases r <;> rfl
    rw [he] at h
    have g := a.toAlternatingMap.map_swap ![baseFrame k,baseFrame j,baseFrame i]
      (show (1 : Fin 3) ≠ 2 by decide)
    have ge : (![baseFrame k,baseFrame j,baseFrame i] ∘ Equiv.swap (1 : Fin 3) 2) =
        ![baseFrame k,baseFrame i,baseFrame j] := by
      funext r; fin_cases r <;> rfl
    rw [ge, h, neg_neg] at g
    exact congrArg Subtype.val g.symm

theorem baseTwoCoordinates_symmetricExterior (n : ℕ) (a : FormValue n 1) :
    baseTwoCoordinates (symmetricExterior n 1 (coordinateChart basepoint) a) =
      (1/2 : ℝ) • exteriorOne (baseOneCoordinates a) := by
  funext i j
  exact symmetricExterior_one_basepoint n a i j

theorem baseTwoCoordinates_symmetricContraction (n : ℕ) (a : FormValue n 3) :
    baseTwoCoordinates (symmetricContraction n 2 (coordinateChart basepoint) a) =
      (1/2 : ℝ) • contractionThree (baseThreeCoordinates a) := by
  funext i j
  exact symmetricContraction_three_basepoint n a i j

/-- Literal adjointness for the metric and the actual inverse-Gram contraction. -/
theorem symmetricExterior_one_basepoint_adjoint (n : ℕ) (a : FormValue n 1) (b : FormValue n 2) :
    formPairing n 2 (coordinateChart basepoint) (symmetricExterior n 1 (coordinateChart basepoint) a) b =
      formPairing n 1 (coordinateChart basepoint) a (symmetricContraction n 1 (coordinateChart basepoint) b) := by
  rw [formPairing_basepoint_two, formPairing_basepoint_one, baseTwoCoordinates_symmetricExterior,
    twoPairing_smul_left, exteriorOne_contractionTwo_adjoint _ _ (baseTwoCoordinates_alternating b)]
  change _ = onePairing (baseOneCoordinates a)
    (fun i => (symmetricContraction n 1 (coordinateChart basepoint) b ![baseFrame i]).val)
  rw [baseOneCoordinates_symmetricContraction, onePairing_smul_right]

/-- Literal adjointness in the upper adjacent degree. -/
theorem symmetricExterior_two_basepoint_adjoint (n : ℕ) (a : FormValue n 2) (b : FormValue n 3) :
    formPairing n 3 (coordinateChart basepoint) (symmetricExterior n 2 (coordinateChart basepoint) a) b =
      formPairing n 2 (coordinateChart basepoint) a (symmetricContraction n 2 (coordinateChart basepoint) b) := by
  rw [formPairing_basepoint_three, formPairing_basepoint_two, baseThreeCoordinates_symmetricExterior,
    threePairing_smul_left, exteriorTwo_contractionThree_adjoint _ _ (baseThreeCoordinates_alternating b),
    baseTwoCoordinates_symmetricContraction, twoPairing_smul_right]

end TernaryPoly.PolynomialFormGeometricEnergy
