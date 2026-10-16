module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineHomogeneousBoundary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineCoefficientPolynomial (degree : ℕ) : goodLineCoefficientRep degree →ₗ[ℂ] HomogeneousPoly degree :=
  LinearMap.id

def lowerRadicalLatticeContribution (degree : ℕ) (coordinate : Fin 2) :
    HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (lowerRadicalCoordinate degree).comp
    ((LinearMap.single ℂ (fun _ : Fin 2 => HomogeneousPoly degree) coordinate).comp
      (lowerRadicalAverageEquiv degree coordinate).symm.toLinearMap)

theorem lowerRadicalCoordinate_averages (degree : ℕ) (pair : Fin 2 → HomogeneousPoly degree) :
    lowerRadicalCoordinate degree (fun coordinate => (lowerRadicalAverageEquiv degree coordinate).symm (pair coordinate)) =
      lowerRadicalLatticeContribution degree 0 (pair 0) + lowerRadicalLatticeContribution degree 1 (pair 1) := by
  change lowerRadicalCoordinate degree _ =
    lowerRadicalCoordinate degree (Pi.single 0 ((lowerRadicalAverageEquiv degree 0).symm (pair 0))) +
      lowerRadicalCoordinate degree (Pi.single 1 ((lowerRadicalAverageEquiv degree 1).symm (pair 1)))
  rw [← map_add]
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp

/-- The mixed lower-radical coordinate on an arbitrary group two-cochain. -/
def goodLineMixedCoordinate (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    ((flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
      flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) → goodLineCoefficientRep degree) →ₗ[ℂ]
        Binary.HomogeneousPoly (degree + 1) :=
  (lowerRadicalCoordinate degree).comp (LinearMap.pi (fun coordinate : Fin 2 =>
    ((lowerRadicalAverageEquiv degree coordinate).symm.toLinearMap.comp (goodLineCoefficientPolynomial degree)).comp
      ((LinearMap.proj (R := ℂ) (φ := fun _ => goodLineCoefficientRep degree) (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate)))) -
        LinearMap.proj (R := ℂ) (φ := fun _ => goodLineCoefficientRep degree)
          (goodLineRadicalInclusion (radicalLatticeGenerator coordinate), goodLineLeviSection matrix))))

theorem goodLineMixedCoordinate_edge (degree : ℕ) (positive : 0 < degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCoordinate degree matrix (fun pair => cycle.val pair) =
      goodLineBinaryEdgeCycle degree positive cycle matrix :=
  (goodLineBinaryEdgeCycle_value degree positive cycle matrix).symm

theorem goodLineMixedCoordinate_correction (degree : ℕ) (positive : 0 < degree)
    (cochain : (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
      flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) → goodLineCoefficientRep degree)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (formula : ∀ pair, cycle.val pair = cochain pair -
      twoBoundaryCycle (goodLineCoefficientRep degree) primitive pair)
    (zero : ∀ matrix : GeneralLinearGroup (Fin 2) ℤ, goodLineBinaryEdgeCycle degree positive cycle matrix = 0)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCoordinate degree matrix cochain =
      goodLineMixedCoordinate degree matrix (fun pair => twoBoundaryCycle (goodLineCoefficientRep degree) primitive pair) := by
  have difference : (fun pair => cycle.val pair) =
      cochain - (fun pair => twoBoundaryCycle (goodLineCoefficientRep degree) primitive pair) :=
    funext formula
  have value := (goodLineMixedCoordinate_edge degree positive cycle matrix).trans (zero matrix)
  rw [difference, map_sub] at value
  exact sub_eq_zero.mp value

theorem goodLineMixedCoordinate_contributions (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cochain : (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
      flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) → goodLineCoefficientRep degree) :
    goodLineMixedCoordinate degree matrix cochain =
      lowerRadicalLatticeContribution degree 0
        (goodLineCoefficientPolynomial degree
          (cochain (goodLineLeviSection matrix, goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeFirst)) -
            cochain (goodLineRadicalInclusion radicalLatticeFirst, goodLineLeviSection matrix))) +
      lowerRadicalLatticeContribution degree 1
        (goodLineCoefficientPolynomial degree
          (cochain (goodLineLeviSection matrix, goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeSecond)) -
            cochain (goodLineRadicalInclusion radicalLatticeSecond, goodLineLeviSection matrix))) :=
  lowerRadicalCoordinate_averages degree (fun coordinate => goodLineCoefficientPolynomial degree
    (cochain (goodLineLeviSection matrix,
        goodLineRadicalInclusion (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate))) -
      cochain (goodLineRadicalInclusion (radicalLatticeGenerator coordinate), goodLineLeviSection matrix)))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
