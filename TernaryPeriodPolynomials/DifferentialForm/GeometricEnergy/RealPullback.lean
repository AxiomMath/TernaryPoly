module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.RealContraction

@[expose] public section

/-! Actual inverse-substitution pullback of coefficient-valued forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem realCoefficientMap_inverse (n : ℕ) (g : RealGL) (p : Coefficients n) :
    realCoefficientMap n g (realCoefficientMap n g⁻¹ p) = p := by
  change coefficientSubstitution n g.val⁻¹ (coefficientSubstitution n (g⁻¹).val⁻¹ p) = p
  simp only [← Matrix.coe_units_inv, inv_inv]
  rw [coefficientSubstitution_mul]
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, coefficientSubstitution_one]

/-- Pull back tangent slots and undo the coefficient action by actual inverse substitution. -/
def realFormPullback (n k : ℕ) (g : RealGL) (x : Coordinates) (a : FormValue n k) : FormValue n k :=
  coefficientFormMap (realCoefficientMap n g⁻¹) k
    (a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x))

theorem realFormPullback_spec (n k : ℕ) (g : RealGL) (x : Coordinates) (a : FormValue n k) :
    a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k (realFormPullback n k g x a) := by
  apply ContinuousAlternatingMap.ext
  intro v
  change a (fun i => fderiv ℝ (coordinateAction g) x (v i)) =
    realCoefficientMap n g (realCoefficientMap n g⁻¹ (a (fun i => fderiv ℝ (coordinateAction g) x (v i))))
  rw [realCoefficientMap_inverse]

theorem realFormPullback_pairing (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (a b : FormValue n k) :
    formPairing n k (coordinateAction g x) a b =
      formPairing n k x (realFormPullback n k g x a) (realFormPullback n k g x b) :=
  formPairing_real n k g hg x hx a b _ _ (realFormPullback_spec n k g x a) (realFormPullback_spec n k g x b)

end TernaryPoly.PolynomialFormGeometricEnergy
