module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Divergence

@[expose] public section



/-! Degree-0 specialization of the compact mixed operator and the descended energy-current
divergence: a single term (no `compactSymmetricContraction n (-1)` cross term exists). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
open TernaryPoly.SmoothLocalDeRham Set
open scoped ContDiff Matrix.Norms.Elementwise

/-- Actual compact anticommutator at degree 0, a single term. -/
def compactMixedOperatorZero (n : ℕ) (a : Core n 0) : Core n 0 :=
  compactSymmetricContraction n 0 (compactCovariantExterior n 0 a)

theorem compactMixedOperatorZero_apply (n : ℕ) (a : Core n 0) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactMixedOperatorZero n a).val.val.val x =
      symmetricContraction n 0 x (covariantExterior n 0 a.val.val.val x) := by
  change (compactSymmetricContraction n 0 (compactCovariantExterior n 0 a)).val.val.val x = _
  exact (compactSymmetricContraction_apply n 0 _ x).trans
    (congrArg (symmetricContraction n 0 x) (compactCovariantExterior_apply n 0 a x hx))

/-- A genuine smooth descended scalar at degree 0. -/
def compactCurrentDivergenceZero (n : ℕ) (a : Core n 0) (q : OrbitSpace) : ℝ :=
  2 * scalarPairing n 0 a.val (compactMixedOperatorZero n a).val q

theorem continuous_compactCurrentDivergenceZero (n : ℕ) (a : Core n 0) :
    Continuous (compactCurrentDivergenceZero n a) :=
  continuous_const.mul (continuous_scalarPairing n 0 a.val (compactMixedOperatorZero n a).val)

theorem compactCurrentDivergenceZero_coordinateProjection (n : ℕ) (a : Core n 0)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    compactCurrentDivergenceZero n a (coordinateProjection x) =
      weightedDivergence (energyCurrent n 0 a.val.val.val) x := by
  calc
    _ = 2 * formPairing n 0 x (a.val.val.val x) ((compactMixedOperatorZero n a).val.val.val x) :=
      congrArg (2 * ·) (scalarPairing_coordinateProjection n 0 a.val (compactMixedOperatorZero n a).val x hx)
    _ = 2 * formPairing n 0 x (a.val.val.val x)
        (symmetricContraction n 0 x (covariantExterior n 0 a.val.val.val x)) :=
      congrArg (fun z => 2 * formPairing n 0 x (a.val.val.val x) z) (compactMixedOperatorZero_apply n a x hx)
    _ = _ := (weightedDivergence_energyCurrent_zero n
      (by simpa only [liftedDomain_univ] using Form.smooth a.val.val) x hx).symm

end TernaryPeriodPolynomials.Argument.Coercivity
