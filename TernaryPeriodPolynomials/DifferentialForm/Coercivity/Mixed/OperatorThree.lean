module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DivergenceThree
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.MixedOperator

@[expose] public section



/-! Degree-3 specialization of the compact mixed operator and the descended energy-current
divergence, mirroring `compactMixedOperator`/`compactCurrentDivergence`
(`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/MixedOperator.lean`) one level up: a genuine two-term
anticommutator (both `compactSymmetricContraction n 3 ∘ compactCovariantExterior n 3` and
`compactCovariantExterior n 2 ∘ compactSymmetricContraction n 2` survive, unlike the degree-4/5
one-term case `MixedOperatorFour.lean`), using `compactCovariantExterior_apply` (generic in `k`,
already proved in `TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/MixedOperator.lean`) and the degree-3
current-divergence formula `weightedDivergence_energyCurrent_three`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise ContDiff

/-- The compact anticommutator at degree 3 (output degree 3), mirroring `compactMixedOperator`. -/
def compactMixedOperatorThree (n : ℕ) (a : Core n 3) : Core n 3 :=
  compactSymmetricContraction n 3 (compactCovariantExterior n 3 a) +
    compactCovariantExterior n 2 (compactSymmetricContraction n 2 a)

theorem compactMixedOperatorThree_apply (n : ℕ) (a : Core n 3) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactMixedOperatorThree n a).val.val.val x =
      symmetricContraction n 3 x (covariantExterior n 3 a.val.val.val x) +
        covariantExterior n 2 (fun y => symmetricContraction n 2 y (a.val.val.val y)) x := by
  change (compactSymmetricContraction n 3 (compactCovariantExterior n 3 a)).val.val.val x +
    (compactCovariantExterior n 2 (compactSymmetricContraction n 2 a)).val.val.val x = _
  apply congrArg₂ (· + ·)
  · exact (compactSymmetricContraction_apply n 3 _ x).trans
      (congrArg (symmetricContraction n 3 x) (compactCovariantExterior_apply n 3 a x hx))
  · exact (compactCovariantExterior_apply n 2 _ x hx).trans
      (congrArg (fun w => covariantExterior n 2 w x) (funext (compactSymmetricContraction_apply n 2 a)))

/-- A genuine smooth descended scalar at degree 3, mirroring `compactCurrentDivergence`. -/
def compactCurrentDivergenceThree (n : ℕ) (a : Core n 3) (q : OrbitSpace) : ℝ :=
  2 * scalarPairing n 3 a.val (compactMixedOperatorThree n a).val q

theorem continuous_compactCurrentDivergenceThree (n : ℕ) (a : Core n 3) :
    Continuous (compactCurrentDivergenceThree n a) :=
  continuous_const.mul (continuous_scalarPairing n 3 a.val (compactMixedOperatorThree n a).val)

theorem compactCurrentDivergenceThree_coordinateProjection (n : ℕ) (a : Core n 3)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    compactCurrentDivergenceThree n a (coordinateProjection x) =
      weightedDivergence (energyCurrent n 3 a.val.val.val) x := by
  calc
    _ = 2 * formPairing n 3 x (a.val.val.val x) ((compactMixedOperatorThree n a).val.val.val x) :=
      congrArg (2 * ·) (scalarPairing_coordinateProjection n 3 a.val (compactMixedOperatorThree n a).val x hx)
    _ = 2 * formPairing n 3 x (a.val.val.val x)
        (symmetricContraction n 3 x (covariantExterior n 3 a.val.val.val x) +
          covariantExterior n 2 (fun y => symmetricContraction n 2 y (a.val.val.val y)) x) :=
      congrArg (fun z => 2 * formPairing n 3 x (a.val.val.val x) z) (compactMixedOperatorThree_apply n a x hx)
    _ = _ := (weightedDivergence_energyCurrent_three n
      (by simpa only [liftedDomain_univ] using Form.smooth a.val.val) x hx).symm

end TernaryPeriodPolynomials.Argument.Coercivity
