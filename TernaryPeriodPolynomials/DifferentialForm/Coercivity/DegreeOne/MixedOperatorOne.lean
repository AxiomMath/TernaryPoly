module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.DivergenceOne
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.MixedOperator

@[expose] public section



/-! Degree-1 specialization of the compact mixed operator and the descended energy-current
divergence, mirroring `compactMixedOperatorThree`/`compactCurrentDivergenceThree`
(`TernaryPeriodPolynomials.Argument.Coercivity.MixedOperatorThree`, read-only reference)
one level down: a genuine two-term anticommutator (both
`compactSymmetricContraction n 1 ∘ compactCovariantExterior n 1` and
`compactCovariantExterior n 0 ∘ compactSymmetricContraction n 0` survive, unlike the degree-0
one-term edge case `MixedOperator.lean`), using `compactCovariantExterior_apply`/
`compactSymmetricContraction_apply` (both generic in `k`, already proved in
`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/MixedOperator.lean`) and the degree-1 current-divergence
formula `weightedDivergence_energyCurrent_one` from `DivergenceOne.lean`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise ContDiff

/-- The compact anticommutator at degree 1 (output degree 1), mirroring
`compactMixedOperatorThree`. -/
def compactMixedOperatorOne (n : ℕ) (a : Core n 1) : Core n 1 :=
  compactSymmetricContraction n 1 (compactCovariantExterior n 1 a) +
    compactCovariantExterior n 0 (compactSymmetricContraction n 0 a)

theorem compactMixedOperatorOne_apply (n : ℕ) (a : Core n 1) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactMixedOperatorOne n a).val.val.val x =
      symmetricContraction n 1 x (covariantExterior n 1 a.val.val.val x) +
        covariantExterior n 0 (fun y => symmetricContraction n 0 y (a.val.val.val y)) x := by
  change (compactSymmetricContraction n 1 (compactCovariantExterior n 1 a)).val.val.val x +
    (compactCovariantExterior n 0 (compactSymmetricContraction n 0 a)).val.val.val x = _
  apply congrArg₂ (· + ·)
  · exact (compactSymmetricContraction_apply n 1 _ x).trans
      (congrArg (symmetricContraction n 1 x) (compactCovariantExterior_apply n 1 a x hx))
  · exact (compactCovariantExterior_apply n 0 _ x hx).trans
      (congrArg (fun w => covariantExterior n 0 w x) (funext (compactSymmetricContraction_apply n 0 a)))

/-- A genuine smooth descended scalar at degree 1, mirroring `compactCurrentDivergenceThree`. -/
def compactCurrentDivergenceOne (n : ℕ) (a : Core n 1) (q : OrbitSpace) : ℝ :=
  2 * scalarPairing n 1 a.val (compactMixedOperatorOne n a).val q

theorem continuous_compactCurrentDivergenceOne (n : ℕ) (a : Core n 1) :
    Continuous (compactCurrentDivergenceOne n a) :=
  continuous_const.mul (continuous_scalarPairing n 1 a.val (compactMixedOperatorOne n a).val)

theorem compactCurrentDivergenceOne_coordinateProjection (n : ℕ) (a : Core n 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    compactCurrentDivergenceOne n a (coordinateProjection x) =
      weightedDivergence (energyCurrent n 1 a.val.val.val) x := by
  calc
    _ = 2 * formPairing n 1 x (a.val.val.val x) ((compactMixedOperatorOne n a).val.val.val x) :=
      congrArg (2 * ·) (scalarPairing_coordinateProjection n 1 a.val (compactMixedOperatorOne n a).val x hx)
    _ = 2 * formPairing n 1 x (a.val.val.val x)
        (symmetricContraction n 1 x (covariantExterior n 1 a.val.val.val x) +
          covariantExterior n 0 (fun y => symmetricContraction n 0 y (a.val.val.val y)) x) :=
      congrArg (fun z => 2 * formPairing n 1 x (a.val.val.val x) z) (compactMixedOperatorOne_apply n a x hx)
    _ = _ := (weightedDivergence_energyCurrent_one n
      (by simpa only [liftedDomain_univ] using Form.smooth a.val.val) x hx).symm

end TernaryPeriodPolynomials.Argument.CoercivityOne
