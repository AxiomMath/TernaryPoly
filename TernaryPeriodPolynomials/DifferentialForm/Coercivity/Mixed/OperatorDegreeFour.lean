module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DivergenceDegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.MixedOperator

@[expose] public section



/-! Degree-4 specialization of the compact mixed operator and the descended energy-current
divergence, mirroring `compactMixedOperatorThree`/`compactCurrentDivergenceThree`
(`MixedOperatorThree.lean`) one level up: a genuine two-term anticommutator (both
`compactSymmetricContraction n 4 ∘ compactCovariantExterior n 4` and
`compactCovariantExterior n 3 ∘ compactSymmetricContraction n 3` survive), using
`compactCovariantExterior_apply` (generic in `k`, already proved in
`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/MixedOperator.lean`) and the degree-4 current-divergence
formula `weightedDivergence_energyCurrent_four`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-4 compact mixed operator, mirroring `compactMixedOperatorThree` one level up. -/
def compactMixedOperatorDegreeFour (n : ℕ) (a : Core n 4) : Core n 4 :=
  compactSymmetricContraction n 4 (compactCovariantExterior n 4 a) +
    compactCovariantExterior n 3 (compactSymmetricContraction n 3 a)

theorem compactMixedOperatorDegreeFour_apply (n : ℕ) (a : Core n 4) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactMixedOperatorDegreeFour n a).val.val.val x =
      symmetricContraction n 4 x (covariantExterior n 4 a.val.val.val x) +
        covariantExterior n 3 (fun y => symmetricContraction n 3 y (a.val.val.val y)) x := by
  change (compactSymmetricContraction n 4 (compactCovariantExterior n 4 a)).val.val.val x +
    (compactCovariantExterior n 3 (compactSymmetricContraction n 3 a)).val.val.val x = _
  apply congrArg₂ (· + ·)
  · exact (compactSymmetricContraction_apply n 4 _ x).trans
      (congrArg (symmetricContraction n 4 x) (compactCovariantExterior_apply n 4 a x hx))
  · exact (compactCovariantExterior_apply n 3 _ x hx).trans
      (congrArg (fun w => covariantExterior n 3 w x) (funext (compactSymmetricContraction_apply n 3 a)))

def compactCurrentDivergenceDegreeFour (n : ℕ) (a : Core n 4) (q : OrbitSpace) : ℝ :=
  2 * scalarPairing n 4 a.val (compactMixedOperatorDegreeFour n a).val q

theorem continuous_compactCurrentDivergenceDegreeFour (n : ℕ) (a : Core n 4) :
    Continuous (compactCurrentDivergenceDegreeFour n a) :=
  continuous_const.mul (continuous_scalarPairing n 4 a.val (compactMixedOperatorDegreeFour n a).val)

theorem compactCurrentDivergenceDegreeFour_coordinateProjection (n : ℕ) (a : Core n 4)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    compactCurrentDivergenceDegreeFour n a (coordinateProjection x) =
      weightedDivergence (energyCurrent n 4 a.val.val.val) x := by
  calc
    _ = 2 * formPairing n 4 x (a.val.val.val x) ((compactMixedOperatorDegreeFour n a).val.val.val x) :=
      congrArg (2 * ·) (scalarPairing_coordinateProjection n 4 a.val (compactMixedOperatorDegreeFour n a).val x hx)
    _ = 2 * formPairing n 4 x (a.val.val.val x)
        (symmetricContraction n 4 x (covariantExterior n 4 a.val.val.val x) +
          covariantExterior n 3 (fun y => symmetricContraction n 3 y (a.val.val.val y)) x) :=
      congrArg (fun z => 2 * formPairing n 4 x (a.val.val.val x) z) (compactMixedOperatorDegreeFour_apply n a x hx)
    _ = _ := (weightedDivergence_energyCurrent_four n
      (by simpa only [liftedDomain_univ] using Form.smooth a.val.val) x hx).symm

end TernaryPeriodPolynomials.Argument.Coercivity
