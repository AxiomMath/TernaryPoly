module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Splitting
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDivergence

@[expose] public section


/-! The exact compact mixed operator and the actual descended energy-current divergence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates PolynomialFormHilbert
open PolynomialFormConnection SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham Set
open scoped ContDiff Matrix.Norms.Elementwise

theorem compactCovariantExterior_apply (n k : ℕ) (a : Core n k) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactCovariantExterior n k a).val.val.val x = covariantExterior n k a.val.val.val x := by
  change (d (liftedDomain_isOpen isOpen_univ) k a.val.val).val x -
    (compactSymmetricExterior n k a).val.val.val x = _
  exact congrArg₂ (· - ·)
    (d_apply (liftedDomain_isOpen isOpen_univ) a.val.val
      (show x ∈ liftedDomain (Set.univ : Set OrbitSpace) from ⟨hx, mem_univ _⟩))
    (compactSymmetricExterior_apply n k a x)

/-- Actual compact anticommutator, assembled from already equivariant compact operators. -/
def compactMixedOperator (n : ℕ) (a : Core n 2) : Core n 2 :=
  compactSymmetricContraction n 2 (compactCovariantExterior n 2 a) +
    compactCovariantExterior n 1 (compactSymmetricContraction n 1 a)

theorem compactMixedOperator_apply (n : ℕ) (a : Core n 2) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactMixedOperator n a).val.val.val x =
      symmetricContraction n 2 x (covariantExterior n 2 a.val.val.val x) +
        covariantExterior n 1 (fun y => symmetricContraction n 1 y (a.val.val.val y)) x := by
  change (compactSymmetricContraction n 2 (compactCovariantExterior n 2 a)).val.val.val x +
    (compactCovariantExterior n 1 (compactSymmetricContraction n 1 a)).val.val.val x = _
  apply congrArg₂ (· + ·)
  · exact (compactSymmetricContraction_apply n 2 _ x).trans
      (congrArg (symmetricContraction n 2 x) (compactCovariantExterior_apply n 2 a x hx))
  · exact (compactCovariantExterior_apply n 1 _ x hx).trans
      (congrArg (fun w => covariantExterior n 1 w x) (funext (compactSymmetricContraction_apply n 1 a)))

/-- A genuine smooth descended scalar, defined from actual compact equivariant forms. -/
def compactCurrentDivergence (n : ℕ) (a : Core n 2) (q : OrbitSpace) : ℝ :=
  2 * scalarPairing n 2 a.val (compactMixedOperator n a).val q

theorem continuous_compactCurrentDivergence (n : ℕ) (a : Core n 2) :
    Continuous (compactCurrentDivergence n a) :=
  continuous_const.mul (continuous_scalarPairing n 2 a.val (compactMixedOperator n a).val)

theorem compactCurrentDivergence_coordinateProjection (n : ℕ) (a : Core n 2)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    compactCurrentDivergence n a (coordinateProjection x) =
      weightedDivergence (energyCurrent n 2 a.val.val.val) x := by
  calc
    _ = 2 * formPairing n 2 x (a.val.val.val x) ((compactMixedOperator n a).val.val.val x) :=
      congrArg (2 * ·) (scalarPairing_coordinateProjection n 2 a.val (compactMixedOperator n a).val x hx)
    _ = 2 * formPairing n 2 x (a.val.val.val x)
        (symmetricContraction n 2 x (covariantExterior n 2 a.val.val.val x) +
          covariantExterior n 1 (fun y => symmetricContraction n 1 y (a.val.val.val y)) x) :=
      congrArg (fun z => 2 * formPairing n 2 x (a.val.val.val x) z) (compactMixedOperator_apply n a x hx)
    _ = _ := (weightedDivergence_energyCurrent_two n
      (by simpa only [liftedDomain_univ] using Form.smooth a.val.val) x hx).symm

end TernaryPoly.PolynomialFormGeometricEnergy
