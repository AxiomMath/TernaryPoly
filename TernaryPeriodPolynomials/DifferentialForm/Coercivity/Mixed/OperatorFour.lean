module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CovariantAdjointFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.FiveIdentity

@[expose] public section



/-! Degree-4 specialization of the compact mixed operator and the descended energy-current
divergence, mirroring `MixedOperator.lean`'s degree-0 case: a single surviving term, here
`compactCovariantExterior n 4 ∘ compactSymmetricContraction n 4` (the other cross term,
`compactSymmetricContraction n 5 ∘ compactCovariantExterior n 5`, is identically zero since its
intermediate value lives in the trivial module `Core n 6`, `SixVanishing.lean`), using the
one-term anticommutator corollary `covariant_contraction_anticommutator_five_contraction`
(`AnticommutatorFiveIdentity.lean`) in place of the generic two-term
`covariant_contraction_anticommutator_two`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise ContDiff

/-- The compact anticommutator at degree 4 (output degree 5), a single term. Mirrors
`compactMixedOperatorZero`. -/
def compactMixedOperatorFour (n : ℕ) (a : Core n 5) : Core n 5 :=
  compactCovariantExterior n 4 (compactSymmetricContraction n 4 a)

theorem compactMixedOperatorFour_apply (n : ℕ) (a : Core n 5) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    (compactMixedOperatorFour n a).val.val.val x =
      covariantExterior n 4 (fun y => symmetricContraction n 4 y (a.val.val.val y)) x := by
  change (compactCovariantExterior n 4 (compactSymmetricContraction n 4 a)).val.val.val x = _
  exact (compactCovariantExterior_apply n 4 _ x hx).trans
    (congrArg (fun w => covariantExterior n 4 w x) (funext (compactSymmetricContraction_apply n 4 a)))

/-- Degree-5 energy-current divergence, mirroring `weightedDivergence_energyCurrent_two` via the
one-term anticommutator corollary. -/
theorem weightedDivergence_energyCurrent_five (n : ℕ) {w : Coordinates → FormValue n 5}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n 5 w) x =
      2 * formPairing n 5 x (w x) (covariantExterior n 4 (fun y => symmetricContraction n 4 y (w y)) x) := by
  rw [weightedDivergence_energyCurrent n 5 hw x hx,
    covariant_contraction_anticommutator_five_contraction n w x hx
      (((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))]

def compactCurrentDivergenceFour (n : ℕ) (a : Core n 5) (q : OrbitSpace) : ℝ :=
  2 * scalarPairing n 5 a.val (compactMixedOperatorFour n a).val q

theorem continuous_compactCurrentDivergenceFour (n : ℕ) (a : Core n 5) :
    Continuous (compactCurrentDivergenceFour n a) :=
  continuous_const.mul (continuous_scalarPairing n 5 a.val (compactMixedOperatorFour n a).val)

theorem compactCurrentDivergenceFour_coordinateProjection (n : ℕ) (a : Core n 5)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    compactCurrentDivergenceFour n a (coordinateProjection x) =
      weightedDivergence (energyCurrent n 5 a.val.val.val) x := by
  calc
    _ = 2 * formPairing n 5 x (a.val.val.val x) ((compactMixedOperatorFour n a).val.val.val x) :=
      congrArg (2 * ·) (scalarPairing_coordinateProjection n 5 a.val (compactMixedOperatorFour n a).val x hx)
    _ = 2 * formPairing n 5 x (a.val.val.val x)
        (covariantExterior n 4 (fun y => symmetricContraction n 4 y (a.val.val.val y)) x) :=
      congrArg (fun z => 2 * formPairing n 5 x (a.val.val.val x) z) (compactMixedOperatorFour_apply n a x hx)
    _ = _ := (weightedDivergence_energyCurrent_five n
      (by simpa only [liftedDomain_univ] using Form.smooth a.val.val) x hx).symm

end TernaryPeriodPolynomials.Argument.Coercivity
