module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LocalPotential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.HilbertFormDifferential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.HilbertRegularCurrent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.ChartClosedness

@[expose] public section


/-! Actual local scalar-current potentials for actual Hilbert weak primitives of compact forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpacePositive
  SymmetricSpaceCharts SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- On every genuine coordinate box inside a genuine quotient chart, a Hilbert weak primitive
of a compact smooth two-form is the sum of a genuine smooth local primitive and the actual
exterior differential of a zero-form compact-test current. Closedness is derived from the given
Hilbert graph equation. -/
theorem hilbert_weak_primitive_local_potential (n : ℕ) (S : Space)
    (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates)
    (hΩ : (coordinateTestBox e a : Set Coordinates) ⊆ (quotientChart S).target)
    (ω : Core n 2) (u : Hilbert n 1)
    (hu : (u, inclusion n 2 ω) ∈ (maximalDifferential n 1).graph) :
    ∃ v : Form (F := Coefficients n) (coordinateTestBox e a : Set Coordinates) 1,
      d (coordinateTestBox e a).isOpen 1 (v) =
        restrictTo hΩ 2 (globalChartRepresentative (deckRepresentation n) S 2 ω.val) ∧
      ∃ T : FormWeak n 0 (coordinateTestBox e a),
        formWeakExterior n 0 (coordinateTestBox e a) T =
          chartHilbertFormCurrent n 1 S (coordinateTestBox e a) hΩ u -
            valuedRegularCurrent volume (coordinateTestBox e a) v.val (Form.smooth v).continuousOn := by
  let Ω := coordinateTestBox e a
  let z := restrictTo hΩ 2 (globalChartRepresentative (deckRepresentation n) S 2 ω.val)
  apply coordinateTestBox_weak_primitive_mod_smooth n e a _ z
    (restrictedChart_closed_of_weak_primitive n 1 S Ω hΩ ω u hu)
  apply (chartHilbertFormCurrent_differential n 1 S Ω hΩ u (inclusion n 2 ω) hu).trans
  apply (chartHilbertFormCurrent_inclusion n 2 S Ω hΩ ω).trans
  apply valuedRegularCurrent_congr volume Ω
  intro x hx
  exact (restrictTo_apply hΩ _ hx).symm

end TernaryPoly.PolynomialFormWeakSmooth
