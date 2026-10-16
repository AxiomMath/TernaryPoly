module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Poincare
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.RegularDifferential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.CurrentAlgebra
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.BoxConvex
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamPoincare

@[expose] public section


/-! Actual local current potentials after subtracting a genuine smooth primitive. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts
open SmoothLocalDeRham ContinuousAlternatingMap

/-- On an actual coordinate box, every actual current primitive of a closed smooth two-form is
an actual smooth one-form primitive plus the actual exterior derivative of a scalar current. -/
theorem coordinateTestBox_weak_primitive_mod_smooth (n : ℕ)
    (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates)
    (W : FormWeak n 1 (coordinateTestBox e a))
    (ω : Form (F := Coefficients n) (coordinateTestBox e a : Set Coordinates) 2)
    (hω : d (coordinateTestBox e a).isOpen 2 ω = 0)
    (hW : formWeakExterior n 1 (coordinateTestBox e a) W =
      valuedRegularCurrent volume (coordinateTestBox e a) ω.val (Form.smooth ω).continuousOn) :
    ∃ v : Form (F := Coefficients n) (coordinateTestBox e a : Set Coordinates) 1,
      d (coordinateTestBox e a).isOpen 1 v = ω ∧
      ∃ T : FormWeak n 0 (coordinateTestBox e a),
        formWeakExterior n 0 (coordinateTestBox e a) T =
          W - valuedRegularCurrent volume (coordinateTestBox e a) v.val (Form.smooth v).continuousOn := by
  let Ω := coordinateTestBox e a
  obtain ⟨v, hv⟩ := poincare_convex Ω.isOpen (coordinateTestBox_convex e a) ω hω
  refine ⟨v, hv, ?_⟩
  apply coordinateTestBox_formWeakOneExact n e a
  apply (formWeakExterior_sub n 1 Ω W
    (valuedRegularCurrent volume Ω v.val (Form.smooth v).continuousOn)).trans
  apply sub_eq_zero.mpr
  apply hW.trans
  apply Eq.trans _ (formWeakExterior_regular n 1 volume Ω v.val (Form.smooth v)).symm
  apply valuedRegularCurrent_congr volume Ω
  intro x hx
  exact ((congrArg (fun z : Form (F := Coefficients n) (Ω : Set Coordinates) 2 => z.val x) hv).symm).trans
    (d_apply Ω.isOpen v hx)

end TernaryPoly.PolynomialFormWeakSmooth
