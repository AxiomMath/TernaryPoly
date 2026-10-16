module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothExtension
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Recognition

@[expose] public section


/-! Actual intrinsic scalar-current smooth recognition on genuine coordinate boxes. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormCoordinates SymmetricSpaceCharts
  SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham

/-- A genuine intrinsic zero-current whose actual differential is a genuine smooth one-form
current is itself the actual current of a genuine smooth zero-form on each coordinate box. -/
theorem intrinsicCurrent_zero_smooth_on_coordinateTestBox (n : ℕ) (S : Space)
    (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates)
    (hΩ : (coordinateTestBox b c : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n 0 (chartOpen S (coordinateTestBox b c)))
    (a : EquivariantForm (deckRepresentation n) (chartOpen S (coordinateTestBox b c)) 1)
    (hT : intrinsicCurrentDifferential n 0 (chartOpen S (coordinateTestBox b c)) T =
      intrinsicSmoothCurrent n 1 (chartOpen S (coordinateTestBox b c))
        (chartOpen_isOpen S (coordinateTestBox b c).isOpen) a) :
    ∃ f : EquivariantForm (deckRepresentation n) (chartOpen S (coordinateTestBox b c)) 0,
      T = intrinsicSmoothCurrent n 0 (chartOpen S (coordinateTestBox b c))
        (chartOpen_isOpen S (coordinateTestBox b c).isOpen) f := by
  let Ω := coordinateTestBox b c
  have hd : formWeakExterior n 0 Ω (intrinsicChartFormCurrent n 0 S Ω hΩ T) =
      valuedRegularCurrent volume Ω a.val.val (intrinsicChart_local_smooth n 1 S Ω hΩ a).continuousOn :=
    (intrinsicChartFormCurrent_differential n 0 S Ω hΩ T).trans
      ((congrArg (intrinsicChartFormCurrent n 1 S Ω hΩ) hT).trans
        (intrinsicChartFormCurrent_smooth n 1 S Ω hΩ a))
  exact (coordinateTestBox_zeroForm_smooth_of_smooth_exterior n b c
    (intrinsicChartFormCurrent n 0 S Ω hΩ T) a.val.val
    (intrinsicChart_local_smooth n 1 S Ω hΩ a) hd).elim (fun f hf => hf.elim (fun hfs he => by
      let w : Form (E := Coordinates) (F := Coefficients n) (Ω : Set Coordinates) 0 :=
        restrictForm (E := Coordinates) (F := Coefficients n) (Ω : Set Coordinates) f hfs
      refine ⟨chartExtendOn (deckRepresentation n) S Ω.isOpen 0 w, ?_⟩
      apply (Function.LeftInverse.injective (intrinsicCurrentOfForm_chartFormCurrent n 0 S Ω hΩ))
      apply he.trans
      apply Eq.trans _ (intrinsicChartFormCurrent_smooth_extend n 0 S Ω hΩ w).symm
      apply valuedRegularCurrent_congr volume Ω
      intro x hx
      exact (restrictForm_apply (E := Coordinates) (F := Coefficients n) (n := 0) f hfs hx).symm))

end TernaryPoly.PolynomialFormWeakSmooth
