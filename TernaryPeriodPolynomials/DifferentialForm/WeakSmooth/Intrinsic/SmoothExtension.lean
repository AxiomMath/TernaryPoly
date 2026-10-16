module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothChart

@[expose] public section


/-! Literal regular-current coordinates of the actual smooth chart extension. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormCoordinates SymmetricSpaceCharts
  SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham
  SmoothSingularComparison

/-- Actual chart extension of a genuine smooth coordinate form has precisely that form's
literal Bochner compact-test current. -/
theorem intrinsicChartFormCurrent_smooth_extend (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : Form (F := Coefficients n) Ω k) :
    intrinsicChartFormCurrent n k S Ω hΩ
      (intrinsicSmoothCurrent n k (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen)
        (chartExtendOn (deckRepresentation n) S Ω.isOpen k a)) =
      valuedRegularCurrent volume Ω a.val (Form.smooth a).continuousOn := by
  apply (intrinsicChartFormCurrent_smooth n k S Ω hΩ _).trans
  apply valuedRegularCurrent_congr volume Ω
  intro x hx
  have he := congrArg (fun z : Form (F := Coefficients n) Ω k => z.val x)
    (coveringChartRestriction_extend (deckRepresentation n) S Ω.isOpen hΩ k a)
  exact (restrictTo_apply (chartSubset_liftedDomain S hΩ)
    (chartExtendOn (deckRepresentation n) S Ω.isOpen k a).val hx).symm.trans he

end TernaryPoly.PolynomialFormWeakSmooth
