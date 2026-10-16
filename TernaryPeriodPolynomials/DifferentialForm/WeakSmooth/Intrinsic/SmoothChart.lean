module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothCoordinates
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.FormDifferential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.RegularDifferential
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.CoveringChart

@[expose] public section


/-! Actual smooth-current faithfulness and exterior differentiation on genuine chart opens. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormCoordinates SymmetricSpaceCharts
  SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham
  SmoothSingularComparison

/-- Actual intrinsic smooth currents separate genuine smooth equivariant forms on every actual
chart open. -/
theorem intrinsicSmoothCurrent_chart_injective (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) :
    Function.Injective (intrinsicSmoothCurrent n k (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen)) := by
  intro a b hab
  have hr := (intrinsicChartFormCurrent_smooth n k S Ω hΩ a).symm.trans
    ((congrArg (intrinsicChartFormCurrent n k S Ω hΩ) hab).trans
      (intrinsicChartFormCurrent_smooth n k S Ω hΩ b))
  have he := (valuedRegularCurrent_eq_iff volume (coordinates n k) Ω a.val.val b.val.val
    (intrinsicChart_local_smooth n k S Ω hΩ a).continuousOn
    (intrinsicChart_local_smooth n k S Ω hΩ b).continuousOn).mp hr
  have hl : coveringChartRestriction (deckRepresentation n) S hΩ k a =
      coveringChartRestriction (deckRepresentation n) S hΩ k b := by
    apply Form.ext
    intro x hx
    exact (restrictTo_apply (chartSubset_liftedDomain S hΩ) a.val hx).trans
      ((he hx).trans (restrictTo_apply (chartSubset_liftedDomain S hΩ) b.val hx).symm)
  exact (coveringChartExtend_restrict (deckRepresentation n) S Ω.isOpen hΩ k a).symm.trans
    ((congrArg (chartExtendOn (deckRepresentation n) S Ω.isOpen k) hl).trans
      (coveringChartExtend_restrict (deckRepresentation n) S Ω.isOpen hΩ k b))

/-- The actual intrinsic smooth current commutes with the genuine exterior differential on
actual quotient chart opens. -/
theorem intrinsicSmoothCurrent_chart_differential (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : EquivariantForm (deckRepresentation n) (chartOpen S Ω) k) :
    intrinsicCurrentDifferential n k (chartOpen S Ω)
        (intrinsicSmoothCurrent n k (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen) a) =
      intrinsicSmoothCurrent n (k+1) (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen)
        (differential (deckRepresentation n) (chartOpen_isOpen S Ω.isOpen) k a) := by
  apply (Function.LeftInverse.injective (intrinsicCurrentOfForm_chartFormCurrent n (k+1) S Ω hΩ))
  apply (intrinsicChartFormCurrent_differential n k S Ω hΩ _).symm.trans
  apply (congrArg (formWeakExterior n k Ω) (intrinsicChartFormCurrent_smooth n k S Ω hΩ a)).trans
  apply (formWeakExterior_regular n k volume Ω a.val.val (intrinsicChart_local_smooth n k S Ω hΩ a)).trans
  apply Eq.trans _ (intrinsicChartFormCurrent_smooth n (k+1) S Ω hΩ _).symm
  apply valuedRegularCurrent_congr volume Ω
  intro x hx
  exact (d_apply (liftedDomain_isOpen (chartOpen_isOpen S Ω.isOpen)) a.val
    (intrinsicChart_domain_lifted S Ω hΩ hx)).symm

end TernaryPoly.PolynomialFormWeakSmooth
