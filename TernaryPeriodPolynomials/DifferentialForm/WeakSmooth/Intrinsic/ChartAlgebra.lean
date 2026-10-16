module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothExtension

@[expose] public section


/-! Exact additive chart-current transport and actual smooth global reconstruction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates SymmetricSpaceCharts SymmetricSpacePositive
  SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham SmoothSingularComparison

/-- The genuine intrinsic chart-current correspondence preserves actual differences. -/
theorem intrinsicChartFormCurrent_sub (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T R : IntrinsicCurrent n k (chartOpen S Ω)) :
    intrinsicChartFormCurrent n k S Ω hΩ (T - R) =
      intrinsicChartFormCurrent n k S Ω hΩ T - intrinsicChartFormCurrent n k S Ω hΩ R := by
  apply LinearMap.ext
  intro φ
  exact map_sub (coordinates n k).symm
    (fun i => T (intrinsicMetricDualChartTest n k S Ω hΩ i φ))
    (fun i => R (intrinsicMetricDualChartTest n k S Ω hΩ i φ))

/-- Extending the genuine local representative of a global smooth form recovers precisely its
actual restriction to the smaller quotient chart. -/
theorem intrinsicChartExtend_globalRepresentative (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : EquivariantForm (deckRepresentation n) univ k) :
    chartExtendOn (deckRepresentation n) S Ω.isOpen k
      (restrictTo hΩ k (globalChartRepresentative (deckRepresentation n) S k a)) =
      restrictEquivariant (deckRepresentation n) (subset_univ _) k a := by
  have he : restrictTo hΩ k (globalChartRepresentative (deckRepresentation n) S k a) =
      coveringChartRestriction (deckRepresentation n) S hΩ k
        (restrictEquivariant (deckRepresentation n) (subset_univ _) k a) := by
    apply Form.ext
    intro x hx
    apply (restrictTo_apply hΩ _ hx).trans
    apply (globalChartRepresentative_apply (deckRepresentation n) S a (hΩ hx)).trans
    apply Eq.trans _ (restrictTo_apply (chartSubset_liftedDomain S hΩ) _ hx).symm
    exact (restrictEquivariant_apply (deckRepresentation n) (subset_univ _) a
      (chartSubset_liftedDomain S hΩ hx)).symm
  exact (congrArg (chartExtendOn (deckRepresentation n) S Ω.isOpen k) he).trans
    (coveringChartExtend_restrict (deckRepresentation n) S Ω.isOpen hΩ k _)

end TernaryPoly.PolynomialFormWeakSmooth
