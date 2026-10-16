module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Closedness
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Transitions

@[expose] public section


/-! Actual chart restrictions of a smooth form with a genuine weak primitive are closed. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpacePositive
  SymmetricSpaceCharts SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- The actual global chart representative intertwines the genuine smooth differentials. -/
theorem globalChartRepresentative_d (n k : ℕ) (S : Space)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    globalChartRepresentative (deckRepresentation n) S (k+1)
        (differential (deckRepresentation n) isOpen_univ k w) =
      d (quotientChart S).open_target k (globalChartRepresentative (deckRepresentation n) S k w) := by
  change chartRestrict (deckRepresentation n) S (k+1)
      (restrictEquivariant (deckRepresentation n) (subset_univ _) (k+1)
        (differential (deckRepresentation n) isOpen_univ k w)) = _
  exact (congrArg (chartRestrict (deckRepresentation n) S (k+1))
    (restrictEquivariant_d (deckRepresentation n) isOpen_univ (quotientChart S).open_source
      (subset_univ _) w)).trans (chartRestrict_d (deckRepresentation n) S _)

/-- The actual smooth chart representative of a smooth form possessing a genuine Hilbert weak
primitive is closed, with no independent closedness hypothesis. -/
theorem restrictedChart_closed_of_weak_primitive (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (ω : Core n (k+1)) (u : Hilbert n k)
    (hu : (u, inclusion n (k+1) ω) ∈ (maximalDifferential n k).graph) :
    d Ω.isOpen (k+1) (restrictTo hΩ (k+1)
      (globalChartRepresentative (deckRepresentation n) S (k+1) ω.val)) = 0 := by
  apply (restrictTo_d (quotientChart S).open_target Ω.isOpen hΩ _).symm.trans
  apply Eq.trans _ (map_zero (restrictTo hΩ (k+2)))
  apply congrArg (restrictTo hΩ (k+2))
  apply (globalChartRepresentative_d n (k+1) S ω.val).symm.trans
  exact (congrArg (globalChartRepresentative (deckRepresentation n) S (k+2))
    (differential_eq_zero_of_weak_primitive n k ω u hu)).trans
      (map_zero (globalChartRepresentative (deckRepresentation n) S (k+2)))

end TernaryPoly.PolynomialFormWeakSmooth
