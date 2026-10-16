module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Exactness
public import TernaryPeriodPolynomials.DifferentialForm.PositiveHilbertExactness
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CoefficientExactness

@[expose] public section


/-! Actual compact smooth degree-two exactness in every positive polynomial coefficient degree. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpaceCovering SmoothCoveringDeRham

/-- Every actual closed compact smooth two-form with positive polynomial coefficient degree has
a genuine global smooth equivariant one-form primitive. -/
theorem positive_degree_compact_smooth_exact {n : ℕ} (hn : 0 < n) :
    CompactExactInDegree (deckRepresentation n) 1 := by
  intro omega hClosed
  exact (closed_compact_has_weak_primitive hn omega hClosed).elim
    (fun u hu => hilbert_weak_primitive_smooth_exact n omega u hu)

end TernaryPoly.PolynomialFormWeakSmooth
