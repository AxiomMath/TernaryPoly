module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.SupportSub
public import TernaryPeriodPolynomials.DifferentialForm.Chart.HilbertNorm
public import TernaryPeriodPolynomials.DifferentialForm.WeightedSquare

@[expose] public section


/-! Exact Hilbert difference norm in one actual quotient chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert

theorem norm_inclusion_sub_square_chart (n k : ℕ) (S : Space) (a b : Core n k)
    (ha : quotientSupport a.val ⊆ (quotientChart S).source)
    (hb : quotientSupport b.val ⊆ (quotientChart S).source)
    (f g : Coordinates → FormValue n k)
    (hf : (globalChartRepresentative (deckRepresentation n) S k a.val).val = f)
    (hg : (globalChartRepresentative (deckRepresentation n) S k b.val).val = g) :
    ‖inclusion n k a - inclusion n k b‖^2 = ∫ x, weightedSquare n k (f-g) x := by
  have hs : quotientSupport (a-b).val ⊆ (quotientChart S).source :=
    (quotientSupport_sub a.val b.val).trans (union_subset ha hb)
  have hr : (globalChartRepresentative (deckRepresentation n) S k (a-b).val).val = f-g := by
    have h := congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val)
      ((globalChartRepresentative (deckRepresentation n) S k).map_sub a.val b.val)
    exact h.trans (congrArg₂ (· - ·) hf hg)
  have hn := norm_inclusion_square_chart n k S (a-b) hs
  exact (congrArg (fun v : Hilbert n k => ‖v‖^2) ((inclusion n k).map_sub a b).symm).trans
    (hn.trans (congrArg (fun z : Coordinates → FormValue n k => ∫ x, weightedSquare n k z x) hr))

end TernaryPoly.PolynomialFormCoordinates
