module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.Norm
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral

@[expose] public section


/-! Genuine local metric square integrability and compact-region L2 norm equivalence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian
  CompactCoordinateIntegration CompactSquareIntegral
open scoped ContDiff

def weightedSquare (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) : ℝ :=
  coordinateDensity x * formPairing n k x (w x) (w x)

theorem tsupport_weightedSquare (n k : ℕ) (w : Coordinates → FormValue n k) :
    tsupport (weightedSquare n k w) ⊆ tsupport w := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp only [weightedSquare, hx, formPairing_zero_left, mul_zero]

theorem contDiff_weightedSquare (n k : ℕ) (w : Coordinates → FormValue n k)
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (hs : tsupport w ⊆ positiveCoordinates) :
    ContDiff ℝ ∞ (weightedSquare n k w) :=
  contDiff_of_tsupport_subset isOpen_positiveCoordinates
    (contDiffOn_coordinateDensity.mul (contDiffOn_formPairing_functions n k (fun _ h => h) hw hw))
    ((tsupport_weightedSquare n k w).trans hs)

theorem integrable_weightedSquare (n k : ℕ) (w : Coordinates → FormValue n k)
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ positiveCoordinates) : Integrable (weightedSquare n k w) volume :=
  (contDiff_weightedSquare n k w hw hs).continuous.integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_weightedSquare n k w))

theorem compact_integral_weighted_bounds (n k : ℕ) {K : Set Coordinates}
    (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ w : Coordinates → FormValue n k,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ K →
      c * (∫ x, ‖w x‖^2) ≤ ∫ x, weightedSquare n k w x ∧
      (∫ x, weightedSquare n k w x) ≤ C * ∫ x, ‖w x‖^2 := by
  obtain ⟨c,hc,hl⟩ := compact_weighted_lower_bound n k hK hKpos
  obtain ⟨C,hC,hu⟩ := compact_weighted_upper_bound n k hK hKpos
  refine ⟨c,C,hc,hC,fun w hw hcw hsw => ?_⟩
  have hi := integrable_weightedSquare n k w hw.contDiffOn hcw (hsw.trans hKpos)
  have hn := integrable_norm_square w hw.continuous hcw (μ := volume)
  have hl' (x : Coordinates) : c * ‖w x‖^2 ≤ weightedSquare n k w x := by
    by_cases hx : x ∈ K
    · exact hl x hx (w x)
    · have hw0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsw h))
      simp only [weightedSquare, hw0, norm_zero, zero_pow (by decide : 2 ≠ 0),
        formPairing_zero_left, mul_zero, le_refl]
  have hu' (x : Coordinates) : weightedSquare n k w x ≤ C * ‖w x‖^2 := by
    by_cases hx : x ∈ K
    · exact (le_abs_self _).trans (hu x hx (w x))
    · have hw0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsw h))
      simp only [weightedSquare, hw0, norm_zero, zero_pow (by decide : 2 ≠ 0),
        formPairing_zero_left, mul_zero, le_refl]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hn.const_mul c) hi hl'
  · rw [← integral_const_mul]
    exact integral_mono hi (hn.const_mul C) hu'

end TernaryPoly.PolynomialFormCoordinates
