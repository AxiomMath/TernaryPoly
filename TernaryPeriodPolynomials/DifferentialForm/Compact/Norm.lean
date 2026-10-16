module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Basis
public import TernaryPeriodPolynomials.Analysis.Compact.PositiveBilinear

@[expose] public section


/-! Genuine uniform norm comparisons for polynomial forms in compact coordinate regions. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian
open scoped ContDiff

/-- The actual local metric-volume bilinear form, in the original normed form fiber. -/
def weightedContinuousBilin (n k : ℕ) (x : Coordinates) :
    FormValue n k →L[ℝ] FormValue n k →L[ℝ] ℝ :=
  coordinateDensity x • formContinuousBilin n k x

@[simp] theorem weightedContinuousBilin_apply (n k : ℕ) (x : Coordinates) (a b : FormValue n k) :
    weightedContinuousBilin n k x a b = coordinateDensity x * formPairing n k x a b := rfl

theorem continuousOn_weightedContinuousBilin (n k : ℕ) :
    ContinuousOn (weightedContinuousBilin n k) positiveCoordinates :=
  contDiffOn_coordinateDensity.continuousOn.smul (contDiffOn_formContinuousBilin n k).continuousOn

/-- On every actual compact coordinate region, the metric-volume norm controls the form norm uniformly. -/
theorem compact_weighted_lower_bound (n k : ℕ) {K : Set Coordinates}
    (hK : IsCompact K) (hKU : K ⊆ positiveCoordinates) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ a : FormValue n k,
      c * ‖a‖ ^ 2 ≤ coordinateDensity x * formPairing n k x a a := by
  exact PositiveBilinearFinite.compact_pos_lower_bound (weightedContinuousBilin n k) hK
    ((continuousOn_weightedContinuousBilin n k).mono hKU)
    (fun x hx a ha => mul_pos (coordinateDensity_pos x (hKU hx))
      (formPairing_positive n k x (hKU hx) a ha))

/-- The local metric-volume norm is also bounded above by the original form norm on compact regions. -/
theorem compact_weighted_upper_bound (n k : ℕ) {K : Set Coordinates}
    (hK : IsCompact K) (hKU : K ⊆ positiveCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ a : FormValue n k,
      |coordinateDensity x * formPairing n k x a a| ≤ C * ‖a‖ ^ 2 :=
  PositiveBilinearFinite.compact_upper_bound (E := FormValue n k) (X := Coordinates) (weightedContinuousBilin n k) hK
    ((continuousOn_weightedContinuousBilin n k).mono hKU)

end TernaryPoly.PolynomialFormCoordinates
