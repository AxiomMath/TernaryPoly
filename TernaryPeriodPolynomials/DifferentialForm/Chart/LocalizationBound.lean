module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Localization
public import TernaryPeriodPolynomials.DifferentialForm.QuotientPairing
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic

@[expose] public section


/-! The true quotient metric norm of chart localization is bounded by the cutoff supremum. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  SymmetricSpaceRiemannian PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)

theorem scalarPairing_chartCutoff_le (M : ℝ) (hχM : ∀ x, ‖χ x‖ ≤ M)
    (w : EquivariantForm (deckRepresentation n) univ k) (q : OrbitSpace) :
    scalarPairing n k (chartCutoff n k S χ hχ hcχ hsχ w).val
      (chartCutoff n k S χ hχ hcχ hsχ w).val q ≤ M^2 * scalarPairing n k w w q := by
  let a := chartCutoff n k S χ hχ hcχ hsχ w
  by_cases hq : q ∈ (quotientChart S).source
  · let x := quotientChart S q
    have hx : x ∈ (quotientChart S).target := (quotientChart S).map_source hq
    have hxp := quotientChart_target_subset S hx
    have hp : coordinateProjection x = q := by
      rw [← quotientChart_projection_coordinates S hx]
      exact (quotientChart S).left_inv hq
    have ha : a.val.val.val x = χ x • w.val.val x := chartCutoff_apply n k S χ hχ hcχ hsχ w hx
    have hsq : χ x ^ 2 ≤ M^2 := by
      simpa only [← pow_two, Real.norm_eq_abs, sq_abs] using
        mul_self_le_mul_self (norm_nonneg (χ x)) (hχM x)
    calc
      _ = formPairing n k x (a.val.val.val x) (a.val.val.val x) :=
        (congrArg (scalarPairing n k a.val a.val) hp.symm).trans
          (scalarPairing_coordinateProjection n k a.val a.val x hxp)
      _ = χ x ^ 2 * formPairing n k x (w.val.val x) (w.val.val x) := by
        rw [ha, formPairing_smul_left, formPairing_smul_right]
        ring
      _ ≤ M^2 * formPairing n k x (w.val.val x) (w.val.val x) :=
        mul_le_mul_of_nonneg_right hsq (formPairing_nonneg n k x hxp _)
      _ = _ := congrArg (M^2 * ·) ((scalarPairing_coordinateProjection n k w w x hxp).symm.trans
        (congrArg (scalarPairing n k w w) hp))
  · have hz : scalarPairing n k a.val a.val q = 0 := by
      by_contra hn
      exact hq (quotientSupport_chartCutoff n k S χ hχ hcχ hsχ w
        (subset_closure (support_scalarPairing n k a.val a.val hn).1))
    rw [hz]
    exact mul_nonneg (sq_nonneg _) (scalarPairing_nonneg n k w q)

theorem norm_chartCutoff_square_le (M : ℝ) (hχM : ∀ x, ‖χ x‖ ≤ M) (w : Core n k) :
    ‖inclusion n k (chartCutoff n k S χ hχ hcχ hsχ w.val)‖^2 ≤ M^2 * ‖inclusion n k w‖^2 := by
  let a := chartCutoff n k S χ hχ hcχ hsχ w.val
  have hn (z : Core n k) : ‖inclusion n k z‖^2 = ∫ q, scalarPairing n k z.val z.val q ∂orbitVolume :=
    (real_inner_self_eq_norm_sq _).symm.trans (inner_inclusion n k z z)
  calc
    _ = ∫ q, scalarPairing n k a.val a.val q ∂orbitVolume := hn a
    _ ≤ ∫ q, M^2 * scalarPairing n k w.val w.val q ∂orbitVolume :=
      integral_mono (integrable_scalarPairing n k a a.val)
        ((integrable_scalarPairing n k w w.val).const_mul _)
        (scalarPairing_chartCutoff_le n k S χ hχ hcχ hsχ M hχM w.val)
    _ = _ := (integral_const_mul (M^2) (scalarPairing n k w.val w.val)).trans
      (congrArg (M^2 * ·) (hn w).symm)

end TernaryPoly.PolynomialFormCoordinates
