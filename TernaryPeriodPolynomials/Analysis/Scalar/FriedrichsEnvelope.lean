module

public import TernaryPeriodPolynomials.Analysis.ScaledScalarKernel
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


/-! The actual first-order commutator envelope has scale-independent row and column masses. -/
noncomputable section
namespace TernaryPoly.ScalarFriedrichsEnvelope
open MeasureTheory
open ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation-invariant envelope of the derivative commutator kernel. -/
def envelope (κ : E → ℝ) (v : E) (L A B : ℝ) (z : E) : ℝ :=
  L * (‖z‖ * ‖fderiv ℝ κ z v‖) + (A + 2 * B) * ‖κ z‖

theorem envelope_nonneg (κ : E → ℝ) (v z : E) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ envelope κ v L A B z := by
  unfold envelope
  positivity

/-- Bounds on the actual variable coefficients imply a bound for the complete kernel. -/
theorem norm_commutatorKernel_le (κ a b : E → ℝ) (v x y : E) (L A B : ℝ)
    (ha : ‖a x - a y‖ ≤ L * ‖x - y‖) (hda : ‖fderiv ℝ a y v‖ ≤ A)
    (hbx : ‖b x‖ ≤ B) (hby : ‖b y‖ ≤ B) :
    ‖(a x - a y) * fderiv ℝ κ (x - y) v +
      (fderiv ℝ a y v + b x - b y) * κ (x - y)‖ ≤ envelope κ v L A B (x-y) := by
  have hzero : ‖fderiv ℝ a y v + b x - b y‖ ≤ A + 2 * B := by
    calc
      _ ≤ ‖fderiv ℝ a y v + b x‖ + ‖b y‖ := norm_sub_le _ _
      _ ≤ (‖fderiv ℝ a y v‖ + ‖b x‖) + ‖b y‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ A + 2 * B := by linarith
  calc
    _ ≤ ‖(a x - a y) * fderiv ℝ κ (x-y) v‖ +
        ‖(fderiv ℝ a y v + b x - b y) * κ (x-y)‖ := norm_add_le _ _
    _ = ‖a x - a y‖ * ‖fderiv ℝ κ (x-y) v‖ +
        ‖fderiv ℝ a y v + b x - b y‖ * ‖κ (x-y)‖ := by rw [norm_mul, norm_mul]
    _ ≤ (L * ‖x-y‖) * ‖fderiv ℝ κ (x-y) v‖ + (A+2*B) * ‖κ (x-y)‖ :=
      add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hzero (norm_nonneg _))
    _ = _ := by unfold envelope; ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem envelope_dilate (κ : E → ℝ) (v z : E) (L A B c : ℝ) (hc : 0 < c)
    (hκ : Differentiable ℝ κ) :
    envelope (dilate c κ) v L A B z = dilate c (envelope κ v L A B) z := by
  unfold envelope
  rw [derivativeMoment_dilate κ c hc hκ v z]
  simp only [dilate, norm_mul, Real.norm_of_nonneg (pow_nonneg hc.le _)]
  ring

theorem integral_envelope_dilate (μ : Measure E) [μ.IsAddHaarMeasure]
    (κ : E → ℝ) (v : E) (L A B c : ℝ) (hc : 0 < c) (hκ : Differentiable ℝ κ) :
    ∫ z, envelope (dilate c κ) v L A B z ∂μ = ∫ z, envelope κ v L A B z ∂μ := by
  simp_rw [envelope_dilate κ v _ L A B c hc hκ]
  exact integral_dilate μ c hc _

/-- Every row of the genuine dominating kernel has the same scale-independent mass. -/
theorem row_mass (μ : Measure E) [μ.IsAddHaarMeasure]
    (κ : E → ℝ) (v x : E) (L A B c : ℝ) (hc : 0 < c) (hκ : Differentiable ℝ κ) :
    ∫ y, envelope (dilate c κ) v L A B (x-y) ∂μ = ∫ z, envelope κ v L A B z ∂μ := by
  rw [integral_sub_left_eq_self]
  exact integral_envelope_dilate μ κ v L A B c hc hκ

/-- Every column has that same mass; no symmetry assumption on the kernel is needed. -/
theorem column_mass (μ : Measure E) [μ.IsAddHaarMeasure]
    (κ : E → ℝ) (v y : E) (L A B c : ℝ) (hc : 0 < c) (hκ : Differentiable ℝ κ) :
    ∫ x, envelope (dilate c κ) v L A B (x-y) ∂μ = ∫ z, envelope κ v L A B z ∂μ := by
  rw [integral_sub_right_eq_self]
  exact integral_envelope_dilate μ κ v L A B c hc hκ

end TernaryPoly.ScalarFriedrichsEnvelope
