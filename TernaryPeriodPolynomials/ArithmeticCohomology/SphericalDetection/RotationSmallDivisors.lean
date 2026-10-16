module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationWeights
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def rotationGaussian : GaussianInt := ⟨3, 4⟩

def rotationGaussianReduction : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(2 : ZMod 5), by decide⟩

theorem rotationGaussianReduction_apply : rotationGaussianReduction rotationGaussian = 1 := by
  norm_num [rotationGaussianReduction, Zsqrtd.lift_apply_apply, rotationGaussian]
  decide

theorem rotationGaussian_pow_sub_ne_zero (exponent : ℕ) (positive : 0 < exponent) :
    rotationGaussian ^ exponent - (5 : GaussianInt) ^ exponent ≠ 0 := by
  intro zero
  have reduced := congrArg rotationGaussianReduction zero
  rw [map_sub, map_pow, map_pow, rotationGaussianReduction_apply, map_ofNat, map_zero,
    one_pow] at reduced
  rw [show (5 : ZMod 5) = 0 by decide, zero_pow (ne_of_gt positive), sub_zero] at reduced
  exact (show (1 : ZMod 5) ≠ 0 by decide) reduced

theorem gaussianInt_complex_norm_ge_one (value : GaussianInt) (nonzero : value ≠ 0) :
    1 ≤ ‖GaussianInt.toComplex value‖ := by
  have integer_lower : 1 ≤ Zsqrtd.norm value := GaussianInt.norm_pos.mpr nonzero
  have real_lower : (1 : ℝ) ≤ (Zsqrtd.norm value : ℝ) := by exact_mod_cast integer_lower
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at real_lower
  nlinarith [norm_nonneg (GaussianInt.toComplex value)]

/-- An explicit unit-circle phase with quantitative separation of its powers. -/
def rotationSeparationPhase : ℂ := GaussianInt.toComplex rotationGaussian / 5

theorem rotationSeparationPhase_norm : ‖rotationSeparationPhase‖ = 1 := by
  have square : ‖rotationSeparationPhase‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [rotationSeparationPhase, GaussianInt.toComplex_def, rotationGaussian,
      Complex.normSq_apply, Complex.div_re, Complex.div_im]
  nlinarith [norm_nonneg rotationSeparationPhase]

theorem rotationSeparationPhase_ne_zero : rotationSeparationPhase ≠ 0 := by
  intro zero
  have norm := rotationSeparationPhase_norm
  rw [zero, norm_zero] at norm
  norm_num at norm

theorem rotationSeparationPhase_pow_sub (exponent : ℕ) :
    rotationSeparationPhase ^ exponent - 1 =
      GaussianInt.toComplex (rotationGaussian ^ exponent - (5 : GaussianInt) ^ exponent) / (5 : ℂ) ^ exponent := by
  simp only [rotationSeparationPhase, div_pow, map_sub, map_pow, map_ofNat]
  field_simp

theorem rotationSeparationPhase_pow_bound (exponent : ℕ) (positive : 0 < exponent) :
    (5 : ℝ)⁻¹ ^ exponent ≤ ‖rotationSeparationPhase ^ exponent - 1‖ := by
  rw [rotationSeparationPhase_pow_sub, norm_div, norm_pow]
  norm_num only [Complex.norm_ofNat]
  rw [div_pow, one_pow]
  exact div_le_div_of_nonneg_right
    (gaussianInt_complex_norm_ge_one _ (rotationGaussian_pow_sub_ne_zero exponent positive))
    (pow_nonneg (by norm_num) _)

theorem rotationSeparationPhase_pow_ne_one (exponent : ℕ) (positive : 0 < exponent) :
    rotationSeparationPhase ^ exponent ≠ 1 := by
  intro one
  have bound := rotationSeparationPhase_pow_bound exponent positive
  rw [one, sub_self, norm_zero] at bound
  exact (not_le_of_gt (pow_pos (by norm_num : (0 : ℝ) < 5⁻¹) exponent)) bound

theorem complex_unit_norm_inv_sub_one (value : ℂ) (unit_norm : ‖value‖ = 1) :
    ‖value⁻¹ - 1‖ = ‖value - 1‖ := by
  have nonzero : value ≠ 0 := by
    intro zero
    norm_num [zero] at unit_norm
  have equality : value⁻¹ - 1 = -(value - 1) / value := by
    field_simp
    ring
  rw [equality, norm_div, norm_neg, unit_norm, div_one]

theorem rotationSeparationPhase_zpow_bound (exponent : ℤ) (nonzero : exponent ≠ 0) :
    (5 : ℝ)⁻¹ ^ exponent.natAbs ≤ ‖rotationSeparationPhase ^ exponent - 1‖ := by
  cases exponent with
  | ofNat exponent =>
    change (5 : ℝ)⁻¹ ^ exponent ≤ ‖rotationSeparationPhase ^ exponent - 1‖
    exact rotationSeparationPhase_pow_bound exponent
      (Nat.pos_of_ne_zero (fun zero => nonzero (by rw [zero]; rfl)))
  | negSucc exponent =>
    rw [zpow_negSucc, complex_unit_norm_inv_sub_one _ (by rw [norm_pow, rotationSeparationPhase_norm, one_pow])]
    exact rotationSeparationPhase_pow_bound (exponent + 1) (by omega)

theorem rotationSeparationPhase_zpow_ne_one (exponent : ℤ) (nonzero : exponent ≠ 0) :
    rotationSeparationPhase ^ exponent ≠ 1 := by
  intro one
  have bound := rotationSeparationPhase_zpow_bound exponent nonzero
  rw [one, sub_self, norm_zero] at bound
  exact (not_le_of_gt (pow_pos (by norm_num : (0 : ℝ) < 5⁻¹) exponent.natAbs)) bound

theorem rotationSeparationPhase_sub_norm (first second : ℤ) :
    ‖rotationSeparationPhase ^ first - rotationSeparationPhase ^ second‖ =
      ‖rotationSeparationPhase ^ (first - second) - 1‖ := by
  have equality : rotationSeparationPhase ^ first - rotationSeparationPhase ^ second =
      (rotationSeparationPhase ^ (first - second) - 1) * rotationSeparationPhase ^ second := by
    rw [sub_mul, ← zpow_add₀ rotationSeparationPhase_ne_zero, sub_add_cancel, one_mul]
  rw [equality, norm_mul, norm_zpow, rotationSeparationPhase_norm, one_zpow, mul_one]

theorem rotationSeparationPhase_zpow_injective : Function.Injective (fun exponent : ℤ => rotationSeparationPhase ^ exponent) := by
  intro first second equal
  change rotationSeparationPhase ^ first = rotationSeparationPhase ^ second at equal
  by_contra distinct
  have zero : ‖rotationSeparationPhase ^ (first - second) - 1‖ = 0 := by
    rw [← rotationSeparationPhase_sub_norm, equal, sub_self, norm_zero]
  exact rotationSeparationPhase_zpow_ne_one (first - second) (sub_ne_zero.mpr distinct)
    (sub_eq_zero.mp (norm_eq_zero.mp zero))

theorem rotationSeparationPhase_sub_inv_bound (first second : ℤ) (distinct : first ≠ second) :
    ‖(rotationSeparationPhase ^ first - rotationSeparationPhase ^ second)⁻¹‖ ≤
      (5 : ℝ) ^ (first - second).natAbs := by
  rw [norm_inv, rotationSeparationPhase_sub_norm]
  have lower := rotationSeparationPhase_zpow_bound (first - second) (sub_ne_zero.mpr distinct)
  have positive : 0 < (5 : ℝ)⁻¹ ^ (first - second).natAbs := pow_pos (by norm_num) _
  have inverted := inv_le_inv₀ (positive.trans_le lower) positive |>.mpr lower
  simpa only [inv_pow, inv_inv] using inverted

def rotationSeparatingCircle : Circle :=
  ⟨rotationSeparationPhase, by simpa [Submonoid.unitSphere] using rotationSeparationPhase_norm⟩

theorem rotationSeparatingCircle_coe : (rotationSeparatingCircle : ℂ) = rotationSeparationPhase := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
