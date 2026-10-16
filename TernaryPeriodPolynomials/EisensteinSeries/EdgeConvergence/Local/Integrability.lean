module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Coordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.HaarScaling
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section


/-!
# The local height and integrability of its negative powers

`localHeight u = √(1 + u₁² + u₂²)_∞ · max(1, |u₁|₃, |u₂|₃)` on the local radical coordinates
`u ∈ (ℝ × ℚ₃)²`; `H^{-c}` is integrable for `localRadicalMeasure` exactly when `c > 2`.
-/

open MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The local height `√(1 + u₁² + u₂²)_∞ · max(1, |u₁|₃, |u₂|₃)` on the local radical. -/
def localHeight (coordinates : LocalLine × LocalLine) : ℝ :=
  Real.sqrt (1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2) *
    max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖)

theorem localHeight_pos (coordinates : LocalLine × LocalLine) : 0 < localHeight coordinates := by
  unfold localHeight
  have first : 0 < 1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2 := by positivity
  exact mul_pos (Real.sqrt_pos.mpr first) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem localHeight_continuous : Continuous localHeight := by
  unfold localHeight
  fun_prop

theorem one_le_localHeight_three_part (coordinates : LocalLine × LocalLine) :
    1 ≤ max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖) := le_max_left _ _

theorem norm_natCast_three_pow_inv (j : ℕ) : ‖((3 : ℕ) : ℚ_[3]) ^ j‖⁻¹ = (3 : ℝ) ^ j := by
  rw [norm_pow, Padic.norm_p]
  simp [inv_pow]

/-- Three-adic shell decomposition: every `y` lies in the ball of radius `3^j` where
`max 1 ‖y‖ = 3^j`. -/
theorem exists_inversePowerBall_index (y : ℚ_[3]) :
    ∃ j : ℕ, y ∈ padicInversePowerBall (prime := 3) j ∧ max 1 ‖y‖ = (3 : ℝ) ^ j := by
  have ballNorm := norm_natCast_three_pow_inv
  by_cases small : ‖y‖ ≤ 1
  · refine ⟨0, ?_, by rw [pow_zero]; exact max_eq_left small⟩
    change ‖y‖ ≤ ‖((3 : ℕ) : ℚ_[3]) ^ 0‖⁻¹
    rw [ballNorm]
    simpa using small
  · have large : 1 < ‖y‖ := lt_of_not_ge small
    have nonzero : y ≠ 0 := by
      intro zero
      rw [zero, norm_zero] at large
      exact absurd large (by norm_num)
    have normValue : ‖y‖ = (3 : ℝ) ^ (-y.valuation) := by
      have := Padic.norm_eq_zpow_neg_valuation (p := 3) nonzero
      simpa using this
    have positive : 0 < -y.valuation := by
      by_contra notPositive
      have : (-y.valuation) ≤ 0 := not_lt.mp notPositive
      have bound : (3 : ℝ) ^ (-y.valuation) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) this
      rw [← normValue] at bound
      exact absurd large (not_lt.mpr bound)
    have power : (3 : ℝ) ^ ((-y.valuation).toNat) = ‖y‖ := by
      rw [normValue, ← zpow_natCast, Int.toNat_of_nonneg positive.le]
    refine ⟨(-y.valuation).toNat, ?_, ?_⟩
    · change ‖y‖ ≤ ‖((3 : ℕ) : ℚ_[3]) ^ (-y.valuation).toNat‖⁻¹
      rw [ballNorm, power]
    · rw [max_eq_right large.le, power]

/-- `max(1, |y|₃)^{-d}` is integrable for the normalized Haar measure of `ℚ₃` when `d > 1`. -/
theorem padicThree_integrable_max_one_rpow (d : ℝ) (hd : 1 < d) :
    Integrable (fun y : ℚ_[3] => (max 1 ‖y‖) ^ (-d)) normalizedLocalThreeMeasure := by
  have : normalizedLocalThreeMeasure.IsAddHaarMeasure := normalizedLocalThreeMeasure_haar
  set q : ℝ := (3 : ℝ) ^ (-d) with hq
  have qPositive : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have ratio : 3 * q < 1 := by
    have lower : (3 : ℝ) ^ (-d) < (3 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at lower
    linarith
  have measurableFunction : Measurable fun y : ℚ_[3] => (max 1 ‖y‖) ^ (-d) := by
    have : Continuous fun y : ℚ_[3] => (max 1 ‖y‖) ^ (-d) :=
      Continuous.rpow_const (continuous_const.max continuous_norm)
        (fun y => Or.inl (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')
    exact this.measurable
  refine ⟨measurableFunction.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have pointwise : ∀ y : ℚ_[3], ‖(max 1 ‖y‖) ^ (-d)‖ₑ ≤
      ∑' j : ℕ, (padicInversePowerBall (prime := 3) j).indicator
        (fun _ => ENNReal.ofReal (q ^ j)) y := by
    intro y
    obtain ⟨j, memberBall, valueEq⟩ := exists_inversePowerBall_index y
    have nonneg : 0 ≤ (max 1 ‖y‖) ^ (-d) :=
      Real.rpow_nonneg (lt_of_lt_of_le one_pos (le_max_left _ _)).le _
    rw [Real.enorm_eq_ofReal nonneg]
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem memberBall, valueEq, hq,
      ← Real.rpow_natCast, ← Real.rpow_natCast]
    apply le_of_eq
    congr 1
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      mul_comm]
  have balls : ∀ j : ℕ, MeasurableSet (padicInversePowerBall (prime := 3) j) :=
    fun j => padicInversePowerBall_measurable j
  calc ∫⁻ y, ‖(max 1 ‖y‖) ^ (-d)‖ₑ ∂normalizedLocalThreeMeasure
      ≤ ∫⁻ y, ∑' j : ℕ, (padicInversePowerBall (prime := 3) j).indicator
          (fun _ => ENNReal.ofReal (q ^ j)) y ∂normalizedLocalThreeMeasure :=
        lintegral_mono pointwise
    _ = ∑' j : ℕ, ENNReal.ofReal (q ^ j) *
          normalizedLocalThreeMeasure (padicInversePowerBall (prime := 3) j) := by
        rw [lintegral_tsum (fun j => (measurable_const.indicator (balls j)).aemeasurable)]
        exact tsum_congr fun j => lintegral_indicator_const (balls j) _
    _ = ∑' j : ℕ, ENNReal.ofReal (3 * q) ^ j := by
        refine tsum_congr fun j => ?_
        rw [padicInversePowerBall_measure normalizedLocalThreeMeasure
          normalizedLocalThreeMeasure_normalized j]
        have cast : (((3 ^ j : ℕ)) : ℝ≥0∞) = ENNReal.ofReal ((3 : ℝ) ^ j) := by
          rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
          simp
        rw [cast, ← ENNReal.ofReal_mul (pow_nonneg qPositive.le j),
          ← ENNReal.ofReal_pow (mul_pos (by norm_num : (0 : ℝ) < 3) qPositive).le]
        congr 1
        ring
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        refine ENNReal.inv_lt_top.mpr (tsub_pos_of_lt ?_)
        exact (ENNReal.ofReal_lt_one).mpr ratio

/-- `(1 + x²)^{-d/2}` is integrable on `ℝ` when `d > 1`. -/
theorem real_integrable_one_add_sq_rpow (d : ℝ) (hd : 1 < d) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-d / 2)) volume := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) (r := d)
    (by simpa using hd)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- Splitting a negative power over a pair of larger bases. -/
theorem rpow_neg_le_mul_of_le {S x y e : ℝ} (hx : 0 < x) (hy : 0 < y) (hxS : x ≤ S)
    (hyS : y ≤ S) (he : 0 ≤ e) : S ^ (-e) ≤ x ^ (-e / 2) * y ^ (-e / 2) := by
  have positive : 0 < S := lt_of_lt_of_le hx hxS
  have split : S ^ (-e) = S ^ (-e / 2) * S ^ (-e / 2) := by
    rw [← Real.rpow_add positive]
    congr 1
    ring
  rw [split]
  have nonpositive : -e / 2 ≤ 0 := by linarith
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hx hxS nonpositive)
    (Real.rpow_le_rpow_of_nonpos hy hyS nonpositive)
    (Real.rpow_nonneg positive.le _) (Real.rpow_nonneg hx.le _)

/-- The product majorant of `H^{-c}`: a function of the first line times one of the second. -/
def localLineFactor (d : ℝ) (value : LocalLine) : ℝ :=
  (1 + value.1 ^ 2) ^ (-d / 2) * (max 1 ‖value.2‖) ^ (-d)

theorem localLineFactor_integrable (d : ℝ) (hd : 1 < d) :
    Integrable (localLineFactor d) localLineMeasure := by
  let : normalizedLocalThreeMeasure.IsAddHaarMeasure := normalizedLocalThreeMeasure_haar
  exact (real_integrable_one_add_sq_rpow d hd).mul_prod (padicThree_integrable_max_one_rpow d hd)

theorem localLineFactor_nonneg (d : ℝ) (value : LocalLine) : 0 ≤ localLineFactor d value :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (lt_of_lt_of_le one_pos (le_max_left _ _)).le _)

theorem localHeight_rpow_le (c : ℝ) (hc : 0 ≤ c) (coordinates : LocalLine × LocalLine) :
    localHeight coordinates ^ (-c) ≤
      localLineFactor (c / 2) coordinates.1 * localLineFactor (c / 2) coordinates.2 := by
  unfold localHeight
  set realPart : ℝ := 1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2 with realDef
  set padicPart : ℝ := max 1 (max ‖coordinates.1.2‖ ‖coordinates.2.2‖) with padicDef
  have realPositive : 0 < realPart := by rw [realDef]; positivity
  have padicPositive : 0 < padicPart := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [Real.mul_rpow (Real.sqrt_nonneg _) padicPositive.le]
  have sqrtPower : Real.sqrt realPart ^ (-c) = realPart ^ (-(c / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul realPositive.le]
    congr 1
    ring
  rw [sqrtPower]
  have realBound : realPart ^ (-(c / 2)) ≤ (1 + coordinates.1.1 ^ 2) ^ (-(c / 2) / 2) *
      (1 + coordinates.2.1 ^ 2) ^ (-(c / 2) / 2) := by
    have := rpow_neg_le_mul_of_le (S := realPart) (x := 1 + coordinates.1.1 ^ 2)
      (y := 1 + coordinates.2.1 ^ 2) (e := c / 2) (by positivity) (by positivity)
      (by rw [realDef]; nlinarith [sq_nonneg coordinates.2.1])
      (by rw [realDef]; nlinarith [sq_nonneg coordinates.1.1]) (by linarith)
    exact this
  have padicBound : padicPart ^ (-c) ≤ (max 1 ‖coordinates.1.2‖) ^ (-(c / 2)) *
      (max 1 ‖coordinates.2.2‖) ^ (-(c / 2)) := by
    have := rpow_neg_le_mul_of_le (S := padicPart) (x := max 1 ‖coordinates.1.2‖)
      (y := max 1 ‖coordinates.2.2‖) (e := c) (lt_of_lt_of_le one_pos (le_max_left _ _))
      (lt_of_lt_of_le one_pos (le_max_left _ _))
      (max_le_max le_rfl (le_max_left _ _)) (max_le_max le_rfl (le_max_right _ _)) hc
    have halve : -c / 2 = -(c / 2) := by ring
    rwa [halve] at this
  unfold localLineFactor
  calc realPart ^ (-(c / 2)) * padicPart ^ (-c)
      ≤ ((1 + coordinates.1.1 ^ 2) ^ (-(c / 2) / 2) *
          (1 + coordinates.2.1 ^ 2) ^ (-(c / 2) / 2)) *
        ((max 1 ‖coordinates.1.2‖) ^ (-(c / 2)) * (max 1 ‖coordinates.2.2‖) ^ (-(c / 2))) :=
        mul_le_mul realBound padicBound (Real.rpow_nonneg padicPositive.le _)
          (by positivity)
    _ = _ := by ring

/-- `H^{-c}` is integrable on the local radical exactly in the range `c > 2`. -/
theorem localHeight_rpow_integrable (c : ℝ) (hc : 2 < c) :
    Integrable (fun coordinates => localHeight coordinates ^ (-c)) localRadicalMeasure := by
  have factor : 1 < c / 2 := by linarith
  have majorant : Integrable (fun coordinates : LocalLine × LocalLine =>
      localLineFactor (c / 2) coordinates.1 * localLineFactor (c / 2) coordinates.2)
      localRadicalMeasure :=
    (localLineFactor_integrable (c / 2) factor).mul_prod (localLineFactor_integrable (c / 2) factor)
  refine majorant.mono' ?_ (Filter.Eventually.of_forall fun coordinates => ?_)
  · exact ((localHeight_continuous.rpow_const
      (fun coordinates => Or.inl (localHeight_pos coordinates).ne')).aestronglyMeasurable)
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (localHeight_pos coordinates).le _)]
    exact localHeight_rpow_le c (by linarith) coordinates

/-- A measurable function dominated by a constant times `H^{-c}`, `c > 2`, is integrable on the
local radical: the form in which the norm majorant of the local standard integrand is used. -/
theorem integrable_of_norm_le_localHeight_rpow {E : Type*} [NormedAddCommGroup E]
    (function : LocalLine × LocalLine → E)
    (measurable : AEStronglyMeasurable function localRadicalMeasure) (c bound : ℝ) (hc : 2 < c)
    (dominated : ∀ coordinates, ‖function coordinates‖ ≤ bound * localHeight coordinates ^ (-c)) :
    Integrable function localRadicalMeasure :=
  ((localHeight_rpow_integrable c hc).const_mul bound).mono' measurable
    (Filter.Eventually.of_forall dominated)

end TernaryPeriodPolynomials.EdgeConvergence
