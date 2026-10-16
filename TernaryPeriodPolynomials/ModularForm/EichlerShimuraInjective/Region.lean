module

public import Mathlib

@[expose] public section


/-!
# Truncated fundamental domain of `SL₂(ℤ)`: arcs and region

The arc `x ↦ √(1-x²)` and the compact region `regionF T = {|x| ≤ 1/2, √(1-x²) ≤ y ≤ T}` of the upper half plane.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open scoped ComplexConjugate


/-- The lower boundary arc `x ↦ √(1-x²)` of the standard fundamental domain. -/
def arcY (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

theorem arcY_continuous : Continuous arcY := by unfold arcY; fun_prop

theorem arcY_nonneg (x : ℝ) : 0 ≤ arcY x := Real.sqrt_nonneg _

theorem arcY_le_one (x : ℝ) : arcY x ≤ 1 := by
  unfold arcY
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg x]

theorem sqrt3_div_two_le_arcY {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.sqrt 3 / 2 ≤ arcY x := by
  unfold arcY
  have h3 : Real.sqrt 3 / 2 = Real.sqrt (3 / 4) := by
    rw [Real.sqrt_div (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h3]
  apply Real.sqrt_le_sqrt
  have : x ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hx
    nlinarith
  linarith

/-- The set `{(x, y) | |x| ≤ 1/2, √(1-x²) ≤ y ≤ T}`. -/
def regionF (T : ℝ) : Set (ℝ × ℝ) :=
  {p | -1 / 2 ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ arcY p.1 ≤ p.2 ∧ p.2 ≤ T}

theorem regionF_closed (T : ℝ) : IsClosed (regionF T) := by
  have h1 : IsClosed {p : ℝ × ℝ | -1 / 2 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | p.1 ≤ 1 / 2} := isClosed_le continuous_fst continuous_const
  have h3 : IsClosed {p : ℝ × ℝ | arcY p.1 ≤ p.2} :=
    isClosed_le (arcY_continuous.comp continuous_fst) continuous_snd
  have h4 : IsClosed {p : ℝ × ℝ | p.2 ≤ T} := isClosed_le continuous_snd continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

theorem regionF_subset (T : ℝ) : regionF T ⊆ Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc 0 T := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨⟨h1, h2⟩, (arcY_nonneg x).trans h3, h4⟩

theorem regionF_compact (T : ℝ) : IsCompact (regionF T) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (regionF_closed T) (regionF_subset T)


/-- The mirror function `y ↦ √(1-y²)` of the arc. -/
def arcX (y : ℝ) : ℝ := Real.sqrt (1 - y ^ 2)

theorem arcX_nonneg (y : ℝ) : 0 ≤ arcX y := Real.sqrt_nonneg _

theorem arcX_le_half {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) : arcX y ≤ 1 / 2 := by
  unfold arcX
  have h3 : (1 : ℝ) / 2 = Real.sqrt (1 / 4) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h3]
  apply Real.sqrt_le_sqrt
  have h0 : 0 ≤ Real.sqrt 3 / 2 := by positivity
  have : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith [sq_nonneg y]

theorem arcY_le_iff {x y : ℝ} (hy : 0 ≤ y) : arcY x ≤ y ↔ arcX y ≤ |x| := by
  unfold arcY arcX
  rw [Real.sqrt_le_left hy, Real.sqrt_le_left (abs_nonneg x), sq_abs]
  constructor <;> intro h <;> nlinarith

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
