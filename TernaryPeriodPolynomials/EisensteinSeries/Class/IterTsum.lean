module

public import Mathlib

@[expose] public section


/-!
# Exchange of an infinite sum with the iterated integral over the unit square

Paper: "the integrated
radical quotient is compact, so Fubini applies": the average over the compact radical torus commutes
with the absolutely convergent sum over cosets.

`tsum_iterIntegral`: for continuous functions on the unit square dominated by a summable family, the
sum of the iterated integrals is the iterated integral of the sum.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One-variable exchange of a sum with the interval integral over `[0, 1]`. -/
theorem tsum_intervalIntegral_unit {ι : Type*} [Countable ι] (F : ι → ℝ → E)
    (hF : ∀ i, Continuous (F i)) (B : ι → ℝ) (hB : Summable B)
    (hFB : ∀ i b, b ∈ Icc (0:ℝ) 1 → ‖F i b‖ ≤ B i) :
    (∑' i, ∫ b in (0:ℝ)..1, F i b) = ∫ b in (0:ℝ)..1, ∑' i, F i b := by
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  have hint : ∀ i, Integrable (F i) (volume.restrict (Ioc (0:ℝ) 1)) := fun i =>
    ((hF i).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hbd : ∀ i, ∫ b in Ioc (0:ℝ) 1, ‖F i b‖ ≤ B i := by
    intro i
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0:ℝ) 1)
      (f := fun b => ‖F i b‖) (C := B i) (by simp) (fun b hb => by
        simpa using hFB i b (Ioc_subset_Icc_self hb))
    refine le_trans (le_abs_self _) (le_trans (by simpa using this) ?_)
    simp
  have hsum : Summable fun i => ∫ b in Ioc (0:ℝ) 1, ‖F i b‖ :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun b => norm_nonneg _) hbd hB
  exact integral_tsum_of_summable_integral_norm hint hsum

/-- **Exchange of a sum with the iterated integral over the unit square.** -/
theorem tsum_iterIntegral {ι : Type*} [Countable ι] [CompleteSpace E] (F : ι → ℝ → ℝ → E)
    (hF : ∀ i, Continuous (Function.uncurry (F i))) (B : ι → ℝ) (hB : Summable B)
    (hFB : ∀ i a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → ‖F i a b‖ ≤ B i) :
    (∑' i, ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, F i a b) =
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∑' i, F i a b := by
  have hG : ∀ i, Continuous fun a => ∫ b in (0:ℝ)..1, F i a b := fun i =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hF i) 0 1
  have hGB : ∀ i a, a ∈ Icc (0:ℝ) 1 → ‖∫ b in (0:ℝ)..1, F i a b‖ ≤ B i := by
    intro i a ha
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun b => F i a b) (C := B i) (fun b hb => by
        rw [uIoc_of_le zero_le_one] at hb
        exact hFB i a b ha (Ioc_subset_Icc_self hb))
    simpa using this
  rw [tsum_intervalIntegral_unit (fun i a => ∫ b in (0:ℝ)..1, F i a b) hG B hB hGB]
  refine intervalIntegral.integral_congr fun a ha => ?_
  rw [uIcc_of_le zero_le_one] at ha
  exact tsum_intervalIntegral_unit (fun i b => F i a b)
    (fun i => (hF i).comp (Continuous.prodMk_right a)) B hB (fun i b hb => hFB i a b ha hb)

end

end TernaryPeriodPolynomials.Argument.EisensteinClass
