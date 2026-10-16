module

public import Mathlib

@[expose] public section


/-!
# Continuous linear maps commute with iterated interval integrals

(the average
"is a cochain map": it commutes with the constant-coefficient operators `d`, pullbacks and
coefficient twists).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- A continuous linear map commutes with an iterated interval integral of a continuous function. -/
theorem iterIntegral_clm_comm (L : A →L[ℝ] B) (g : ℝ → ℝ → A)
    (hg : Continuous (Function.uncurry g)) :
    L (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, g a b) = ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, L (g a b) := by
  have hin : ∀ a, IntervalIntegrable (fun b => g a b) volume 0 1 := fun a =>
    (hg.comp (Continuous.prodMk_right a)).intervalIntegrable 0 1
  have hcont : Continuous fun a => ∫ b in (0:ℝ)..1, g a b :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 1
  rw [← L.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)]
  refine intervalIntegral.integral_congr fun a _ => ?_
  exact (L.intervalIntegral_comp_comm (hin a)).symm

end TernaryPeriodPolynomials.Argument.EisensteinClass
