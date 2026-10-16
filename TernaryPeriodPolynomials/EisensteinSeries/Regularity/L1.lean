module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.BergmanCore

@[expose] public section


/-!
# The weighted `L¹` integral of a Bergman vector

`l1Integral F = ∫ ‖F w‖ |Im w|^(k/2) dμ_hyp(w)`. It controls the realization integral of `F`
(the evaluation functionals of a finite-adelic model are bounded at each level), and it is finite
for vectors with two continuous rotation derivatives (`Sobolev.lean`). `L1Finite F` records its
finiteness; it is stable under linear combinations.
-/

noncomputable section

open MeasureTheory

namespace TernaryPeriodPolynomials.Regularity

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The weighted `L¹` integral `∫ ‖F w‖ |Im w|^(k/2) dμ_hyp(w)`. -/
def l1Integral (F : BergmanSpace k E) : ENNReal :=
  ∫⁻ w, ENNReal.ofReal (‖F w‖ * |w.im| ^ ((k : ℝ) / 2)) ∂hypMeasure

/-- Finiteness of the weighted `L¹` integral. -/
def L1Finite (F : BergmanSpace k E) : Prop := l1Integral F ≠ ⊤

theorem aestronglyMeasurable_l1 (F : BergmanSpace k E) :
    AEStronglyMeasurable (fun w : ℂ => ‖F w‖ * |w.im| ^ ((k : ℝ) / 2)) hypMeasure :=
  BergmanAux.aesm (((BergmanSpace.continuousOn F).norm).mul
    ((Complex.continuous_im.abs.rpow_const fun _ => Or.inr (by positivity)).continuousOn))

/-- A vector with finite weighted `L¹` integral gives an integrable weighted norm. -/
theorem L1Finite.integrable {F : BergmanSpace k E} (hF : L1Finite F) :
    Integrable (fun w : ℂ => ‖F w‖ * |w.im| ^ ((k : ℝ) / 2)) hypMeasure := by
  refine ⟨aestronglyMeasurable_l1 F, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => by positivity)]
  exact lt_top_iff_ne_top.mpr hF

theorem l1Integral_add_le (F G : BergmanSpace k E) :
    l1Integral (F + G) ≤ l1Integral F + l1Integral G := by
  rw [l1Integral, l1Integral, l1Integral, ← lintegral_add_left' ?_]
  · refine lintegral_mono fun w => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact norm_add_le _ _
  · exact (aestronglyMeasurable_l1 F).aemeasurable.ennreal_ofReal

theorem l1Integral_smul (c : ℂ) (F : BergmanSpace k E) :
    l1Integral (c • F) = ENNReal.ofReal ‖c‖ * l1Integral F := by
  rw [l1Integral, l1Integral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg c), BergmanSpace.smul_apply, norm_smul, mul_assoc]

theorem L1Finite.add {F G : BergmanSpace k E} (hF : L1Finite F) (hG : L1Finite G) :
    L1Finite (F + G) :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hF, hG⟩) (l1Integral_add_le F G)

theorem L1Finite.smul (c : ℂ) {F : BergmanSpace k E} (hF : L1Finite F) : L1Finite (c • F) := by
  rw [L1Finite, l1Integral_smul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF

end TernaryPeriodPolynomials.Regularity

end
