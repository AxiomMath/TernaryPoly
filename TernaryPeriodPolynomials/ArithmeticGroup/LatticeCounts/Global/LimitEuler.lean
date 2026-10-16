module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitProduct

@[expose] public section


/-!
# Global limit: the Euler product bound

For `b > 3`, `∏_{w∈S} (1 - p_w^(2-b))⁻¹ ≤ M` for every finite set `S` of places, with `M = exp(2 Σ_w p_w^(2-b))` (the series converges since `b - 2 > 1`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open scoped ENNReal

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitEuler

theorem inv_one_sub_le_exp {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1 / 2) : (1 - q)⁻¹ ≤ Real.exp (2 * q) := by
  have h2 : (1 - q)⁻¹ ≤ 1 + 2 * q := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith [Real.add_one_le_exp (2 * q)]

theorem primesEquiv_val_injective :
    Function.Injective (fun w : FinitePlace => (Rat.HeightOneSpectrum.primesEquiv w).val) :=
  fun _ _ h => (Rat.HeightOneSpectrum.primesEquiv).injective (Subtype.val_injective h)

theorem euler_bound (b : ℝ) (hb : 3 < b) :
    ∃ M : ℝ, ∀ S : Finset FinitePlace,
      ∏ w ∈ S, ENNReal.ofReal ((1 - (((Rat.HeightOneSpectrum.primesEquiv w).val : ℕ) : ℝ) ^ (2 - b))⁻¹) ≤
        ENNReal.ofReal M := by
  set f : FinitePlace → ℝ := fun w => (((Rat.HeightOneSpectrum.primesEquiv w).val : ℕ) : ℝ) ^ (2 - b) with hf
  have hf0 : ∀ w, 0 ≤ f w := fun w => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hf1 : ∀ w, f w ≤ 1 / 2 := by
    intro w
    have hp : (2 : ℝ) ≤ (((Rat.HeightOneSpectrum.primesEquiv w).val : ℕ) : ℝ) :=
      Nat.ofNat_le_cast.2 (Rat.HeightOneSpectrum.primesEquiv w).2.two_le
    calc f w ≤ (2 : ℝ) ^ (2 - b) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hsum : Summable f := by
    have hg : Summable (fun n : ℕ => (n : ℝ) ^ (2 - b)) := Real.summable_nat_rpow.2 (by linarith)
    exact hg.comp_injective primesEquiv_val_injective
  refine ⟨Real.exp (2 * ∑' w, f w), fun S => ?_⟩
  have hnn : ∀ w, 0 ≤ (1 - f w)⁻¹ := fun w => inv_nonneg.2 (by linarith [hf1 w])
  calc ∏ w ∈ S, ENNReal.ofReal ((1 - f w)⁻¹) = ENNReal.ofReal (∏ w ∈ S, (1 - f w)⁻¹) :=
        (ENNReal.ofReal_prod_of_nonneg fun w _ => hnn w).symm
    _ ≤ ENNReal.ofReal (Real.exp (2 * ∑' w, f w)) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∏ w ∈ S, (1 - f w)⁻¹ ≤ ∏ w ∈ S, Real.exp (2 * f w) :=
              Finset.prod_le_prod₀ (fun w _ => hnn w) fun w _ => inv_one_sub_le_exp (hf0 w) (hf1 w)
          _ = Real.exp (2 * ∑ w ∈ S, f w) := by
              rw [← Real.exp_sum, ← Finset.mul_sum]
          _ ≤ Real.exp (2 * ∑' w, f w) := by
              apply Real.exp_le_exp.2
              have := hsum.sum_le_tsum S (fun w _ => hf0 w)
              linarith

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitEuler
