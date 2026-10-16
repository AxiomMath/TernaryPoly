module

public import TernaryPeriodPolynomials.ModularForm.Period.Basic

@[expose] public section


noncomputable section
open Complex MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- The literal outer coefficient in the paper's `(zY-X)^d` convention. -/
theorem coeff_oddPeriod_extreme_LSeries {d : ℕ} (hd : 4 < d) (f : Forms d) :
    (oddPeriod f).coeff (exponent d 1) =
      (-(d : ℂ) * I ^ d * Gamma (d : ℂ) / (2 * (Real.pi : ℂ)) ^ d) *
        LSeries (coefficients f) (d : ℂ) := by
  rw [coeff_oddPeriod_extreme (by omega), moment_nat_eq (by omega), lseries_eq_L hd]
  ring

/-- The scalar multiplying the critical L-value is nonzero. -/
theorem extreme_scalar_ne_zero {d : ℕ} (hd : 0 < d) :
    (-(d : ℂ) * I ^ d * Gamma (d : ℂ) / (2 * (Real.pi : ℂ)) ^ d) ≠ 0 := by
  apply div_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hd)))
        (pow_ne_zero _ I_ne_zero)
    · exact Gamma_ne_zero_of_re_pos (by
        simpa only [natCast_re] using (show (0 : ℝ) < d by exact_mod_cast hd))
  · exact pow_ne_zero _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))

/-- Vanishing of the literal extreme coefficient is exactly vanishing of the critical L-value. -/
theorem coeff_oddPeriod_extreme_eq_zero_iff {d : ℕ} (hd : 4 < d) (f : Forms d) :
    (oddPeriod f).coeff (exponent d 1) = 0 ↔ LSeries (coefficients f) (d : ℂ) = 0 := by
  rw [coeff_oddPeriod_extreme_LSeries hd]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (extreme_scalar_ne_zero (show 0 < d by omega))
  · intro h
    rw [h, mul_zero]

/-- An actual cusp-form consumer of both the finite coefficient theorem and absolute convergence.
The parity hypothesis is unnecessary for this identity, so the result applies in particular to
all even `d` (equivalently all even weights `d+2`). -/
theorem actual_cusp_outer_coefficient_and_summability {d : ℕ} (hd : 4 < d) (f : Forms d) :
    (oddPeriod f).IsHomogeneous d ∧
    (oddPeriod f).coeff (exponent d 1) =
      (-(d : ℂ) * I ^ d * Gamma (d : ℂ) / (2 * (Real.pi : ℂ)) ^ d) *
        LSeries (coefficients f) (d : ℂ) ∧
    Summable (fun n => ‖LSeries.term (coefficients f) (d : ℂ) n‖) :=
  ⟨oddPeriod_isHomogeneous f, coeff_oddPeriod_extreme_LSeries hd f, norm_terms_summable hd f⟩

end TernaryPoly.BinaryCuspPeriod
