module

public import TernaryPeriodPolynomials.ModularForm.BinaryCuspOuter

@[expose] public section


noncomputable section
open Complex MeasureTheory
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- Integer Mellin moments are literal integrals on the positive real axis. -/
theorem moment_succ_eq_integral {d : ℕ} (f : Forms d) (m : ℕ) :
    moment f (m + 1 : ℕ) =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ m * f (ofComplex (I * t)) := by
  unfold moment mellin
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, cpow_natCast, smul_eq_mul]

/-- Parameterization of `∫₀^{i∞} f(z) z^m dz` by `z = i*t`, including `dz = i*dt`. -/
def axisMoment {d : ℕ} (f : Forms d) (m : ℕ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, f (ofComplex (I * t)) * (I * (t : ℂ)) ^ m * I

/-- The phase of the actual imaginary-axis integral is `i^(m+1)`. -/
theorem axisMoment_eq {d : ℕ} (f : Forms d) (m : ℕ) :
    axisMoment f m = I ^ (m + 1) * moment f (m + 1 : ℕ) := by
  rw [axisMoment, moment_succ_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [mul_pow, pow_succ]
  ring

end TernaryPoly.BinaryCuspPeriod
