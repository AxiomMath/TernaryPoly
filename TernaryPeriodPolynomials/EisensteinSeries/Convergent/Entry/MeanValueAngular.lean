module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.AngularExp
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Integrability
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section


/-!
# The angular integrand of the real entry as a polynomial in `e^{2iθ}`, and the mean value

For `k = n + 3` the angular integrand `e^{ikθ}(c - irv)³(c - iv/r)ⁿ` of Appendix C.5
(`angularIntegrand`) is the polynomial `Q_r(ζ)³ Q_{1/r}(ζ)ⁿ` evaluated at `ζ = e^{2iθ}`, where
`Q_a(ζ) = ((1 - a)ζ + (1 + a))/2`, because `c - iav = e^{-iθ} Q_a(e^{2iθ})`.  Hence it contains only
the frequencies `0, 2, …, 2k` in `θ`.  Against a function holomorphic on a disc of radius `> 1` the
mean value property kills all positive frequencies, so only the constant term survives
(`integral_comp_exp_two_mul`).  This is the mechanism by which the real entry of a general
holomorphic `h` is `h(i)` times the value for `h₀ = (τ + i)^{-(n+3)}`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument MeasureTheory Set

/-- `Q_a(ζ) = ((1 - a)ζ + (1 + a))/2`. -/
def entryQ (a : ℝ) (ζ : ℂ) : ℂ := ((1 - (a : ℂ)) * ζ + (1 + (a : ℂ))) / 2

/-- The polynomial `Q_r(ζ)³ Q_{1/r}(ζ)ⁿ` whose value at `ζ = e^{2iθ}` is `angularIntegrand n r θ`. -/
def entryAngularPoly (n : ℕ) (r : ℝ) (ζ : ℂ) : ℂ :=
  entryQ r ζ ^ 3 * entryQ r⁻¹ ζ ^ n

/-- `cos θ - i a sin θ = e^{-iθ} Q_a(e^{2iθ})`. -/
theorem cos_sub_I_mul_sin_eq_exp_mul_entryQ (b : ℝ) (θ : ℝ) :
    (Real.cos θ : ℂ) - Complex.I * (b : ℂ) * (Real.sin θ : ℂ) =
      Complex.exp (-(Complex.I * θ)) * entryQ b (Complex.exp (2 * Complex.I * θ)) := by
  rw [cos_sub_I_mul_mul_sin_eq b θ, entryQ]
  have e : Complex.exp (-(Complex.I * (θ : ℂ))) * Complex.exp (2 * Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination (1 - (b : ℂ)) / 2 * (-e)

/-- `angularIntegrand n r θ = Q_r(e^{2iθ})³ Q_{1/r}(e^{2iθ})ⁿ`. -/
theorem angularIntegrand_eq_entryAngularPoly (n : ℕ) (r θ : ℝ) :
    angularIntegrand n r θ = entryAngularPoly n r (Complex.exp (2 * Complex.I * θ)) := by
  unfold angularIntegrand entryAngularPoly
  have h1 := cos_sub_I_mul_sin_eq_exp_mul_entryQ r θ
  have h2 := cos_sub_I_mul_sin_eq_exp_mul_entryQ r⁻¹ θ
  have h2' : (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) / (r : ℂ) =
      Complex.exp (-(Complex.I * θ)) * entryQ r⁻¹ (Complex.exp (2 * Complex.I * θ)) := by
    rw [← h2]; push_cast; ring
  have hEE : Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-(Complex.I * (θ : ℂ))) = 1 := by
    rw [← Complex.exp_add]; simp
  have hexp : Complex.exp (Complex.I * ((n : ℂ) + 3) * (θ : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) ^ (n + 3) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h1, h2', hexp]
  calc Complex.exp (Complex.I * (θ : ℂ)) ^ (n + 3) *
        (Complex.exp (-(Complex.I * θ)) * entryQ r (Complex.exp (2 * Complex.I * θ))) ^ 3 *
        (Complex.exp (-(Complex.I * θ)) * entryQ r⁻¹ (Complex.exp (2 * Complex.I * θ))) ^ n
      = (Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-(Complex.I * (θ : ℂ)))) ^ (n + 3) *
        entryQ r (Complex.exp (2 * Complex.I * θ)) ^ 3 *
          entryQ r⁻¹ (Complex.exp (2 * Complex.I * θ)) ^ n := by ring
    _ = _ := by rw [hEE]; simp

/-- Mean value over the doubled angle: for `Ψ` holomorphic on a neighbourhood of the closed unit
disc, `∫_{-π}^{π} Ψ(e^{2iθ}) dθ = 2π Ψ(0)`. -/
theorem integral_comp_exp_two_mul (Ψ : ℂ → ℂ) (hΨ : DiffContOnCl ℂ Ψ (Metric.ball 0 1)) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, Ψ (Complex.exp (2 * Complex.I * θ)) =
      2 * Real.pi * Ψ 0 := by
  set g : ℝ → ℂ := fun θ => Ψ (circleMap 0 1 θ) with hg
  have hcont : Continuous g := by
    have hcl : ContinuousOn Ψ (Metric.closedBall 0 1) := by
      simpa [closure_ball (0 : ℂ) one_ne_zero] using hΨ.2
    refine hcl.comp_continuous (continuous_circleMap 0 1) (fun θ => ?_)
    simp [circleMap]
  have hper : Function.Periodic g (2 * Real.pi) := fun θ => by
    simp only [hg]; rw [periodic_circleMap 0 1 θ]
  have hmean : ∫ θ in (0 : ℝ)..2 * Real.pi, g θ = 2 * Real.pi * Ψ 0 := by
    have hΨ' : DiffContOnCl ℂ Ψ (Metric.ball 0 |(1 : ℝ)|) := by rwa [abs_one]
    have h := DiffContOnCl.circleAverage (R := 1) hΨ'
    rw [Real.circleAverage_def, inv_smul_eq_iff₀ (by positivity)] at h
    rw [Complex.real_smul] at h
    simpa [hg] using h
  have hrewrite : ∀ θ : ℝ, Ψ (Complex.exp (2 * Complex.I * θ)) = g (2 * θ) := by
    intro θ
    simp only [hg, circleMap, zero_add]
    congr 1
    push_cast
    ring_nf
  have hab : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  simp_rw [hrewrite]
  rw [intervalIntegral.integral_comp_mul_left (fun x => g x) (two_ne_zero)]
  have hsplit : ∫ x in (2 * -Real.pi)..(2 * Real.pi), g x =
      (∫ x in (2 * -Real.pi)..0, g x) + ∫ x in (0 : ℝ)..(2 * Real.pi), g x :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hshift : ∫ x in (2 * -Real.pi)..0, g x = ∫ x in (0 : ℝ)..(2 * Real.pi), g x := by
    have := hper.intervalIntegral_add_eq (2 * -Real.pi) 0
    rw [show 2 * -Real.pi + 2 * Real.pi = 0 by ring, zero_add] at this
    exact this
  rw [hsplit, hshift, hmean]
  simp
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
