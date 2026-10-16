module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityParam
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValueInner
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.RadialIntegral
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PolarPointwise

@[expose] public section


/-!
# The angular and radial integrals of the seed's frame coefficient at the base point

`integral_comp_exp`: the mean value `∫_{-π}^{π} Ψ(e^{iθ}) dθ = 2πΨ(0)` for `Ψ` holomorphic near the closed disc.
`angular_integral_coeff`: for every monomial `m` of degree `n` and every pair of tangent directions `V, W`, the angular
integral over the polar circle of radius `ρ` of the `m`-th coefficient of `ω̃_h(L_{s,t})(V,W)` is
`ρ K_m(r) · 2π · F(0) · xiPoly m 0 · wedgePoly (V+Vᵀ) (W+Wᵀ) 0`, `F(0) = (2i)^{n+3} h(i)`
(only the constant mode of the holomorphic function `ξ ↦ F(ξ²) xiPoly wedgePoly` survives);
`iterated_integral_coeff`: the radial integral (`radial_integral : ∫ ρ (1+ρ²)^{-(n+3)/2} = 1/(n+1)`) then gives
`c_∞ · h(i) · multinomial(m) · xiPoly m 0 · (A∧B)(V+Vᵀ, W+Wᵀ)`, `c_∞ = -2πi/(n+1)`, where
`(A∧B)(p,p')` (`linePair`) is the pairing of the line seed `h(τ)(τZ-Y)ⁿ(τ dw₁+dw₂)∧dτ` at its base point.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex MvPolynomial MeasureTheory Set TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

/-- Mean value over the circle: for `Ψ` holomorphic on a neighbourhood of the closed unit disc,
`∫_{-π}^{π} Ψ(e^{iθ}) dθ = 2π Ψ(0)`. -/
theorem integral_comp_exp (Ψ : ℂ → ℂ) (hΨ : DiffContOnCl ℂ Ψ (Metric.ball 0 1)) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, Ψ (Complex.exp (Complex.I * θ)) = 2 * Real.pi * Ψ 0 := by
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
  have hrewrite : ∀ θ : ℝ, Ψ (Complex.exp (Complex.I * θ)) = g θ := by
    intro θ
    simp only [hg, circleMap, zero_add]
    congr 1
    push_cast
    ring_nf
  have hab : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  simp_rw [hrewrite]
  have := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
  rw [this, hmean]


theorem xiPoly_differentiable (m : Fin 3 →₀ ℕ) : Differentiable ℂ (xiPoly m) := by
  unfold xiPoly; fun_prop

theorem wedgePoly_differentiable (p p' : Matrix (Fin 3) (Fin 3) ℝ) :
    Differentiable ℂ (wedgePoly p p') := by
  unfold wedgePoly; fun_prop

/-- On the polar circle of radius `ρ`, `ξ = (ρ/(r+1)) e^{iθ}`. -/
theorem xiOf_polar (ρ θ : ℝ) :
    xiOf (ρ * Real.sin θ) (ρ * Real.cos θ) =
      ((ρ / (Real.sqrt (1 + ρ ^ 2) + 1) : ℝ) : ℂ) * Complex.exp (Complex.I * θ) := by
  have hr : entryRadius (ρ * Real.sin θ, ρ * Real.cos θ) = Real.sqrt (1 + ρ ^ 2) := by
    unfold entryRadius
    have heq : 1 + (ρ * Real.sin θ) ^ 2 + (ρ * Real.cos θ) ^ 2 = 1 + ρ ^ 2 := by
      linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ
    rw [heq]
  unfold xiOf
  rw [hr, mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I]
  push_cast
  have : (Real.sqrt (1 + ρ ^ 2) : ℂ) + 1 ≠ 0 := by
    have h1 : (0 : ℝ) < Real.sqrt (1 + ρ ^ 2) + 1 := by positivity
    exact_mod_cast h1.ne'
  field_simp

theorem polar_ne_zero (ρ θ : ℝ) (hρ : 0 < ρ) : ((ρ * Real.sin θ, ρ * Real.cos θ) : ℝ × ℝ) ≠ (0, 0) := by
  intro h0
  have h1 : ρ * Real.sin θ = 0 := congrArg Prod.fst h0
  have h2 : ρ * Real.cos θ = 0 := congrArg Prod.snd h0
  have h3 : Real.sin θ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hρ.ne'
    · exact h
  have h4 : Real.cos θ = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hρ.ne'
    · exact h
  have := Real.sin_sq_add_cos_sq θ
  rw [h3, h4] at this
  norm_num at this


/-- The scalar `K_m(r) = multinomial(m) (i/2) (2i)^{-(n+3)} r^{-(n+3)}`. -/
def baseK (n : ℕ) (m : Fin 3 →₀ ℕ) (r : ℝ) : ℂ :=
  (m.multinomial : ℂ) * (Complex.I / 2) * ((2 * Complex.I) ^ (n + 3))⁻¹ * ((r : ℂ) ^ (n + 3))⁻¹

theorem entryRadius_polar' (ρ θ : ℝ) :
    entryRadius (ρ * Real.sin θ, ρ * Real.cos θ) = Real.sqrt (1 + ρ ^ 2) := by
  unfold entryRadius
  have heq : 1 + (ρ * Real.sin θ) ^ 2 + (ρ * Real.cos θ) ^ 2 = 1 + ρ ^ 2 := by
    linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [heq]

/-- **The angular integral of a coefficient of the seed's frame coefficient** (mean value in `ε = e^{iθ}`):
only the constant term `F(0) · xiPoly m 0 · wedgePoly p p' 0` survives. -/
theorem angular_integral_coeff (n : ℕ) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (m : Fin 3 →₀ ℕ) (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ • (frameCoefficient (seedForm n h) (entryFrame (ρ * Real.sin θ) (ρ * Real.cos θ)) V W).coeff m =
      (ρ : ℂ) * baseK n m (Real.sqrt (1 + ρ ^ 2)) *
        (2 * Real.pi * (entryDiscFn n h 0 *
          (xiPoly m 0 * wedgePoly (V + V.transpose) (W + W.transpose) 0))) := by
  set r := Real.sqrt (1 + ρ ^ 2) with hr_def
  have hr2 : r ^ 2 = 1 + ρ ^ 2 := Real.sq_sqrt (by positivity)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg ρ]
  set c : ℂ := ((ρ / (r + 1) : ℝ) : ℂ) with hc
  have hcnorm : ‖c‖ < 1 := by
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_lt_one (by linarith)]
    nlinarith
  set Ψ : ℂ → ℂ := fun ε => entryDiscFn n h ((c * ε) ^ 2) *
    (xiPoly m (c * ε) * wedgePoly (V + V.transpose) (W + W.transpose) (c * ε)) with hΨdef
  have hdiff : DifferentiableOn ℂ Ψ (Metric.closedBall 0 1) := by
    have hmaps : Set.MapsTo (fun ε : ℂ => (c * ε) ^ 2) (Metric.closedBall 0 1) (Metric.ball 0 1) := by
      intro ε hε
      rw [mem_ball_zero_iff, norm_pow, norm_mul]
      rw [mem_closedBall_zero_iff] at hε
      have h0 : 0 ≤ ‖c‖ := norm_nonneg _
      have : ‖c‖ * ‖ε‖ < 1 := by nlinarith
      exact pow_lt_one₀ (by positivity) this (by norm_num)
    refine ((entryDiscFn_differentiableOn n h hh).comp
      (by fun_prop : DifferentiableOn ℂ (fun ε : ℂ => (c * ε) ^ 2) _) hmaps).mul ?_
    refine DifferentiableOn.mul ?_ ?_
    · exact (xiPoly_differentiable m).comp_differentiableOn (by fun_prop)
    · exact (wedgePoly_differentiable _ _).comp_differentiableOn (by fun_prop)
  have hΨ : DiffContOnCl ℂ Ψ (Metric.ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hdiff
  have pt : ∀ θ : ℝ, ρ • (frameCoefficient (seedForm n h) (entryFrame (ρ * Real.sin θ) (ρ * Real.cos θ)) V W).coeff m =
      ((ρ : ℂ) * baseK n m r) * Ψ (Complex.exp (Complex.I * θ)) := by
    intro θ
    rw [Complex.real_smul, coeff_frameCoefficient_xi n h m hm V W _ _ (polar_ne_zero ρ θ hρ),
      xiOf_polar, entryRadius_polar']
    simp only [hΨdef, baseK, hc]
    ring
  simp_rw [pt]
  rw [MeasureTheory.integral_const_mul, integral_comp_exp Ψ hΨ]
  simp only [hΨdef, mul_zero, zero_pow two_ne_zero]


/-- The pairing `(A ∧ B)(p, p')` of the line seed at the base point, `A = i dp₀₁ + dp₀₂`,
`B = dp₁₂ + (i/2)(dp₁₁ - dp₂₂)`. -/
def linePair (p p' : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  (Complex.I * p 0 1 + p 0 2) * ((p' 1 2 : ℂ) + Complex.I / 2 * (p' 1 1 - p' 2 2)) -
    (Complex.I * p' 0 1 + p' 0 2) * ((p 1 2 : ℂ) + Complex.I / 2 * (p 1 1 - p 2 2))

theorem wedgePoly_zero (p p' : Matrix (Fin 3) (Fin 3) ℝ) : wedgePoly p p' 0 = -2 * linePair p p' := by
  unfold wedgePoly linePair dirW dirCoef
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem xiPoly_zero (m : Fin 3 →₀ ℕ) :
    xiPoly m 0 = if m 0 = 0 then (-1) ^ (m 1) * Complex.I ^ (m 2) else 0 := by
  unfold xiPoly
  by_cases h0 : m 0 = 0
  · simp [h0]
  · simp [h0, zero_pow h0]


/-- **The iterated polar integral of a coefficient of the seed's frame coefficient at the base point**:
`= c_∞ · h(i) · multinomial(m) · xiPoly m 0 · (A∧B)(V+Vᵀ, W+Wᵀ)`. -/
theorem iterated_integral_coeff (n : ℕ) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (m : Fin 3 →₀ ℕ) (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    ∫ ρ in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ • (frameCoefficient (seedForm n h) (entryFrame (ρ * Real.sin θ) (ρ * Real.cos θ)) V W).coeff m =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * h Complex.I *
        ((m.multinomial : ℂ) * xiPoly m 0) * linePair (V + V.transpose) (W + W.transpose) := by
  have h2I : (2 * Complex.I : ℂ) ^ (n + 3) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hcongr : ∀ ρ ∈ Set.Ioi (0 : ℝ),
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ • (frameCoefficient (seedForm n h) (entryFrame (ρ * Real.sin θ) (ρ * Real.cos θ)) V W).coeff m =
      ((m.multinomial : ℂ) * (Complex.I / 2) * ((2 * Complex.I) ^ (n + 3))⁻¹ *
          (2 * Real.pi * ((2 * Complex.I) ^ (n + 3) * h Complex.I *
            (xiPoly m 0 * (-2 * linePair (V + V.transpose) (W + W.transpose)))))) *
        ((ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ (n + 3) : ℝ) : ℂ) := by
    intro ρ hρ
    rw [angular_integral_coeff n h hh m hm V W ρ hρ, entryDiscFn_zero, wedgePoly_zero]
    unfold baseK
    push_cast
    rw [inv_pow]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
    integral_complex_ofReal, radial_integral]
  push_cast
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  field_simp

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
