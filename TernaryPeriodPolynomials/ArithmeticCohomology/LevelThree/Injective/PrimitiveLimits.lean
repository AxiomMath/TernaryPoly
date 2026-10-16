module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Primitive
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


/-!
# Limits and boundary values of Eichler integrals

Let `g` be holomorphic on the upper half-plane and `Q` a primitive of `g(z) (X₀ - z X₁)^m dz`
(`IsPrimitive`). Every coordinate `ℓ_j = (binaryStandardBasis m).coord j` of `Q` is a primitive of
`g(z) · C(m, j) (-z)^(m-j)`, so along the imaginary axis `t ↦ ℓ_j (Q (i t))` has derivative
`i · C(m, j) (-i t)^(m-j) g(i t)`.

* If `g` decays exponentially at `i∞` (`ExpDecay`), the moments `t^p g(i t)` are integrable on
  `(1, ∞)` (`integrableOn_Ioi_one`), `Q` has a limit at `i∞`, the same along every vertical line
  (`exists_tendsto_shift`), and for `Q(i) = 0` the coordinates of the limit are
  `C(m, j) (-i)^(m-j) i ∫_1^∞ t^(m-j) g(i t) dt` (`coord_eq_integral_Ioi`).
* If `g(i t)` is bounded for `0 < t ≤ 1` (`integrableOn_Ioc_zero_one`) and `Q(i t)` has a limit at
  `t → 0⁺`, the coordinates of the limit are `-C(m, j) (-i)^(m-j) i ∫_0^1 t^(m-j) g(i t) dt`
  (`coord_eq_integral_Ioc`).

The space `Sym^m` carries no topology in this development, so limits in `V m` are stated
coordinatewise.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Filter Topology MeasureTheory
open scoped Manifold
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.LevelThreeInjective.PrimitiveLimits

/-- Uniform exponential decay at `i∞`. -/
def ExpDecay (g : ℍ → ℂ) : Prop :=
  ∃ C κ A : ℝ, 0 < κ ∧ ∀ z : ℂ, A ≤ z.im → ‖g (ofComplex z)‖ ≤ C * Real.exp (-κ * z.im)

theorem ExpDecay.normalize {g : ℍ → ℂ} (hd : ExpDecay g) :
    ∃ C κ A : ℝ, 0 < C ∧ 0 < κ ∧ 1 ≤ A ∧
      ∀ z : ℂ, A ≤ z.im → ‖g (ofComplex z)‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨C, κ, A, hκ, h⟩ := hd
  refine ⟨max C 1, κ, max A 1, lt_max_of_lt_right one_pos, hκ, le_max_right _ _,
    fun z hz => ?_⟩
  exact (h z ((le_max_left _ _).trans hz)).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-! ### Elementary estimates -/

theorem pow_exp_le {κ : ℝ} (hκ : 0 < κ) (p : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ p * Real.exp (-κ * t) ≤
      (p.factorial : ℝ) * (2 / κ) ^ p * Real.exp (-(κ / 2) * t) := by
  have hfac : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  have h := (div_le_iff₀ hfac).mp
    (Real.pow_div_factorial_le_exp (x := κ * t / 2) (by positivity) p)
  have hκ0 : κ ≠ 0 := hκ.ne'
  have e0 : 2 / κ * (κ * t / 2) = t := by
    field_simp
  have e1 : t ^ p = (2 / κ) ^ p * (κ * t / 2) ^ p := by
    rw [← mul_pow, e0]
  have e2 : Real.exp (κ * t / 2) * Real.exp (-κ * t) = Real.exp (-(κ / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc t ^ p * Real.exp (-κ * t)
      = (2 / κ) ^ p * (κ * t / 2) ^ p * Real.exp (-κ * t) := by rw [← e1]
    _ ≤ (2 / κ) ^ p * (Real.exp (κ * t / 2) * p.factorial) * Real.exp (-κ * t) := by gcongr
    _ = (p.factorial : ℝ) * (2 / κ) ^ p * (Real.exp (κ * t / 2) * Real.exp (-κ * t)) := by ring
    _ = (p.factorial : ℝ) * (2 / κ) ^ p * Real.exp (-(κ / 2) * t) := by rw [e2]

/-! ### Calculus along vertical and horizontal lines -/

section Calculus

variable {F d : ℂ → ℂ}

theorem hasDerivAt_imag (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (d z) z) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => F (Complex.I * (s : ℂ))) (d (Complex.I * (t : ℂ)) * Complex.I) t := by
  have hpos : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  have inner : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I (t : ℂ) :=
    ((hasDerivAt_id' (t : ℂ)).const_mul Complex.I).congr_deriv (mul_one _)
  exact ((hd _ hpos).comp (t : ℂ) inner).comp_ofReal

theorem hasDerivAt_horizontal (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (d z) z) (t : ℝ)
    (ht : 0 < t) (s : ℝ) :
    HasDerivAt (fun u : ℝ => F (Complex.I * (t : ℂ) + (u : ℂ)))
      (d (Complex.I * (t : ℂ) + (s : ℂ))) s := by
  have hpos : 0 < (Complex.I * (t : ℂ) + (s : ℂ)).im := by simpa using ht
  exact ((hd _ hpos).comp_const_add (Complex.I * (t : ℂ)) (s : ℂ)).comp_ofReal

theorem tendsto_imag_of_integrableOn (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (d z) z)
    (hint : IntegrableOn (fun t : ℝ => d (Complex.I * (t : ℂ)) * Complex.I) (Set.Ioi 1)) :
    Tendsto (fun T : ℝ => F (Complex.I * (T : ℂ))) atTop
      (𝓝 (F Complex.I + ∫ t : ℝ in Set.Ioi 1, d (Complex.I * (t : ℂ)) * Complex.I)) := by
  have hlim := (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id).const_add (F Complex.I)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hint' : IntervalIntegrable (fun t : ℝ => d (Complex.I * (t : ℂ)) * Complex.I) volume 1 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hint.mono_set (fun t ht => ht.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => F (Complex.I * (s : ℂ)))
    (f' := fun t : ℝ => d (Complex.I * (t : ℂ)) * Complex.I) (a := 1) (b := T)
    (fun x hx => hasDerivAt_imag hd x (by
      rw [Set.uIcc_of_le hT] at hx
      linarith [hx.1])) hint'
  simp only [Complex.ofReal_one, mul_one] at hftc
  show F Complex.I + ∫ t : ℝ in (1 : ℝ)..T, d (Complex.I * (t : ℂ)) * Complex.I =
    F (Complex.I * (T : ℂ))
  rw [hftc]
  ring

theorem shift_bound (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (d z) z) {K κ A : ℝ} {n : ℕ}
    (hK : 0 ≤ K)
    (hdb : ∀ z : ℂ, A ≤ z.im → ‖d z‖ ≤ K * ‖z‖ ^ n * Real.exp (-κ * z.im)) (c t : ℝ)
    (ht1 : 1 ≤ t) (htA : A ≤ t) :
    ‖F (Complex.I * (t : ℂ) + (c : ℂ)) - F (Complex.I * (t : ℂ))‖ ≤
      K * |c| * (1 + |c|) ^ n * (t ^ n * Real.exp (-κ * t)) := by
  have ht0 : 0 < t := by linarith
  have hnorm : ‖Complex.I * (t : ℂ)‖ = t := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hbound : ∀ u ∈ Set.uIcc (0 : ℝ) c,
      ‖d (Complex.I * (t : ℂ) + (u : ℂ))‖ ≤ K * (t + |c|) ^ n * Real.exp (-κ * t) := by
    intro u hu
    have hu' : |u| ≤ |c| := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1]
        exact h2.trans (le_abs_self c)
      · rw [abs_of_nonpos h2]
        exact (neg_le_neg h1).trans (neg_le_abs c)
    have him : (Complex.I * (t : ℂ) + (u : ℂ)).im = t := by simp
    have hz : ‖Complex.I * (t : ℂ) + (u : ℂ)‖ ≤ t + |c| := by
      calc ‖Complex.I * (t : ℂ) + (u : ℂ)‖ ≤ ‖Complex.I * (t : ℂ)‖ + ‖(u : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ t + |c| := by
          rw [hnorm, Complex.norm_real, Real.norm_eq_abs]
          linarith
    have h1 := hdb (Complex.I * (t : ℂ) + (u : ℂ)) (by rw [him]; exact htA)
    rw [him] at h1
    refine h1.trans ?_
    gcongr
  have mv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => F (Complex.I * (t : ℂ) + (u : ℂ)))
    (f' := fun u : ℝ => d (Complex.I * (t : ℂ) + (u : ℂ)))
    (s := Set.uIcc (0 : ℝ) c) (C := K * (t + |c|) ^ n * Real.exp (-κ * t))
    (fun u _ => (hasDerivAt_horizontal hd t ht0 u).hasDerivWithinAt) hbound
    (convex_uIcc 0 c) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Complex.ofReal_zero, add_zero, sub_zero, Real.norm_eq_abs] at mv
  have hle : t + |c| ≤ (1 + |c|) * t := by nlinarith [abs_nonneg c]
  calc ‖F (Complex.I * (t : ℂ) + (c : ℂ)) - F (Complex.I * (t : ℂ))‖
      ≤ K * (t + |c|) ^ n * Real.exp (-κ * t) * |c| := mv
    _ ≤ K * ((1 + |c|) * t) ^ n * Real.exp (-κ * t) * |c| := by gcongr
    _ = K * |c| * (1 + |c|) ^ n * (t ^ n * Real.exp (-κ * t)) := by
      rw [mul_pow]
      ring

theorem tendsto_shift_sub (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (d z) z) {K κ A : ℝ} {n : ℕ}
    (hK : 0 ≤ K) (hκ : 0 < κ)
    (hdb : ∀ z : ℂ, A ≤ z.im → ‖d z‖ ≤ K * ‖z‖ ^ n * Real.exp (-κ * z.im)) (c : ℝ) :
    Tendsto (fun t : ℝ => F (Complex.I * (t : ℂ) + (c : ℂ)) - F (Complex.I * (t : ℂ)))
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t ^ n * Real.exp (-κ * t)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) κ hκ).congr
      (fun t => by rw [Real.rpow_natCast])
  have h1 := h0.const_mul (K * |c| * (1 + |c|) ^ n)
  rw [mul_zero] at h1
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [eventually_ge_atTop (max A 1)] with t ht
  exact shift_bound hd hK hdb c t ((le_max_right _ _).trans ht) ((le_max_left _ _).trans ht)

end Calculus

/-! ### The scalar problem -/

section Scalar

variable {g : ℍ → ℂ} {F : ℂ → ℂ} {b : ℂ} {n : ℕ}

/-- The derivative `g(z) · b · (-z)^n` of a coordinate of the Eichler integral. -/
def weight (b : ℂ) (n : ℕ) (g : ℍ → ℂ) (z : ℂ) : ℂ := g (ofComplex z) * (b * (-z) ^ n)

theorem weight_line (t : ℝ) :
    weight b n g (Complex.I * (t : ℂ)) * Complex.I =
      (b * (-Complex.I) ^ n * Complex.I) * ((t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ)))) := by
  have e : (-(Complex.I * (t : ℂ))) ^ n = (-Complex.I) ^ n * (t : ℂ) ^ n := by
    rw [← neg_mul, mul_pow]
  rw [weight, e]
  ring

theorem norm_weight_le {C κ A : ℝ}
    (hbd : ∀ z : ℂ, A ≤ z.im → ‖g (ofComplex z)‖ ≤ C * Real.exp (-κ * z.im)) (z : ℂ)
    (hz : A ≤ z.im) :
    ‖weight b n g z‖ ≤ C * ‖b‖ * ‖z‖ ^ n * Real.exp (-κ * z.im) := by
  rw [weight, norm_mul, norm_mul, norm_pow, norm_neg]
  calc ‖g (ofComplex z)‖ * (‖b‖ * ‖z‖ ^ n)
      ≤ (C * Real.exp (-κ * z.im)) * (‖b‖ * ‖z‖ ^ n) :=
        mul_le_mul_of_nonneg_right (hbd z hz) (by positivity)
    _ = C * ‖b‖ * ‖z‖ ^ n * Real.exp (-κ * z.im) := by ring

theorem continuousOn_line (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    ContinuousOn (fun t : ℝ => g (ofComplex (Complex.I * (t : ℂ)))) (Set.Ioi 0) := by
  have hcont : ContinuousOn (g ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hg).continuousOn
  have path : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) := by fun_prop
  exact hcont.comp path.continuousOn (fun t ht => by simpa using ht)

theorem continuousOn_integrand (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (p : ℕ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioi 0) :=
  (Complex.continuous_ofReal.pow p).continuousOn.mul (continuousOn_line hg)

theorem integrableOn_Ioi_one (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hd : ExpDecay g) (p : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioi 1) := by
  obtain ⟨C, κ, A, hC, hκ, hA, hbd⟩ := hd.normalize
  have hcont := continuousOn_integrand hg p
  have hhead : IntegrableOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioc 1 A) := by
    have h : IntegrableOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
        (Set.Icc 1 A) :=
      (hcont.mono (fun t ht => lt_of_lt_of_le one_pos ht.1)).integrableOn_Icc
    exact h.mono_set Set.Ioc_subset_Icc_self
  have htail : IntegrableOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioi A) := by
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(κ / 2) * t)) (Set.Ioi A) :=
      integrableOn_exp_mul_Ioi (by linarith) A
    refine Integrable.mono' (μ := volume.restrict (Set.Ioi A))
      (g := fun t : ℝ => C * ((p.factorial : ℝ) * (2 / κ) ^ p) * Real.exp (-(κ / 2) * t))
      (Integrable.const_mul hexp _) ?_ ?_
    · exact (hcont.mono (fun t ht => lt_of_lt_of_le zero_lt_one (hA.trans (le_of_lt ht)))).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have htA : A < t := ht
      have ht0 : 0 ≤ t := by linarith
      show ‖(t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ)))‖ ≤
        C * ((p.factorial : ℝ) * (2 / κ) ^ p) * Real.exp (-(κ / 2) * t)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have him : (Complex.I * (t : ℂ)).im = t := by simp
      have hg' := hbd (Complex.I * (t : ℂ)) (by rw [him]; exact htA.le)
      rw [him] at hg'
      have hpe := pow_exp_le hκ p ht0
      calc t ^ p * ‖g (ofComplex (Complex.I * (t : ℂ)))‖
          ≤ t ^ p * (C * Real.exp (-κ * t)) := mul_le_mul_of_nonneg_left hg' (by positivity)
        _ = C * (t ^ p * Real.exp (-κ * t)) := by ring
        _ ≤ C * ((p.factorial : ℝ) * (2 / κ) ^ p * Real.exp (-(κ / 2) * t)) :=
          mul_le_mul_of_nonneg_left hpe hC.le
        _ = C * ((p.factorial : ℝ) * (2 / κ) ^ p) * Real.exp (-(κ / 2) * t) := by ring
  refine (hhead.union htail).mono_set (fun t ht => ?_)
  by_cases h : t ≤ A
  · exact Or.inl ⟨ht, h⟩
  · exact Or.inr (not_le.mp h)

theorem integrableOn_Ioc_zero_one (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hb : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖g (ofComplex (Complex.I * (t : ℂ)))‖ ≤ C)
    (p : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioc 0 1) := by
  obtain ⟨C, hC⟩ := hb
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioc (0 : ℝ) 1) :=
    (continuousOn_integrand hg p).mono Set.Ioc_subset_Ioi_self
  have hconst : IntegrableOn (fun _ : ℝ => |C|) (Set.Icc 0 1) :=
    continuousOn_const.integrableOn_Icc
  refine Integrable.mono' (μ := volume.restrict (Set.Ioc 0 1)) (g := fun _ : ℝ => |C|)
    (hconst.mono_set Set.Ioc_subset_Icc_self) (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
  show ‖(t : ℂ) ^ p * g (ofComplex (Complex.I * (t : ℂ)))‖ ≤ |C|
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
  calc t ^ p * ‖g (ofComplex (Complex.I * (t : ℂ)))‖ ≤ 1 * |C| :=
        mul_le_mul (pow_le_one₀ ht.1.le ht.2) ((hC t ht.1 ht.2).trans (le_abs_self C))
          (norm_nonneg _) zero_le_one
    _ = |C| := one_mul _

theorem integrableOn_weight_Ioi (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hd : ExpDecay g) :
    IntegrableOn (fun t : ℝ => weight b n g (Complex.I * (t : ℂ)) * Complex.I) (Set.Ioi 1) := by
  have e : (fun t : ℝ => weight b n g (Complex.I * (t : ℂ)) * Complex.I) =
      fun t : ℝ => (b * (-Complex.I) ^ n * Complex.I) *
        ((t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ)))) := funext weight_line
  rw [e]
  exact Integrable.const_mul (integrableOn_Ioi_one hg hd n) _

theorem limit_exists (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hd : ExpDecay g)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (weight b n g z) z) :
    ∃ L : ℂ, ∀ c : ℝ,
      Tendsto (fun t : ℝ => F (Complex.I * (t : ℂ) + (c : ℂ))) atTop (𝓝 L) := by
  obtain ⟨C, κ, A, hC, hκ, -, hbd⟩ := hd.normalize
  have h0 := tendsto_imag_of_integrableOn hF (integrableOn_weight_Ioi (b := b) (n := n) hg hd)
  refine ⟨F Complex.I + ∫ t : ℝ in Set.Ioi 1, weight b n g (Complex.I * (t : ℂ)) * Complex.I,
    fun c => ?_⟩
  have hsh := tendsto_shift_sub hF (K := C * ‖b‖) (κ := κ) (A := A) (n := n) (by positivity) hκ
    (fun z hz => norm_weight_le hbd z hz) c
  have h2 := hsh.add h0
  rw [zero_add] at h2
  exact h2.congr (fun t => sub_add_cancel _ _)

theorem limit_eq_integral_Ioi (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hd : ExpDecay g)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (weight b n g z) z) (hI : F Complex.I = 0) {L : ℂ}
    (hL : Tendsto (fun t : ℝ => F (Complex.I * (t : ℂ))) atTop (𝓝 L)) :
    L = b * (-Complex.I) ^ n * Complex.I *
      ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ))) := by
  have h0 := tendsto_imag_of_integrableOn hF (integrableOn_weight_Ioi (b := b) (n := n) hg hd)
  have hL' := tendsto_nhds_unique hL h0
  have e : ∫ t : ℝ in Set.Ioi 1, weight b n g (Complex.I * (t : ℂ)) * Complex.I =
      ∫ t : ℝ in Set.Ioi 1, (b * (-Complex.I) ^ n * Complex.I) *
        ((t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ)))) := by
    congr 1
    funext t
    exact weight_line t
  rw [hL', hI, zero_add, e, integral_const_mul]

/-- The boundary value function on `[0, 1]`: `B` at `0`, and `F (i t)` otherwise. -/
def capped (B : ℂ) (F : ℂ → ℂ) (t : ℝ) : ℂ := if t = 0 then B else F (Complex.I * (t : ℂ))

theorem capped_zero (B : ℂ) (F : ℂ → ℂ) : capped B F 0 = B := by simp [capped]

theorem capped_of_ne (B : ℂ) (F : ℂ → ℂ) {t : ℝ} (ht : t ≠ 0) :
    capped B F t = F (Complex.I * (t : ℂ)) := by simp [capped, ht]

theorem limit_eq_integral_Ioc (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hb : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖g (ofComplex (Complex.I * (t : ℂ)))‖ ≤ C)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (weight b n g z) z) (hI : F Complex.I = 0) {B : ℂ}
    (hB : Tendsto (fun t : ℝ => F (Complex.I * (t : ℂ))) (𝓝[>] 0) (𝓝 B)) :
    B = -(b * (-Complex.I) ^ n * Complex.I *
      ∫ t : ℝ in Set.Ioc 0 1, (t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ)))) := by
  have e : (fun t : ℝ => weight b n g (Complex.I * (t : ℂ)) * Complex.I) =
      fun t : ℝ => (b * (-Complex.I) ^ n * Complex.I) *
        ((t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ)))) := funext weight_line
  have hint : IntervalIntegrable (fun t : ℝ => weight b n g (Complex.I * (t : ℂ)) * Complex.I)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0 : ℝ) ≤ 1), e]
    exact Integrable.const_mul (integrableOn_Ioc_zero_one hg hb n) _
  have hpt : ∀ x : ℝ, 0 < x →
      HasDerivAt (capped B F) (weight b n g (Complex.I * (x : ℂ)) * Complex.I) x := by
    intro x hx0
    refine (hasDerivAt_imag hF x hx0).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hx0] with s hs
    exact capped_of_ne B F hs.ne'
  have hcont : ContinuousOn (capped B F) (Set.Icc 0 1) := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | hx0
    · have h1 : ContinuousWithinAt (capped B F) (Set.Ioi 0) 0 := by
        show Tendsto (capped B F) (𝓝[>] 0) (𝓝 (capped B F 0))
        rw [capped_zero]
        refine hB.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (capped_of_ne B F (Set.mem_Ioi.mp hs).ne').symm
      exact (continuousWithinAt_Ioi_iff_Ici.mp h1).mono Set.Icc_subset_Ici_self
    · exact (hpt x hx0).continuousAt.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (zero_le_one : (0 : ℝ) ≤ 1)
    hcont (fun x hx => hpt x hx.1) hint
  rw [capped_zero, capped_of_ne B F one_ne_zero, Complex.ofReal_one, mul_one, hI,
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hftc
  have e2 : ∫ t : ℝ in Set.Ioc 0 1, weight b n g (Complex.I * (t : ℂ)) * Complex.I =
      (b * (-Complex.I) ^ n * Complex.I) *
        ∫ t : ℝ in Set.Ioc 0 1, (t : ℂ) ^ n * g (ofComplex (Complex.I * (t : ℂ))) := by
    rw [← integral_const_mul]
    congr 1
  rw [e2] at hftc
  linear_combination hftc

end Scalar

/-! ### Coordinates of the Eichler integral -/

section Coordinates

variable (m : ℕ)

theorem coord_pointForm (g : ℍ → ℂ) (j : Fin (m + 1)) (z : ℂ) :
    (binaryStandardBasis m).coord j (pointForm m g z) =
      weight ((m.choose j.val : ℕ) : ℂ) (m - j.val) g z := by
  rw [pointForm, map_smul, smul_eq_mul, binaryPointPower_standardCoord, weight]

theorem hasDerivAt_coord {g : ℍ → ℂ} {Q : ℂ → V m} (hQ : IsPrimitive m g Q) (j : Fin (m + 1)) :
    ∀ z : ℂ, 0 < z.im →
      HasDerivAt (fun w => (binaryStandardBasis m).coord j (Q w))
        (weight ((m.choose j.val : ℕ) : ℂ) (m - j.val) g z) z := by
  intro z hz
  have h := hQ ((binaryStandardBasis m).coord j) z hz
  rwa [coord_pointForm] at h

/-- The primitive has a limit at `i∞`, the same along every vertical line (coordinatewise). -/
theorem exists_tendsto_shift {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hd : ExpDecay g)
    {Q : ℂ → V m} (hQ : IsPrimitive m g Q) :
    ∃ a : V m, ∀ (c : ℝ) (j : Fin (m + 1)),
      Tendsto (fun t : ℝ => (binaryStandardBasis m).coord j (Q (Complex.I * (t : ℂ) + (c : ℂ))))
        atTop (𝓝 ((binaryStandardBasis m).coord j a)) := by
  choose L hL using fun j : Fin (m + 1) =>
    limit_exists (F := fun w => (binaryStandardBasis m).coord j (Q w)) hg hd
      (hasDerivAt_coord m hQ j)
  refine ⟨∑ i, L i • binaryStandardBasis m i, fun c j => ?_⟩
  have hcoord : (binaryStandardBasis m).coord j (∑ i, L i • binaryStandardBasis m i) = L j := by
    rw [Module.Basis.coord_apply]
    exact congrFun (Module.Basis.repr_sum_self _ _) j
  rw [hcoord]
  exact hL j c

theorem coord_eq_integral_Ioi {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hd : ExpDecay g)
    {Q : ℂ → V m} (hQ : IsPrimitive m g Q) (hI : Q Complex.I = 0) {a : V m}
    (j : Fin (m + 1))
    (ha : Tendsto (fun t : ℝ => (binaryStandardBasis m).coord j (Q (Complex.I * (t : ℂ))))
      atTop (𝓝 ((binaryStandardBasis m).coord j a))) :
    (binaryStandardBasis m).coord j a =
      ((m.choose j.val : ℕ) : ℂ) * (-Complex.I) ^ (m - j.val) * Complex.I *
        ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (m - j.val) * g (ofComplex (Complex.I * (t : ℂ))) :=
  limit_eq_integral_Ioi (F := fun w => (binaryStandardBasis m).coord j (Q w)) hg hd
    (hasDerivAt_coord m hQ j) (by simp only [hI, map_zero]) ha

theorem coord_eq_integral_Ioc {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hb : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖g (ofComplex (Complex.I * (t : ℂ)))‖ ≤ C)
    {Q : ℂ → V m} (hQ : IsPrimitive m g Q) (hI : Q Complex.I = 0) {b : V m}
    (j : Fin (m + 1))
    (hb0 : Tendsto (fun t : ℝ => (binaryStandardBasis m).coord j (Q (Complex.I * (t : ℂ))))
      (𝓝[>] 0) (𝓝 ((binaryStandardBasis m).coord j b))) :
    (binaryStandardBasis m).coord j b =
      -(((m.choose j.val : ℕ) : ℂ) * (-Complex.I) ^ (m - j.val) * Complex.I *
        ∫ t : ℝ in Set.Ioc 0 1, (t : ℂ) ^ (m - j.val) * g (ofComplex (Complex.I * (t : ℂ)))) :=
  limit_eq_integral_Ioc (F := fun w => (binaryStandardBasis m).coord j (Q w)) hg hb
    (hasDerivAt_coord m hQ j) (by simp only [hI, map_zero]) hb0

end Coordinates

end TernaryPeriodPolynomials.LevelThreeInjective.PrimitiveLimits
