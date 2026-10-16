module

public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.KernelMass
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.HalfPlaneContinuation

@[expose] public section


/-!
# Holomorphy of kernel integrals beyond the cohomological point

For a function `f` on `ℝ²` with `(1 + |u|²)^δ ‖f u‖` integrable (`δ > 0`), the kernel integral
`s ↦ ∫ (1 + |u|²)^(-3/4 - s/2) f u du` is complex differentiable on the half-plane
`Re s > -3/2 - 2δ`, which contains the cohomological point `s = -3/2`. Together with the
identity theorem `meromorphic_eq_at_in_halfPlane`, this identifies the standard continuation at
`s = -3/2` with the literal integral whenever the integrand decays at that rate.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open MeasureTheory Set Filter Topology Real GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection

noncomputable section

namespace TernaryPeriodPolynomials.ArchimedeanConstant

/-- The base `1 + |u|²` of the kernel. -/
def kernelBase (u : ℝ × ℝ) : ℝ := 1 + u.1 ^ 2 + u.2 ^ 2

theorem kernelBase_one_le (u : ℝ × ℝ) : 1 ≤ kernelBase u := by
  unfold kernelBase; nlinarith [sq_nonneg u.1, sq_nonneg u.2]

theorem kernelBase_pos (u : ℝ × ℝ) : 0 < kernelBase u := by
  linarith [kernelBase_one_le u]

theorem norm_kernel (s : ℂ) (u : ℝ × ℝ) :
    ‖Helpers.standardGoodLineRealKernel s u‖ = kernelBase u ^ (-(3 : ℝ) / 4 - s.re / 2) := by
  rw [Helpers.standardGoodLineRealKernel, Complex.norm_exp, Real.rpow_def_of_pos (kernelBase_pos u)]
  unfold kernelBase
  congr 1
  simp [Complex.mul_re]
  ring

theorem kernel_hasDerivAt (s : ℂ) (u : ℝ × ℝ) :
    HasDerivAt (fun z => Helpers.standardGoodLineRealKernel z u)
      ((-(1 : ℂ) / 2 * (Real.log (kernelBase u) : ℂ)) * Helpers.standardGoodLineRealKernel s u) s := by
  unfold Helpers.standardGoodLineRealKernel
  have hlin : HasDerivAt (fun z : ℂ => (-(3 : ℂ) / 4 - z / 2) * (Real.log (1 + u.1 ^ 2 + u.2 ^ 2) : ℂ))
      (-(1 : ℂ) / 2 * (Real.log (1 + u.1 ^ 2 + u.2 ^ 2) : ℂ)) s := by
    have h := ((hasDerivAt_id s).div_const 2).const_sub (-(3 : ℂ) / 4)
    have h2 := h.mul_const ((Real.log (1 + u.1 ^ 2 + u.2 ^ 2) : ℂ))
    refine h2.congr_deriv ?_
    ring
  refine hlin.cexp.congr_deriv ?_
  unfold kernelBase
  ring

theorem kernel_continuous (s : ℂ) : Continuous (fun u => Helpers.standardGoodLineRealKernel s u) := by
  unfold Helpers.standardGoodLineRealKernel
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact Continuous.log (by fun_prop) (fun u => (kernelBase_pos u).ne')

theorem norm_kernel_le (s : ℂ) (e : ℝ) (he : -(3 : ℝ) / 4 - s.re / 2 ≤ e) (u : ℝ × ℝ) :
    ‖Helpers.standardGoodLineRealKernel s u‖ ≤ kernelBase u ^ e := by
  rw [norm_kernel]
  exact Real.rpow_le_rpow_of_exponent_le (kernelBase_one_le u) he

/-- Kernel integrals of functions with `(1+|u|²)^δ`-integrable norm are holomorphic on
`Re s > -3/2 - 2δ`. -/
theorem kernelIntegral_hasDerivAt (f : ℝ × ℝ → ℂ) (δ : ℝ)
    (hf_meas : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)))
    (hf : Integrable (fun u => kernelBase u ^ δ * ‖f u‖) (volume : Measure (ℝ × ℝ)))
    (s₀ : ℂ) (hs₀ : -(3 : ℝ) / 2 - 2 * δ < s₀.re) :
    HasDerivAt (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * f u)
      (∫ u, (-(1 : ℂ) / 2 * (Real.log (kernelBase u) : ℂ)) *
        Helpers.standardGoodLineRealKernel s₀ u * f u) s₀ := by
  set η : ℝ := (s₀.re + 3 / 2 + 2 * δ) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hmeasK : ∀ s, AEStronglyMeasurable (fun u => Helpers.standardGoodLineRealKernel s u * f u)
      (volume : Measure (ℝ × ℝ)) := fun s => (kernel_continuous s).aestronglyMeasurable.mul hf_meas
  have hint : Integrable (fun u => Helpers.standardGoodLineRealKernel s₀ u * f u) := by
    refine hf.mono' (hmeasK s₀) (Eventually.of_forall fun u => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_kernel_le s₀ δ (by linarith) u) (norm_nonneg _)
  have hbound : Integrable (fun u => (1 / η) * (kernelBase u ^ δ * ‖f u‖)) := hf.const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun s u => Helpers.standardGoodLineRealKernel s u * f u)
    (F' := fun s u => (-(1 : ℂ) / 2 * (Real.log (kernelBase u) : ℂ)) *
      Helpers.standardGoodLineRealKernel s u * f u)
    (x₀ := s₀) (s := Metric.ball s₀ η) (bound := fun u => (1 / η) * (kernelBase u ^ δ * ‖f u‖))
    (Metric.ball_mem_nhds s₀ hηpos)
    (Eventually.of_forall hmeasK) hint
    (((continuous_const.mul (Complex.continuous_ofReal.comp
      (Continuous.log (by unfold kernelBase; fun_prop) (fun u => (kernelBase_pos u).ne')))).mul
        (kernel_continuous s₀)).aestronglyMeasurable.mul hf_meas)
    (Eventually.of_forall fun u s hs => ?_) hbound
    (Eventually.of_forall fun u s _ => (kernel_hasDerivAt s u).mul_const (f u))
  · exact key.2
  · -- the dominating bound on the ball
    have hre : s₀.re - η < s.re := by
      have := Metric.mem_ball.mp hs
      have h2 : |s.re - s₀.re| < η := by
        calc |s.re - s₀.re| = |(s - s₀).re| := by simp
          _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
          _ < η := by rwa [← dist_eq_norm]
      linarith [(abs_lt.mp h2).1]
    have hB := kernelBase_one_le u
    have hlog : Real.log (kernelBase u) ≤ kernelBase u ^ (η / 2) / (η / 2) :=
      Real.log_le_rpow_div (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log (kernelBase u) := Real.log_nonneg hB
    have hK := norm_kernel_le s (δ - η / 2) (by rw [hη] at hre ⊢; linarith) u
    rw [norm_mul, norm_mul, norm_mul]
    have hc : ‖(-(1 : ℂ) / 2)‖ = 1 / 2 := by norm_num
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have hsplit : kernelBase u ^ δ = kernelBase u ^ (η / 2) * kernelBase u ^ (δ - η / 2) := by
      rw [← Real.rpow_add (kernelBase_pos u)]; ring_nf
    have hpow0 : 0 ≤ kernelBase u ^ (η / 2) := Real.rpow_nonneg (kernelBase_pos u).le _
    calc 1 / 2 * Real.log (kernelBase u) * ‖Helpers.standardGoodLineRealKernel s u‖ * ‖f u‖
        ≤ 1 / 2 * (kernelBase u ^ (η / 2) / (η / 2)) * kernelBase u ^ (δ - η / 2) * ‖f u‖ := by
          gcongr
      _ = 1 / η * (kernelBase u ^ δ * ‖f u‖) := by
          rw [hsplit]; field_simp

theorem kernelIntegral_differentiableOn (f : ℝ × ℝ → ℂ) (δ : ℝ)
    (hf_meas : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)))
    (hf : Integrable (fun u => kernelBase u ^ δ * ‖f u‖) (volume : Measure (ℝ × ℝ))) :
    DifferentiableOn ℂ (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * f u)
      {s : ℂ | -(3 : ℝ) / 2 - 2 * δ < s.re} := fun s hs =>
  (kernelIntegral_hasDerivAt f δ hf_meas hf s hs).differentiableAt.differentiableWithinAt

theorem isOpen_halfPlane (b : ℝ) : IsOpen {s : ℂ | b < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem kernelIntegral_analyticAt (f : ℝ × ℝ → ℂ) (δ : ℝ)
    (hf_meas : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)))
    (hf : Integrable (fun u => kernelBase u ^ δ * ‖f u‖) (volume : Measure (ℝ × ℝ)))
    (s₀ : ℂ) (hs₀ : -(3 : ℝ) / 2 - 2 * δ < s₀.re) :
    AnalyticAt ℂ (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * f u) s₀ :=
  (kernelIntegral_differentiableOn f δ hf_meas hf).analyticAt
    ((isOpen_halfPlane _).mem_nhds hs₀)

/-- **Literal value of the continuation at the cohomological point.** If a meromorphic family
agrees with the kernel integral for `Re s ≫ 0`, is analytic at `s = -3/2`, and the integrand
decays like `(1+|u|²)^(-δ)` with `δ > 0`, then its value at `s = -3/2` is the plain integral. -/
theorem continuation_eq_integral (f : ℝ × ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hf_meas : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)))
    (hf : Integrable (fun u => kernelBase u ^ δ * ‖f u‖) (volume : Measure (ℝ × ℝ)))
    (J : ℂ → ℂ) (hJ : MeromorphicOn J {s : ℂ | -(3 : ℝ) / 2 - 2 * δ < s.re})
    (R : ℝ) (agree : ∀ s : ℂ, R < s.re → J s = ∫ u, Helpers.standardGoodLineRealKernel s u * f u)
    (analytic : AnalyticAt ℂ J cohomologicalPoint) :
    J cohomologicalPoint = ∫ u, f u := by
  have hpt : -(3 : ℝ) / 2 - 2 * δ < cohomologicalPoint.re := by
    norm_num [cohomologicalPoint]; linarith
  have hG := kernelIntegral_differentiableOn f δ hf_meas hf
  have hGm : MeromorphicOn (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * f u)
      {s : ℂ | -(3 : ℝ) / 2 - 2 * δ < s.re} := fun s hs =>
    (hG.analyticAt ((isOpen_halfPlane _).mem_nhds hs)).meromorphicAt
  have key := Helpers.meromorphic_eq_at_in_halfPlane (-(3 : ℝ) / 2 - 2 * δ) hJ hGm R
    (fun s hs _ => agree s hs) cohomologicalPoint hpt analytic
    (kernelIntegral_analyticAt f δ hf_meas hf _ hpt)
  rw [key]
  congr 1
  funext u
  rw [Helpers.standardGoodLineRealKernel_endpoint, one_mul]

/-- Kernel integrals of holomorphic families, locally dominated by `(1+|u|²)^δ`-integrable bounds,
are holomorphic on `Re s > -3/2 - 2δ`. -/
theorem kernelFamilyIntegral_hasDerivAt (G G' : ℂ → ℝ × ℝ → ℂ) (δ : ℝ)
    (meas : ∀ s, AEStronglyMeasurable (G s) (volume : Measure (ℝ × ℝ)))
    (meas' : ∀ s, AEStronglyMeasurable (G' s) (volume : Measure (ℝ × ℝ)))
    (deriv : ∀ s u, -(3 : ℝ) / 2 - 2 * δ < s.re → HasDerivAt (fun z => G z u) (G' s u) s)
    (s₀ : ℂ) (hs₀ : -(3 : ℝ) / 2 - 2 * δ < s₀.re)
    (ε : ℝ) (hε : 0 < ε) (b : ℝ × ℝ → ℝ)
    (hb : Integrable (fun u => kernelBase u ^ δ * b u) (volume : Measure (ℝ × ℝ)))
    (bound : ∀ u, ∀ s ∈ Metric.ball s₀ ε, ‖G s u‖ ≤ b u ∧ ‖G' s u‖ ≤ b u) :
    HasDerivAt (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * G s u)
      (∫ u, ((-(1 : ℂ) / 2 * (Real.log (kernelBase u) : ℂ)) *
        Helpers.standardGoodLineRealKernel s₀ u * G s₀ u +
          Helpers.standardGoodLineRealKernel s₀ u * G' s₀ u)) s₀ := by
  set η : ℝ := min ε ((s₀.re + 3 / 2 + 2 * δ) / 2) with hη
  have hηpos : 0 < η := lt_min hε (by linarith)
  have hηle : η ≤ (s₀.re + 3 / 2 + 2 * δ) / 2 := min_le_right _ _
  have hball : ∀ s ∈ Metric.ball s₀ η, s₀.re - η < s.re ∧ s ∈ Metric.ball s₀ ε := by
    intro s hs
    have hd := Metric.mem_ball.mp hs
    refine ⟨?_, Metric.mem_ball.mpr (lt_of_lt_of_le hd (min_le_left _ _))⟩
    have h2 : |s.re - s₀.re| < η := by
      calc |s.re - s₀.re| = |(s - s₀).re| := by simp
        _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        _ < η := by rwa [← dist_eq_norm]
    linarith [(abs_lt.mp h2).1]
  have hmeasK : ∀ s, AEStronglyMeasurable (fun u => Helpers.standardGoodLineRealKernel s u * G s u)
      (volume : Measure (ℝ × ℝ)) := fun s => (kernel_continuous s).aestronglyMeasurable.mul (meas s)
  have hb0 : ∀ u, 0 ≤ b u := fun u =>
    le_trans (norm_nonneg _) (bound u s₀ (Metric.mem_ball_self hε)).1
  have hint : Integrable (fun u => Helpers.standardGoodLineRealKernel s₀ u * G s₀ u) := by
    refine hb.mono' (hmeasK s₀) (Eventually.of_forall fun u => ?_)
    rw [norm_mul]
    exact mul_le_mul (norm_kernel_le s₀ δ (by linarith) u)
      (bound u s₀ (Metric.mem_ball_self hε)).1 (norm_nonneg _)
      (Real.rpow_nonneg (kernelBase_pos u).le _)
  have hlogc : Continuous (fun u : ℝ × ℝ => ((Real.log (kernelBase u) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Continuous.log (by unfold kernelBase; fun_prop) (fun u => (kernelBase_pos u).ne'))
  have hbound : Integrable (fun u => (1 / η + 1) * (kernelBase u ^ δ * b u)) := hb.const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun s u => Helpers.standardGoodLineRealKernel s u * G s u)
    (F' := fun s u => (-(1 : ℂ) / 2 * (Real.log (kernelBase u) : ℂ)) *
      Helpers.standardGoodLineRealKernel s u * G s u +
        Helpers.standardGoodLineRealKernel s u * G' s u)
    (x₀ := s₀) (s := Metric.ball s₀ η) (bound := fun u => (1 / η + 1) * (kernelBase u ^ δ * b u))
    (Metric.ball_mem_nhds s₀ hηpos)
    (Eventually.of_forall hmeasK) hint
    ((((continuous_const.mul hlogc).mul (kernel_continuous s₀)).aestronglyMeasurable.mul
      (meas s₀)).add ((kernel_continuous s₀).aestronglyMeasurable.mul (meas' s₀)))
    (Eventually.of_forall fun u s hs => ?_) hbound
    (Eventually.of_forall fun u s hs => ?_)
  · exact key.2
  · obtain ⟨hre, hsε⟩ := hball s hs
    obtain ⟨hG, hG'⟩ := bound u s hsε
    have hB := kernelBase_one_le u
    have hlog : Real.log (kernelBase u) ≤ kernelBase u ^ (η / 2) / (η / 2) :=
      Real.log_le_rpow_div (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log (kernelBase u) := Real.log_nonneg hB
    have hK := norm_kernel_le s (δ - η / 2) (by linarith) u
    have hK' : ‖Helpers.standardGoodLineRealKernel s u‖ ≤ kernelBase u ^ δ :=
      norm_kernel_le s δ (by linarith) u
    have hpowδ0 : 0 ≤ kernelBase u ^ δ := Real.rpow_nonneg (kernelBase_pos u).le _
    have hsplit : kernelBase u ^ δ = kernelBase u ^ (η / 2) * kernelBase u ^ (δ - η / 2) := by
      rw [← Real.rpow_add (kernelBase_pos u)]; ring_nf
    have hpow0 : 0 ≤ kernelBase u ^ (η / 2) := Real.rpow_nonneg (kernelBase_pos u).le _
    have hc : ‖(-(1 : ℂ) / 2)‖ = 1 / 2 := by norm_num
    have first : ‖(-(1 : ℂ) / 2 * (Real.log (kernelBase u) : ℂ)) *
        Helpers.standardGoodLineRealKernel s u * G s u‖ ≤ 1 / η * (kernelBase u ^ δ * b u) := by
      rw [norm_mul, norm_mul, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
      calc 1 / 2 * Real.log (kernelBase u) * ‖Helpers.standardGoodLineRealKernel s u‖ * ‖G s u‖
          ≤ 1 / 2 * (kernelBase u ^ (η / 2) / (η / 2)) * kernelBase u ^ (δ - η / 2) * b u := by
            gcongr
        _ = 1 / η * (kernelBase u ^ δ * b u) := by
            rw [hsplit]; field_simp
    have second : ‖Helpers.standardGoodLineRealKernel s u * G' s u‖ ≤ kernelBase u ^ δ * b u := by
      rw [norm_mul]; exact mul_le_mul hK' hG' (norm_nonneg _) hpowδ0
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 1 / η * (kernelBase u ^ δ * b u) + kernelBase u ^ δ * b u := add_le_add first second
      _ = (1 / η + 1) * (kernelBase u ^ δ * b u) := by ring
  · obtain ⟨hre, _⟩ := hball s hs
    have hd := deriv s u (by linarith)
    exact ((kernel_hasDerivAt s u).mul hd).congr_deriv (by ring)

/-- **Literal value of the continuation for holomorphic families.** -/
theorem continuation_eq_integral_family (G G' : ℂ → ℝ × ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (meas : ∀ s, AEStronglyMeasurable (G s) (volume : Measure (ℝ × ℝ)))
    (meas' : ∀ s, AEStronglyMeasurable (G' s) (volume : Measure (ℝ × ℝ)))
    (deriv : ∀ s u, -(3 : ℝ) / 2 - 2 * δ < s.re → HasDerivAt (fun z => G z u) (G' s u) s)
    (dominated : ∀ s₀ : ℂ, -(3 : ℝ) / 2 - 2 * δ < s₀.re → ∃ ε > 0, ∃ b : ℝ × ℝ → ℝ,
      Integrable (fun u => kernelBase u ^ δ * b u) (volume : Measure (ℝ × ℝ)) ∧
      ∀ u, ∀ s ∈ Metric.ball s₀ ε, ‖G s u‖ ≤ b u ∧ ‖G' s u‖ ≤ b u)
    (J : ℂ → ℂ) (hJ : MeromorphicOn J {s : ℂ | -(3 : ℝ) / 2 - 2 * δ < s.re})
    (R : ℝ) (agree : ∀ s : ℂ, R < s.re →
      J s = ∫ u, Helpers.standardGoodLineRealKernel s u * G s u)
    (analytic : AnalyticAt ℂ J cohomologicalPoint) :
    J cohomologicalPoint = ∫ u, G cohomologicalPoint u := by
  have hpt : -(3 : ℝ) / 2 - 2 * δ < cohomologicalPoint.re := by
    norm_num [cohomologicalPoint]; linarith
  have hG : DifferentiableOn ℂ (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * G s u)
      {s : ℂ | -(3 : ℝ) / 2 - 2 * δ < s.re} := by
    intro s hs
    obtain ⟨ε, hε, b, hb, hbd⟩ := dominated s hs
    exact (kernelFamilyIntegral_hasDerivAt G G' δ meas meas' deriv s hs ε hε b hb
      hbd).differentiableAt.differentiableWithinAt
  have hAn : ∀ s : ℂ, -(3 : ℝ) / 2 - 2 * δ < s.re →
      AnalyticAt ℂ (fun s => ∫ u, Helpers.standardGoodLineRealKernel s u * G s u) s :=
    fun s hs => hG.analyticAt ((isOpen_halfPlane _).mem_nhds hs)
  have key := Helpers.meromorphic_eq_at_in_halfPlane (-(3 : ℝ) / 2 - 2 * δ) hJ
    (fun s hs => (hAn s hs).meromorphicAt) R
    (fun s hs _ => agree s hs) cohomologicalPoint hpt analytic (hAn _ hpt)
  rw [key]
  congr 1
  funext u
  rw [Helpers.standardGoodLineRealKernel_endpoint, one_mul]

end TernaryPeriodPolynomials.ArchimedeanConstant
