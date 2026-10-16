module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CauchyRiemannSmoothing

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem contDiff_cutoff_of_contDiffOn
    {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {order : ℕ∞}
    (function : X → E) (domain : Set X) (domain_open : IsOpen domain)
    (regular : ContDiffOn ℝ order function domain) (center : X) (cutoff : ContDiffBump center)
    (supported : tsupport (cutoff : X → ℝ) ⊆ domain) :
    ContDiff ℝ order (fun point => cutoff point • function point) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  by_cases member : point ∈ domain
  · exact cutoff.contDiff.contDiffAt.smul (regular.contDiffAt (domain_open.mem_nhds member))
  · have outside : point ∉ tsupport (cutoff : X → ℝ) := fun support_mem => member (supported support_mem)
    apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (cutoff : X → ℝ)).isOpen_compl.mem_nhds outside] with argument argument_outside
    rw [image_eq_zero_of_notMem_tsupport argument_outside, zero_smul]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem contDiffAt_of_local_antiholomorphicDerivative (function : ℂ → E) (regular : ContDiff ℝ 1 function)
    (derivative : ℂ → E) (derivative_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) derivative)
    (point : ℂ) (radius : ℝ) (positive : 0 < radius)
    (equation : ∀ argument ∈ Metric.ball point radius, antiholomorphicDerivative function argument = derivative argument) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) function point := by
  let scale := radius / 4
  have scale_positive : 0 < scale := div_pos positive (by norm_num)
  let mass : ℝ := ∫ direction : ℂ, complexRadialBump scale direction
  have mass_nonzero : mass ≠ 0 := ne_of_gt (complexRadialBump_integral_pos scale scale_positive)
  have smooth := (contDiff_const (c := mass⁻¹)).smul
    ((radialAverage_contDiff scale scale_positive function regular.continuous).sub
      (radialMeanCorrection_contDiff scale scale_positive derivative derivative_regular))
  apply smooth.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds point scale_positive] with center center_mem
  have local_equation (argument : ℂ) (nearby : ‖argument - center‖ ≤ scale) :
      antiholomorphicDerivative function argument = derivative argument := by
    apply equation
    apply lt_of_le_of_lt (dist_triangle argument center point)
    have center_bound : dist center point < scale := center_mem
    have argument_bound : dist argument center ≤ scale := by simpa only [dist_eq_norm] using nearby
    dsimp [scale] at center_bound argument_bound
    linarith
  have formula := radial_cauchyRiemann_formula scale scale_positive function regular derivative center local_equation
  change function center = mass⁻¹ • ((∫ direction : ℂ, complexRadialBump scale direction • function (center + direction)) -
    radialMeanCorrection scale derivative center)
  rw [← formula]
  exact (inv_smul_smul₀ mass_nonzero (function center)).symm

theorem contDiffOn_of_contDiffOn_antiholomorphicDerivative (function : ℂ → E) (domain : Set ℂ)
    (domain_open : IsOpen domain) (regular : ContDiffOn ℝ 1 function domain)
    (derivative_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (antiholomorphicDerivative function) domain) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) function domain := by
  intro point member
  obtain ⟨radius, positive, ball_subset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (domain_open.mem_nhds member)
  let cutoff : ContDiffBump point := ⟨radius / 4, radius / 2, by positivity, by linarith⟩
  have support_subset : tsupport (cutoff : ℂ → ℝ) ⊆ domain := by
    intro argument argument_mem
    apply ball_subset
    have bound : dist argument point ≤ radius / 2 := by
      simpa only [cutoff.tsupport_eq, Metric.mem_closedBall] using argument_mem
    change dist argument point ≤ radius
    linarith
  let extension : ℂ → E := fun argument => cutoff argument • function argument
  let derivative_extension : ℂ → E := fun argument => cutoff argument • antiholomorphicDerivative function argument
  have extension_regular : ContDiff ℝ 1 extension :=
    contDiff_cutoff_of_contDiffOn function domain domain_open regular point cutoff support_subset
  have derivative_extension_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) derivative_extension :=
    contDiff_cutoff_of_contDiffOn (antiholomorphicDerivative function) domain domain_open derivative_regular point cutoff support_subset
  have extension_eq (argument : ℂ) (argument_mem : argument ∈ Metric.ball point cutoff.rIn) :
      extension =ᶠ[nhds argument] function := by
    filter_upwards [cutoff.eventuallyEq_one_of_mem_ball argument_mem] with nearby value
    change cutoff nearby = 1 at value
    change cutoff nearby • function nearby = function nearby
    rw [value, one_smul]
  have equation (argument : ℂ) (argument_mem : argument ∈ Metric.ball point cutoff.rIn) :
      antiholomorphicDerivative extension argument = derivative_extension argument := by
    have derivatives := (extension_eq argument argument_mem).fderiv_eq (𝕜 := ℝ)
    unfold antiholomorphicDerivative
    rw [derivatives]
    change _ = cutoff argument • _
    rw [cutoff.one_of_mem_closedBall (Metric.ball_subset_closedBall argument_mem), one_smul]
    rfl
  have smooth := contDiffAt_of_local_antiholomorphicDerivative extension extension_regular derivative_extension
    derivative_extension_regular point cutoff.rIn cutoff.rIn_pos equation
  apply ContDiffAt.contDiffWithinAt
  exact smooth.congr_of_eventuallyEq (extension_eq point (Metric.mem_ball_self cutoff.rIn_pos)).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
