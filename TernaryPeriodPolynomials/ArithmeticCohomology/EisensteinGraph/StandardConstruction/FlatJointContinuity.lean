module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatNormStrip
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatJointContinuity

theorem norm_derivative_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (center parameter : ℂ) (near : parameter ∈ Metric.ball center 1) :
    ‖deriv (fun z => extension z argument) parameter‖ ≤
      ‖extension ((center.re - 2 : ℝ) : ℂ) argument‖ +
        ‖extension ((center.re + 2 : ℝ) : ℂ) argument‖ := by
  have differentiable : Differentiable ℂ (fun z => extension z argument) :=
    fun z => (flat.2.1 argument z).differentiableAt
  have estimate := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (C := ‖extension ((center.re - 2 : ℝ) : ℂ) argument‖ +
      ‖extension ((center.re + 2 : ℝ) : ℂ) argument‖)
    (show (0 : ℝ) < 1 by norm_num) (differentiable.diffContOnCl (s := Metric.ball parameter 1))
  simp only [div_one] at estimate
  apply estimate
  intro value membership
  have distance : dist value center < 2 := by
    have triangle := dist_triangle value parameter center
    rw [Metric.mem_sphere.mp membership] at triangle
    have inside := Metric.mem_ball.mp near
    linarith
  rw [dist_eq_norm] at distance
  have realBound := (Complex.abs_re_le_norm (value - center)).trans_lt distance
  rw [Complex.sub_re, abs_lt] at realBound
  exact FlatNormStrip.flat_norm_strip_bound data extension flat argument _ _ value
    (by linarith) (by linarith)

theorem parameter_difference_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (center parameter : ℂ) (near : parameter ∈ Metric.ball center 1) :
    ‖extension parameter argument - extension center argument‖ ≤
      (‖extension ((center.re - 2 : ℝ) : ℂ) argument‖ +
        ‖extension ((center.re + 2 : ℝ) : ℂ) argument‖) * ‖parameter - center‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (flat.2.1 argument z).differentiableAt)
    (fun z membership => norm_derivative_bound data extension flat argument center z membership)
    (convex_ball center 1) (Metric.mem_ball_self (by norm_num)) near

theorem joint_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    Continuous (fun pair : ℂ × AdelicGL => extension pair.1 pair.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨center, argument⟩
  let bound : AdelicGL → ℝ := fun value =>
    ‖extension ((center.re - 2 : ℝ) : ℂ) value‖ + ‖extension ((center.re + 2 : ℝ) : ℂ) value‖
  have scalarContinuous : ∀ parameter, Continuous (extension parameter) :=
    fun parameter => InducedContinuity.induced_continuous data .plane parameter _ (flat.1 parameter)
  have boundContinuous : Continuous bound :=
    (scalarContinuous _).norm.add (scalarContinuous _).norm
  let upper : ℂ × AdelicGL → ℝ := fun pair =>
    bound pair.2 * ‖pair.1 - center‖ + ‖extension center pair.2 - extension center argument‖
  have upperContinuous : Continuous upper :=
    ((boundContinuous.comp continuous_snd).mul (continuous_fst.sub continuous_const).norm).add
      (((scalarContinuous center).comp continuous_snd).sub continuous_const).norm
  have upperLimit : Tendsto upper (𝓝 (center, argument)) (𝓝 0) := by
    simpa [upper] using upperContinuous.continuousAt.tendsto (x := (center, argument))
  have near : ∀ᶠ pair : ℂ × AdelicGL in 𝓝 (center, argument), pair.1 ∈ Metric.ball center 1 :=
    ((Metric.isOpen_ball).preimage continuous_fst).mem_nhds (Metric.mem_ball_self (by norm_num))
  have bounded : ∀ᶠ pair : ℂ × AdelicGL in 𝓝 (center, argument),
      ‖extension pair.1 pair.2 - extension center argument‖ ≤ upper pair := by
    filter_upwards [near] with pair membership
    exact (norm_sub_le_norm_sub_add_norm_sub
      (extension pair.1 pair.2) (extension center pair.2) (extension center argument)).trans
      (add_le_add (parameter_difference_bound data extension flat pair.2 center pair.1 membership) le_rfl)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun pair => norm_nonneg _)) bounded upperLimit)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatJointContinuity
