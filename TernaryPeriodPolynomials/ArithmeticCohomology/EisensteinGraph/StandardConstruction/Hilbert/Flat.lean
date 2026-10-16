module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.StandardAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatNormStrip
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.VectorStripIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertFlat

def lift {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) : data.cusp.H :=
  (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter) argument).val

theorem decomposition_formula {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    lift data extension flat parameter (planeUnipotent first second * planeLevi binary unit * compact) =
      ((data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) *
        normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) •
          data.cusp.π binary (lift data extension flat cohomologicalPoint compact) := by
  unfold lift
  rw [mul_assoc, CuspLiftCovariance.vector_plane_radical, FlatUniqueness.planeLevi_split,
    mul_assoc, CuspLiftCovariance.vector_plane_rankOne]
  change (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) •
    (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
      (binaryLevi .plane binary * compact)).val = _
  rw [CuspLiftCovariance.vector_binary, CuspLift.flat_vector data extension flat parameter compact membership,
    smul_smul]

theorem analytic {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (point : ℂ) :
    AnalyticAt ℂ (fun parameter => lift data extension flat parameter argument) point := by
  obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  have formula : (fun parameter => lift data extension flat parameter argument) =
      (fun parameter =>
        ((data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) *
          normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) •
            data.cusp.π binary (lift data extension flat cohomologicalPoint compact)) := by
    funext parameter
    rw [decomposition, decomposition_formula data extension flat parameter first second binary unit compact membership]
  rw [formula]
  have rank : AnalyticAt ℂ (fun parameter => normPower unit (-2 * inductionExponent .plane parameter)) point := by
    unfold normPower inductionExponent
    exact ((analyticAt_const.mul (analyticAt_const.add analyticAt_id.div_const)).mul analyticAt_const).cexp
  have binaryPower : AnalyticAt ℂ (fun parameter => normPower (GeneralLinearGroup.det binary)
      (binaryInductionExponent degree .plane parameter)) point := by
    unfold normPower binaryInductionExponent inductionExponent
    exact ((analyticAt_const.add (analyticAt_const.add analyticAt_id.div_const)).mul analyticAt_const).cexp
  exact ((analyticAt_const.mul rank).mul binaryPower).smul analyticAt_const

theorem norm_exp_affine {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (argument : AdelicGL) :
    ∃ amplitude offset rate : ℝ, 0 ≤ amplitude ∧ ∀ parameter : ℂ,
      ‖lift data extension flat parameter argument‖ = Real.exp (offset + rate * parameter.re) * amplitude := by
  obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  refine ⟨‖lift data extension flat cohomologicalPoint compact‖,
    -Real.log (adeleNorm unit : ℝ) +
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) * ((degree : ℝ) + 4) / 2,
    (-2 * Real.log (adeleNorm unit : ℝ) +
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) / 3,
    norm_nonneg _, ?_⟩
  intro parameter
  rw [decomposition, decomposition_formula data extension flat parameter first second binary unit compact membership]
  simp only [norm_smul, norm_mul, data.chi.unitary, one_mul, NormPower.normPower_norm, data.cusp.unitary]
  have unitPositive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  have binaryPositive : (0 : ℝ) < (adeleNorm (GeneralLinearGroup.det binary) : ℝ) :=
    adeleNorm_pos (GeneralLinearGroup.det binary)
  rw [Real.rpow_def_of_pos unitPositive, Real.rpow_def_of_pos binaryPositive, ← Real.exp_add]
  congr 2
  simp [inductionExponent, binaryInductionExponent, Complex.mul_re]
  ring

theorem norm_strip_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (lower upper : ℝ) (parameter : ℂ)
    (lowerBound : lower ≤ parameter.re) (upperBound : parameter.re ≤ upper) :
    ‖lift data extension flat parameter argument‖ ≤
      ‖lift data extension flat (lower : ℂ) argument‖ + ‖lift data extension flat (upper : ℂ) argument‖ := by
  obtain ⟨amplitude, offset, rate, nonnegative, formula⟩ := norm_exp_affine data extension flat argument
  simp only [formula, Complex.ofReal_re]
  exact FlatNormStrip.exp_affine_strip_bound amplitude offset rate lower upper parameter.re
    nonnegative lowerBound upperBound

theorem standard_analytic_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    AnalyticAt ℂ (fun parameter =>
      HilbertStandard.value data parameter (extension parameter) (flat.1 parameter) argument) parameter := by
  let lower : ℝ := (-(degree : ℝ) / 2 + parameter.re) / 2
  let upper : ℝ := parameter.re + 1
  have lowerHalfPlane : -(degree : ℝ) / 2 < lower := by dsimp [lower]; linarith
  have upperHalfPlane : -(degree : ℝ) / 2 < upper := by dsimp [upper]; linarith
  have differentiable := VectorStripIntegral.integral_differentiableOn_strip radicalMeasure
    (fun parameter => HilbertStandard.integrand data parameter (extension parameter) (flat.1 parameter) argument)
    (fun parameter => (HilbertStandard.integrand_continuous data parameter
      (extension parameter) (flat.1 parameter) argument).aestronglyMeasurable)
    (fun coordinates parameter => (analytic data extension flat _ parameter).differentiableAt)
    lower upper
    (fun coordinates parameter lowerBound upperBound =>
      norm_strip_bound data extension flat _ lower upper parameter lowerBound upperBound)
    (HilbertStandard.integrand_integrable data (lower : ℂ) (extension (lower : ℂ))
      (flat.1 (lower : ℂ)) lowerHalfPlane argument)
    (HilbertStandard.integrand_integrable data (upper : ℂ) (extension (upper : ℂ))
      (flat.1 (upper : ℂ)) upperHalfPlane argument)
  apply differentiable.analyticAt
  apply ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
  constructor <;> dsimp [lower, upper] <;> linarith

theorem norm_derivative_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (center parameter : ℂ) (near : parameter ∈ Metric.ball center 1) :
    ‖deriv (fun z => lift data extension flat z argument) parameter‖ ≤
      ‖lift data extension flat ((center.re - 2 : ℝ) : ℂ) argument‖ +
        ‖lift data extension flat ((center.re + 2 : ℝ) : ℂ) argument‖ := by
  have differentiable : Differentiable ℂ (fun z => lift data extension flat z argument) :=
    fun z => (analytic data extension flat argument z).differentiableAt
  have estimate := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (C := ‖lift data extension flat ((center.re - 2 : ℝ) : ℂ) argument‖ +
      ‖lift data extension flat ((center.re + 2 : ℝ) : ℂ) argument‖)
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
  exact norm_strip_bound data extension flat argument _ _ value
    (by linarith) (by linarith)

theorem parameter_difference_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (center parameter : ℂ) (near : parameter ∈ Metric.ball center 1) :
    ‖lift data extension flat parameter argument - lift data extension flat center argument‖ ≤
      (‖lift data extension flat ((center.re - 2 : ℝ) : ℂ) argument‖ +
        ‖lift data extension flat ((center.re + 2 : ℝ) : ℂ) argument‖) * ‖parameter - center‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (analytic data extension flat argument z).differentiableAt)
    (fun z membership => norm_derivative_bound data extension flat argument center z membership)
    (convex_ball center 1) (Metric.mem_ball_self (by norm_num)) near

theorem joint_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    Continuous (fun pair : ℂ × AdelicGL => lift data extension flat pair.1 pair.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨center, argument⟩
  let bound : AdelicGL → ℝ := fun value =>
    ‖lift data extension flat ((center.re - 2 : ℝ) : ℂ) value‖ + ‖lift data extension flat ((center.re + 2 : ℝ) : ℂ) value‖
  have scalarContinuous : ∀ parameter, Continuous (lift data extension flat parameter) :=
    fun parameter => CuspLift.continuous data .plane parameter _ (flat.1 parameter)
  have boundContinuous : Continuous bound :=
    (scalarContinuous _).norm.add (scalarContinuous _).norm
  let upper : ℂ × AdelicGL → ℝ := fun pair =>
    bound pair.2 * ‖pair.1 - center‖ + ‖lift data extension flat center pair.2 - lift data extension flat center argument‖
  have upperContinuous : Continuous upper :=
    ((boundContinuous.comp continuous_snd).mul (continuous_fst.sub continuous_const).norm).add
      (((scalarContinuous center).comp continuous_snd).sub continuous_const).norm
  have upperLimit : Tendsto upper (𝓝 (center, argument)) (𝓝 0) := by
    simpa [upper] using upperContinuous.continuousAt.tendsto (x := (center, argument))
  have near : ∀ᶠ pair : ℂ × AdelicGL in 𝓝 (center, argument), pair.1 ∈ Metric.ball center 1 :=
    ((Metric.isOpen_ball).preimage continuous_fst).mem_nhds (Metric.mem_ball_self (by norm_num))
  have bounded : ∀ᶠ pair : ℂ × AdelicGL in 𝓝 (center, argument),
      ‖lift data extension flat pair.1 pair.2 - lift data extension flat center argument‖ ≤ upper pair := by
    filter_upwards [near] with pair membership
    exact (norm_sub_le_norm_sub_add_norm_sub
      (lift data extension flat pair.1 pair.2) (lift data extension flat center pair.2) (lift data extension flat center argument)).trans
      (add_le_add (parameter_difference_bound data extension flat pair.2 center pair.1 membership) le_rfl)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun pair => norm_nonneg _)) bounded upperLimit)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertFlat
