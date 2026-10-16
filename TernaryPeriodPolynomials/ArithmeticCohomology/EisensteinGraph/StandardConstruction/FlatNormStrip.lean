module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedHeight
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatNormStrip

theorem norm_exp_affine {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) :
    ∃ amplitude offset rate : ℝ, 0 ≤ amplitude ∧ ∀ parameter : ℂ,
      ‖extension parameter argument‖ = Real.exp (offset + rate * parameter.re) * amplitude := by
  obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  refine ⟨‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖,
    -Real.log (adeleNorm unit : ℝ) +
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) * ((degree : ℝ) + 4) / 2,
    (-2 * Real.log (adeleNorm unit : ℝ) +
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) / 3,
    norm_nonneg _, ?_⟩
  intro parameter
  rw [decomposition, CuspLiftCovariance.flat_scalar_formula data extension flat parameter
    first second binary unit compact membership]
  simp only [norm_mul, data.chi.unitary, one_mul, NormPower.normPower_norm]
  have unitPositive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  have binaryPositive : (0 : ℝ) < (adeleNorm (GeneralLinearGroup.det binary) : ℝ) :=
    adeleNorm_pos (GeneralLinearGroup.det binary)
  rw [Real.rpow_def_of_pos unitPositive, Real.rpow_def_of_pos binaryPositive, ← Real.exp_add]
  congr 2
  simp [inductionExponent, binaryInductionExponent, Complex.mul_re]
  ring

theorem exp_affine_strip_bound (amplitude offset rate lower upper value : ℝ)
    (nonnegative : 0 ≤ amplitude) (lowerBound : lower ≤ value) (upperBound : value ≤ upper) :
    Real.exp (offset + rate * value) * amplitude ≤
      Real.exp (offset + rate * lower) * amplitude +
        Real.exp (offset + rate * upper) * amplitude := by
  by_cases positive : 0 ≤ rate
  · have bounded : Real.exp (offset + rate * value) * amplitude ≤
        Real.exp (offset + rate * upper) * amplitude := by
      gcongr
    exact bounded.trans (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le nonnegative))
  · have bounded : Real.exp (offset + rate * value) * amplitude ≤
        Real.exp (offset + rate * lower) * amplitude := by
      apply mul_le_mul_of_nonneg_right _ nonnegative
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonpos_left lowerBound (le_of_not_ge positive)]
    exact bounded.trans (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le nonnegative))

theorem flat_norm_strip_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (lower upper : ℝ) (parameter : ℂ)
    (lowerBound : lower ≤ parameter.re) (upperBound : parameter.re ≤ upper) :
    ‖extension parameter argument‖ ≤ ‖extension (lower : ℂ) argument‖ +
      ‖extension (upper : ℂ) argument‖ := by
  obtain ⟨amplitude, offset, rate, nonnegative, formula⟩ := norm_exp_affine data extension flat argument
  simp only [formula, Complex.ofReal_re]
  exact exp_affine_strip_bound amplitude offset rate lower upper parameter.re
    nonnegative lowerBound upperBound

theorem summand_strip_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (flag : Flags .plane) (lower upper : ℝ) (parameter : ℂ)
    (lowerBound : lower ≤ parameter.re) (upperBound : parameter.re ≤ upper) :
    ‖eisensteinSummand extension parameter argument flag‖ ≤
      ‖eisensteinSummand extension (lower : ℂ) argument flag‖ +
        ‖eisensteinSummand extension (upper : ℂ) argument flag‖ :=
  flat_norm_strip_bound data extension flat _ lower upper parameter lowerBound upperBound

theorem eisenstein_differentiableOn_strip {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (lower upper : ℝ)
    (lowerSummable : Summable (eisensteinSummand extension (lower : ℂ) argument))
    (upperSummable : Summable (eisensteinSummand extension (upper : ℂ) argument)) :
    DifferentiableOn ℂ (fun parameter => ∑' flag : Flags .plane,
      eisensteinSummand extension parameter argument flag)
        {parameter : ℂ | lower < parameter.re ∧ parameter.re < upper} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (lowerSummable.norm.add upperSummable.norm)
  · intro flag parameter _
    exact (flat.2.1 _ parameter).differentiableAt.differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro flag parameter membership
    exact summand_strip_bound data extension flat argument flag lower upper parameter
      membership.1.le membership.2.le

theorem eisenstein_summable_strip {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (lower upper : ℝ)
    (lowerSummable : Summable (eisensteinSummand extension (lower : ℂ) argument))
    (upperSummable : Summable (eisensteinSummand extension (upper : ℂ) argument))
    (parameter : ℂ) (lowerBound : lower ≤ parameter.re) (upperBound : parameter.re ≤ upper) :
    Summable (eisensteinSummand extension parameter argument) :=
  (lowerSummable.norm.add upperSummable.norm).of_norm_bounded
    (fun flag => summand_strip_bound data extension flat argument flag lower upper parameter
      lowerBound upperBound)

theorem eisenstein_uniform_strip {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (lower upper : ℝ)
    (lowerSummable : Summable (eisensteinSummand extension (lower : ℂ) argument))
    (upperSummable : Summable (eisensteinSummand extension (upper : ℂ) argument)) :
    TendstoUniformlyOn
      (fun finite : Finset (Flags .plane) => fun parameter : ℂ =>
        ∑ flag ∈ finite, eisensteinSummand extension parameter argument flag)
      (fun parameter => ∑' flag : Flags .plane, eisensteinSummand extension parameter argument flag)
      atTop {parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} :=
  tendstoUniformlyOn_tsum (lowerSummable.norm.add upperSummable.norm)
    (fun flag parameter membership => summand_strip_bound data extension flat argument flag
      lower upper parameter membership.1 membership.2)

theorem continuation_analytic_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (threshold : ℝ)
    (sums : ∀ parameter : ℂ, threshold < parameter.re → ∀ argument,
      HasSum (eisensteinSummand extension parameter argument) (continuation parameter argument)) :
    ∀ argument parameter, threshold < parameter.re →
      AnalyticAt ℂ (fun parameter => continuation parameter argument) parameter := by
  intro argument parameter membership
  let lower : ℝ := (threshold + parameter.re) / 2
  let upper : ℝ := parameter.re + 1
  have lowerThreshold : threshold < lower := by dsimp [lower]; linarith
  have upperThreshold : threshold < upper := by dsimp [upper]; linarith
  have stripOpen : IsOpen {z : ℂ | lower < z.re ∧ z.re < upper} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have stripNeighborhood : {z : ℂ | lower < z.re ∧ z.re < upper} ∈ 𝓝 parameter :=
    stripOpen.mem_nhds (by constructor <;> dsimp [lower, upper] <;> linarith)
  have analytic := (eisenstein_differentiableOn_strip data extension flat argument lower upper
    (sums (lower : ℂ) lowerThreshold argument).summable
    (sums (upper : ℂ) upperThreshold argument).summable).analyticAt stripNeighborhood
  apply analytic.congr
  filter_upwards [stripNeighborhood] with value valueMembership
  exact (sums value (lowerThreshold.trans valueMembership.1) argument).tsum_eq

theorem continuation_analytic_some_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension continuation) :
    ∃ threshold : ℝ, ∀ argument parameter, threshold < parameter.re →
      AnalyticAt ℂ (fun parameter => continuation parameter argument) parameter := by
  obtain ⟨threshold, sums⟩ := continues.2
  exact ⟨threshold, continuation_analytic_halfPlane data extension continuation flat threshold sums⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatNormStrip
