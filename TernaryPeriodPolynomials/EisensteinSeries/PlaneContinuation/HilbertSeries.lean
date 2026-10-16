module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HilbertSeries

theorem cuspVector_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (matrix : AdelicGL)
    (parameter reference : ℂ) :
    planeCuspVector (flatSection.1 parameter) matrix =
      Complex.exp ((parameter - reference) * (height matrix : ℂ)) •
        planeCuspVector (flatSection.1 reference) matrix := by
  have parameterFormula := planeCuspVector_planeParabolic (flatSection.1 parameter)
    (parabolicPart matrix) (compactPart matrix)
  have referenceFormula := planeCuspVector_planeParabolic (flatSection.1 reference)
    (parabolicPart matrix) (compactPart matrix)
  rw [← parabolicPart_mul_compactPart] at parameterFormula referenceFormula
  rw [parameterFormula, referenceFormula,
    flatSection_planeCuspVector_eq flatSection parameter _ (compactPart_mem matrix),
    flatSection_planeCuspVector_eq flatSection reference _ (compactPart_mem matrix)]
  simp only [smul_smul]
  congr 1
  have exponentIdentity :
      (-2 * inductionExponent .plane parameter) *
          (Real.log (adeleNorm (planeCornerUnit (parabolicPart matrix)) : ℝ) : ℂ) +
        binaryInductionExponent degree .plane parameter *
          (Real.log (adeleNorm
            (Matrix.GeneralLinearGroup.det (planeBinaryBlock (parabolicPart matrix))) : ℝ) : ℂ) =
      (parameter - reference) * (height matrix : ℂ) +
        ((-2 * inductionExponent .plane reference) *
          (Real.log (adeleNorm (planeCornerUnit (parabolicPart matrix)) : ℝ) : ℂ) +
        binaryInductionExponent degree .plane reference *
          (Real.log (adeleNorm
            (Matrix.GeneralLinearGroup.det (planeBinaryBlock (parabolicPart matrix))) : ℝ) : ℂ)) := by
    simp only [binaryInductionExponent, inductionExponent, height, planeHeightLog,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  simp only [mul_assoc] at exponentIdentity
  simp only [normPower, mul_assoc]
  rw [← Complex.exp_add, exponentIdentity]
  simp only [Complex.exp_add]
  ring

noncomputable def summand {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (parameter : ℂ)
    (basePoint : AdelicGL) (flag : Flags .plane) : data.cusp.H :=
  (planeCuspVector (flatSection.1 parameter) (rationalGroup flag.out⁻¹ * basePoint)).val

noncomputable def literalSum {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (parameter : ℂ)
    (basePoint : AdelicGL) : data.cusp.H :=
  ∑' flag, summand flatSection parameter basePoint flag

theorem summand_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (flag : Flags .plane) (parameter reference : ℂ) :
    summand flatSection parameter basePoint flag =
      Complex.exp ((parameter - reference) * (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)) •
        summand flatSection reference basePoint flag :=
  congrArg Subtype.val (cuspVector_change_parameter flatSection _ parameter reference)

theorem summand_analytic {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (flag : Flags .plane) (parameter : ℂ) :
    AnalyticAt ℂ (fun value => summand flatSection value basePoint flag) parameter := by
  have formula : (fun value => summand flatSection value basePoint flag) =
      fun value => Complex.exp ((value - cohomologicalPoint) *
        (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)) •
          summand flatSection cohomologicalPoint basePoint flag := by
    funext value
    exact summand_change_parameter flatSection basePoint flag value cohomologicalPoint
  rw [formula]
  exact (((analyticAt_id.sub analyticAt_const).mul analyticAt_const).cexp).smul analyticAt_const

theorem hasSum {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (summand flatSection parameter basePoint) (literalSum flatSection parameter basePoint) :=
  (TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.summable_flag_cuspVectors flatSection basePoint parameter rightHalfPlane).hasSum

theorem summand_bound_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (reference : ℂ) (upperBound : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ,
      reference.re ≤ parameter.re → parameter.re ≤ upperBound → ∀ flag : Flags .plane,
      ‖summand flatSection parameter basePoint flag‖ ≤
        bound * ‖summand flatSection reference basePoint flag‖ := by
  obtain ⟨heightBound, heightProperty⟩ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight.height_flag_boundedAbove basePoint
  refine ⟨Real.exp ((upperBound - reference.re) * max 0 heightBound), (Real.exp_pos _).le,
    fun parameter lowerParameter upperParameter flag => ?_⟩
  rw [summand_change_parameter flatSection basePoint flag parameter reference,
    norm_smul, Complex.norm_exp]
  have realExponent : ((parameter - reference) *
      (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)).re =
      (parameter.re - reference.re) * height (rationalGroup flag.out⁻¹ * basePoint) := by simp
  rw [realExponent]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left ((heightProperty flag).trans (le_max_right _ _))
    (sub_nonneg.mpr lowerParameter)).trans
    (mul_le_mul_of_nonneg_right (sub_le_sub_right upperParameter _) (le_max_left _ _))

theorem uniformly_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) (reference : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < reference.re) (upperBound : ℝ) :
    TendstoUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, summand flatSection parameter basePoint flag)
      (fun parameter => literalSum flatSection parameter basePoint)
      Filter.atTop {parameter : ℂ | reference.re ≤ parameter.re ∧ parameter.re ≤ upperBound} := by
  obtain ⟨bound, _, boundProperty⟩ := summand_bound_on_strip flatSection basePoint reference upperBound
  apply tendstoUniformlyOn_tsum
    ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.summable_norm_flag_cuspVectors flatSection basePoint reference
      rightHalfPlane).mul_left bound)
  intro flag parameter membership
  exact boundProperty parameter membership.1 membership.2 flag

theorem locallyUniformly {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) :
    TendstoLocallyUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, summand flatSection parameter basePoint flag)
      (fun parameter => literalSum flatSection parameter basePoint) Filter.atTop
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} := by
  rw [tendstoLocallyUniformlyOn_iff_filter]
  intro parameter parameterBound
  let reference : ℂ := (((-(degree : ℝ) / 2 + parameter.re) / 2 : ℝ) : ℂ)
  have referenceBound : -(degree : ℝ) / 2 < reference.re := by
    dsimp [reference]
    change -(degree : ℝ) / 2 < parameter.re at parameterBound
    linarith
  have parameterReference : reference.re < parameter.re := by
    dsimp [reference]
    change -(degree : ℝ) / 2 < parameter.re at parameterBound
    linarith
  let strip : Set ℂ := {value | reference.re < value.re ∧ value.re < parameter.re + 1}
  have openness : IsOpen strip :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have inclusion : strip ⊆
      {value : ℂ | reference.re ≤ value.re ∧ value.re ≤ parameter.re + 1} := by
    intro value membership
    exact ⟨membership.1.le, membership.2.le⟩
  have uniform := (uniformly_on_strip flatSection basePoint reference referenceBound
    (parameter.re + 1)).mono inclusion
  apply uniform.tendstoUniformlyOnFilter.mono_right
  apply Filter.le_principal_iff.mpr
  apply mem_nhdsWithin_of_mem_nhds
  exact openness.mem_nhds ⟨parameterReference, by linarith⟩

theorem analytic {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) :
    AnalyticOnNhd ℂ (fun parameter => literalSum flatSection parameter basePoint)
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} := by
  have openness : IsOpen {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ openness
  apply (locallyUniformly flatSection basePoint).differentiableOn _ openness
  apply Filter.Eventually.of_forall
  intro finiteSet
  apply DifferentiableOn.fun_sum
  intro flag _ value _
  exact (summand_analytic flatSection basePoint flag value).differentiableAt.differentiableWithinAt

theorem summand_hasDerivAt {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (flag : Flags .plane) (parameter : ℂ) :
    HasDerivAt (fun value => summand flatSection value basePoint flag)
      ((height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) •
        summand flatSection parameter basePoint flag) parameter := by
  have formula : (fun value => summand flatSection value basePoint flag) =
      fun value => Complex.exp ((value - parameter) *
        (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)) •
          summand flatSection parameter basePoint flag := by
    funext value
    exact summand_change_parameter flatSection basePoint flag value parameter
  rw [formula]
  simpa only [id_eq, sub_self, zero_mul, Complex.exp_zero, one_mul] using
    ((((hasDerivAt_id parameter).sub_const parameter).mul_const
      (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)).cexp.smul_const
        (summand flatSection parameter basePoint flag))

theorem locallyUniformly_deriv {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) :
    TendstoLocallyUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) •
          summand flatSection parameter basePoint flag)
      (deriv (fun parameter => literalSum flatSection parameter basePoint)) Filter.atTop
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} := by
  have derivativeFormula (finiteSet : Finset (Flags .plane)) :
      deriv (fun parameter => ∑ flag ∈ finiteSet, summand flatSection parameter basePoint flag) =
        fun parameter => ∑ flag ∈ finiteSet,
          (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) •
            summand flatSection parameter basePoint flag := by
    funext parameter
    exact (HasDerivAt.fun_sum (fun flag _ =>
      summand_hasDerivAt flatSection basePoint flag parameter)).deriv
  have uniform := (locallyUniformly flatSection basePoint).deriv
    (Filter.Eventually.of_forall (fun finiteSet => DifferentiableOn.fun_sum
      (fun flag _ value _ =>
        (summand_hasDerivAt flatSection basePoint flag value).differentiableAt.differentiableWithinAt)))
    (isOpen_lt continuous_const Complex.continuous_re)
  simpa only [Function.comp_def, derivativeFormula] using uniform

theorem hasSum_deriv {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (fun flag : Flags .plane =>
      (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) •
        summand flatSection parameter basePoint flag)
      (deriv (fun value => literalSum flatSection value basePoint) parameter) :=
  (locallyUniformly_deriv flatSection basePoint).tendsto_at rightHalfPlane

theorem moment_hasDerivAt {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (flag : Flags .plane) (order : ℕ) (parameter : ℂ) :
    HasDerivAt (fun value => (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order •
      summand flatSection value basePoint flag)
      ((height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ (order + 1) •
        summand flatSection parameter basePoint flag) parameter := by
  simpa only [Pi.smul_def, smul_smul, pow_succ] using
    (summand_hasDerivAt flatSection basePoint flag parameter).const_smul
      ((height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order)

theorem locallyUniformly_iteratedDeriv {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) (order : ℕ) :
    TendstoLocallyUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order •
          summand flatSection parameter basePoint flag)
      (iteratedDeriv order (fun parameter => literalSum flatSection parameter basePoint))
      Filter.atTop {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} := by
  induction order with
  | zero =>
      simpa only [pow_zero, one_smul, iteratedDeriv_zero] using locallyUniformly flatSection basePoint
  | succ order inductionHypothesis =>
      have derivativeFormula (finiteSet : Finset (Flags .plane)) :
          deriv (fun parameter => ∑ flag ∈ finiteSet,
            (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order •
              summand flatSection parameter basePoint flag) =
          fun parameter => ∑ flag ∈ finiteSet,
            (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ (order + 1) •
              summand flatSection parameter basePoint flag := by
        funext parameter
        exact (HasDerivAt.fun_sum (fun flag _ =>
          moment_hasDerivAt flatSection basePoint flag order parameter)).deriv
      have uniform := inductionHypothesis.deriv
        (Filter.Eventually.of_forall (fun finiteSet => DifferentiableOn.fun_sum
          (fun flag _ value _ =>
            (moment_hasDerivAt flatSection basePoint flag order value).differentiableAt.differentiableWithinAt)))
        (isOpen_lt continuous_const Complex.continuous_re)
      simpa only [Function.comp_def, derivativeFormula, iteratedDeriv_succ] using uniform

theorem hasSum_iteratedDeriv {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (order : ℕ) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (fun flag : Flags .plane =>
      (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order •
        summand flatSection parameter basePoint flag)
      (iteratedDeriv order (fun value => literalSum flatSection value basePoint) parameter) :=
  (locallyUniformly_iteratedDeriv flatSection basePoint order).tendsto_at rightHalfPlane

theorem iteratedDeriv_eq_tsum {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (order : ℕ) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    iteratedDeriv order (fun value => literalSum flatSection value basePoint) parameter =
      ∑' flag : Flags .plane, (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order •
        summand flatSection parameter basePoint flag :=
  (hasSum_iteratedDeriv flatSection basePoint order parameter rightHalfPlane).tsum_eq.symm

theorem abs_pow_mul_exp_le (order : ℕ) (gap bound value : ℝ)
    (positiveGap : 0 < gap) (valueBound : value ≤ bound) :
    |value| ^ order * Real.exp (gap * value) ≤
      ((order.factorial : ℝ) / gap ^ order) * Real.exp (2 * gap * max 0 bound) := by
  have factorialPositive : (0 : ℝ) < order.factorial := by positivity
  have gapPowerPositive : 0 < gap ^ order := pow_pos positiveGap _
  have coefficientNonnegative : 0 ≤ (order.factorial : ℝ) / gap ^ order := by positivity
  have powerBound : |value| ^ order ≤
      Real.exp (gap * |value|) * ((order.factorial : ℝ) / gap ^ order) := by
    calc
      |value| ^ order = ((gap * |value|) ^ order / (order.factorial : ℝ)) *
          ((order.factorial : ℝ) / gap ^ order) := by
        rw [mul_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.pow_div_factorial_le_exp _ (mul_nonneg positiveGap.le (abs_nonneg _)) order)
        coefficientNonnegative
  have doubledBound : |value| + value ≤ 2 * max 0 bound := by
    rcases le_total 0 value with nonnegative | nonpositive
    · rw [abs_of_nonneg nonnegative]
      linarith [valueBound.trans (le_max_right 0 bound)]
    · rw [abs_of_nonpos nonpositive]
      linarith [le_max_left (0 : ℝ) bound]
  calc
    |value| ^ order * Real.exp (gap * value) ≤
        (Real.exp (gap * |value|) * ((order.factorial : ℝ) / gap ^ order)) *
          Real.exp (gap * value) :=
      mul_le_mul_of_nonneg_right powerBound (Real.exp_pos _).le
    _ = ((order.factorial : ℝ) / gap ^ order) * Real.exp (gap * (|value| + value)) := by
      rw [mul_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left doubledBound positiveGap.le]))
      coefficientNonnegative

theorem summable_norm_moments {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (order : ℕ) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      ‖(height (rationalGroup flag.out⁻¹ * basePoint) : ℂ) ^ order •
        summand flatSection parameter basePoint flag‖) := by
  let reference : ℂ := (((-(degree : ℝ) / 2 + parameter.re) / 2 : ℝ) : ℂ)
  have referenceBound : -(degree : ℝ) / 2 < reference.re := by
    dsimp [reference]
    linarith
  have positiveGap : 0 < parameter.re - reference.re := by
    dsimp [reference]
    linarith
  obtain ⟨heightBound, heightProperty⟩ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight.height_flag_boundedAbove basePoint
  let bound : ℝ := ((order.factorial : ℝ) / (parameter.re - reference.re) ^ order) *
    Real.exp (2 * (parameter.re - reference.re) * max 0 heightBound)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.summable_norm_flag_cuspVectors flatSection basePoint reference
      referenceBound).mul_left bound)
  intro flag
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    summand_change_parameter flatSection basePoint flag parameter reference,
    norm_smul, Complex.norm_exp]
  have realExponent : ((parameter - reference) *
      (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)).re =
      (parameter.re - reference.re) * height (rationalGroup flag.out⁻¹ * basePoint) := by simp
  rw [realExponent, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (abs_pow_mul_exp_le order _ heightBound _ positiveGap (heightProperty flag)) (norm_nonneg _)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HilbertSeries
