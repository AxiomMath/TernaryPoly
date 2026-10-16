module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Value
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.NormPower

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardRankOne

theorem radicalMeasure_scale (unit : Adelesˣ) :
    (adeleNorm unit * adeleNorm unit) •
        Measure.map (fun coordinates : Adeles × Adeles =>
          (unit.val * coordinates.1, unit.val * coordinates.2)) radicalMeasure =
      radicalMeasure := by
  have scaled := addEquivAddHaarChar_smul_map adeleMeasure
    (ContinuousAddEquiv.mulLeft unit)
  change adeleNorm unit • Measure.map (fun value => unit.val * value) adeleMeasure =
    adeleMeasure at scaled
  have product := congrArg (fun measure : Measure Adeles => measure.prod measure) scaled
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at product
  have mapped := Measure.map_prod_map (f := fun value => unit.val * value)
    (g := fun value => unit.val * value) adeleMeasure adeleMeasure
    (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  rw [mapped] at product
  exact product

theorem radicalIntegral_scale (unit : Adelesˣ) (function : Adeles × Adeles → ℂ) :
    ((adeleNorm unit : ℝ) * (adeleNorm unit : ℝ)) •
        (∫ coordinates, function (unit.val * coordinates.1, unit.val * coordinates.2)
          ∂radicalMeasure) =
      ∫ coordinates, function coordinates ∂radicalMeasure := by
  let equivalence := (ContinuousAddEquiv.mulLeft unit).toHomeomorph.toMeasurableEquiv
  have scaled := congrArg (fun measure : Measure (Adeles × Adeles) =>
    ∫ coordinates, function coordinates ∂measure) (radicalMeasure_scale unit)
  rw [integral_smul_nnreal_measure] at scaled
  have mapped := integral_map_equiv (μ := radicalMeasure)
    (equivalence.prodCongr equivalence) function
  change (∫ coordinates, function coordinates ∂Measure.map
      (fun coordinates : Adeles × Adeles =>
        (unit.val * coordinates.1, unit.val * coordinates.2)) radicalMeasure) =
    ∫ coordinates, function (unit.val * coordinates.1, unit.val * coordinates.2)
      ∂radicalMeasure at mapped
  rw [mapped] at scaled
  exact scaled

theorem lineUnipotent_rankOne (unit : Adelesˣ) (first second : Adeles) :
    lineUnipotent first second * lineLevi unit 1 =
      lineLevi unit 1 * lineUnipotent (unit.inv * first) (unit.inv * second) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [upperUnipotent, lineLevi_val,
      Matrix.mul_apply, Fin.sum_univ_three, ← mul_assoc]

theorem integrand_rankOne {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (unit : Adelesˣ) (argument : AdelicGL)
    (coordinates : Adeles × Adeles) :
    standardIntegrand extension parameter (lineLevi unit 1 * argument) coordinates =
      (data.chi.toMonoidHom unit *
        normPower unit (-2 * inductionExponent .plane parameter)) *
        standardIntegrand extension parameter argument
          (unit.inv * coordinates.1, unit.inv * coordinates.2) := by
  unfold standardIntegrand
  rw [mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _),
    lineUnipotent_rankOne]
  simp only [mul_assoc]
  rw [← mul_assoc (weyl⁻¹ : AdelicGL) (lineLevi unit 1)
    (lineUnipotent (unit.inv * coordinates.1) (unit.inv * coordinates.2) * argument),
    weyl_inverse_lineLevi]
  simp only [mul_assoc]
  simpa only [mul_assoc] using (flat.1 parameter).2.2.2.2.1 unit
    (weyl⁻¹ * (lineUnipotent (unit.inv * coordinates.1)
      (unit.inv * coordinates.2) * argument))

theorem integral_rankOne {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (unit : Adelesˣ) (argument : AdelicGL) :
    (∫ coordinates, standardIntegrand extension parameter
        (lineLevi unit 1 * argument) coordinates ∂radicalMeasure) =
      (data.chi.toMonoidHom unit *
          normPower unit (-2 * inductionExponent .plane parameter)) *
        (((adeleNorm unit : ℝ) * (adeleNorm unit : ℝ)) •
          (∫ coordinates, standardIntegrand extension parameter argument coordinates
            ∂radicalMeasure)) := by
  simp_rw [integrand_rankOne data extension flat]
  rw [integral_const_mul]
  congr 1
  have scaled := radicalIntegral_scale unit
    (fun coordinates => standardIntegrand extension parameter argument
      (unit.inv * coordinates.1, unit.inv * coordinates.2))
  simpa only [← mul_assoc, unit.inv_val, one_mul] using scaled.symm

theorem integral_rankOne_normalized {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (unit : Adelesˣ) (argument : AdelicGL) :
    (∫ coordinates, standardIntegrand extension parameter
        (lineLevi unit 1 * argument) coordinates ∂radicalMeasure) =
      (data.chi.toMonoidHom unit *
          normPower unit (2 * inductionExponent .line parameter)) *
        (∫ coordinates, standardIntegrand extension parameter argument coordinates
          ∂radicalMeasure) := by
  rw [integral_rankOne data extension flat, NormPower.rankOne_factor]
  simp only [Complex.real_smul, Complex.ofReal_mul, pow_two, mul_assoc]

theorem continuation_rankOne {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation) (point : ℂ)
    (regular : ∀ argument,
      AnalyticAt ℂ (fun parameter => continuation parameter argument) point)
    (unit : Adelesˣ) (argument : AdelicGL) :
    continuation point (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit *
        normPower unit (2 * inductionExponent .line point)) *
        continuation point argument := by
  obtain ⟨threshold, integrals⟩ := continues.2
  have factorAnalytic : ∀ parameter, AnalyticAt ℂ (fun parameter =>
      data.chi.toMonoidHom unit *
        normPower unit (2 * inductionExponent .line parameter)) parameter := by
    intro parameter
    exact analyticAt_const.mul (NormPower.lineRankOne_analytic unit parameter)
  apply ContinuationUniqueness.meromorphic_halfPlane_unique _ _
    (continues.1 (lineLevi unit 1 * argument))
    (fun parameter => (factorAnalytic parameter).meromorphicAt.mul
      (continues.1 argument parameter)) threshold _ point (regular _)
    ((factorAnalytic point).mul (regular argument))
  intro parameter membership
  change continuation parameter (lineLevi unit 1 * argument) =
    (data.chi.toMonoidHom unit * normPower unit (2 * inductionExponent .line parameter)) *
      continuation parameter argument
  rw [(integrals parameter membership _).2, (integrals parameter membership argument).2]
  exact integral_rankOne_normalized data extension flat parameter unit argument

theorem standardValue_rankOne {degree : ℕ} (data : InducingData degree)
    (extension : StandardValue.regularFamilies data) (unit : Adelesˣ)
    (argument : AdelicGL) :
    StandardValue.standardValue data extension (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit * normPower unit 2) *
        StandardValue.standardValue data extension argument := by
  have specification := StandardValue.chosenContinuation_spec data extension
  have transformation := continuation_rankOne data extension.val.val
    (StandardValue.chosenContinuation data extension) extension.val.property
    specification.1 cohomologicalPoint specification.2 unit argument
  have exponent : 2 * inductionExponent .line cohomologicalPoint = (2 : ℂ) := by
    norm_num [inductionExponent, cohomologicalPoint]
  rw [exponent] at transformation
  exact transformation

theorem polynomialContinuation_rankOne {degree : ℕ} (data : InducingData degree)
    (extension continuation :
      ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (flat : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial))
    (continues : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (continuation parameter vertices argument).val.coeff monomial))
    (point : ℂ) (regular : ∀ vertices argument monomial,
      AnalyticAt ℂ (fun parameter => (continuation parameter vertices argument).val.coeff monomial) point)
    (vertices : Fin 3 → RealGL3) (unit : Adelesˣ) (argument : AdelicGL) :
    continuation point vertices (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit *
        normPower unit (2 * inductionExponent .line point)) •
        continuation point vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
    continuation_rankOne data _ _ (flat vertices monomial)
      (continues vertices monomial) point
      (fun argument => regular vertices argument monomial) unit argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardRankOne
