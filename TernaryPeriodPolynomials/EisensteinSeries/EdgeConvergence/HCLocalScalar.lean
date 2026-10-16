module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.AnalyticParameterIntegral

@[expose] public section


/-!
# Holomorphy in the spectral parameter of the realization of the local standard integral

Original work by Claude Sonnet 5.5.

By `localValue_realizes` the realization at a fixed binary adele `B` of the local Hilbert standard
integral of a flat family is the integral over `(ℝ × ℚ₃)²` of the scalar integrand
`s ↦ realize (v_s(w⁻¹ n(u) g)) B`. The scalar integrand is holomorphic in `s`
(`CuspLift.realizes` and the flat structure), jointly continuous, and dominated, uniformly on a vertical
strip inside `Re s > -n/2 - 1`, by an integrable power of the local height (`HCLocalMajorant`). Holomorphy
of the integral follows from `AnalyticParameterIntegral.integral_analyticAt`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The scalar integrand of a flat family is holomorphic in the spectral parameter. -/
theorem localScalarIntegrand_analyticAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (binary : BinaryAdelicGL) (coordinates : LocalLine × LocalLine)
    (point : ℂ) :
    AnalyticAt ℂ (fun parameter => localScalarIntegrand data parameter (extension parameter)
      (flat.1 parameter) argument binary coordinates) point := by
  have power : AnalyticAt ℂ (fun parameter : ℂ => normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .plane parameter)) point := by
    unfold normPower binaryInductionExponent inductionExponent
    exact ((analyticAt_const.add (analyticAt_const.add analyticAt_id.div_const)).neg.mul
      analyticAt_const).cexp
  have extensionAnalytic : AnalyticAt ℂ (fun parameter => extension parameter
      (binaryLevi .plane binary * (weyl⁻¹ * localRadical coordinates * argument))) point :=
    flat.2.1 _ point
  have product := power.mul extensionAnalytic
  apply product.congr
  exact Filter.Eventually.of_forall (fun parameter =>
    (CuspLift.realizes data .plane parameter (extension parameter) (flat.1 parameter) _
      binary).symm)

/-- The integral of the scalar integrand is holomorphic in the spectral parameter on
`Re s > -n/2 - 1`. -/
theorem localScalarIntegral_analyticAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re)
    (argument : AdelicGL) (integral : argument ∈ integralArguments) (binary : BinaryAdelicGL) :
    AnalyticAt ℂ (fun spectral => ∫ coordinates, localScalarIntegrand data spectral
      (extension spectral) (flat.1 spectral) argument binary coordinates ∂localRadicalMeasure)
      parameter := by
  obtain ⟨lower, lowerSpec⟩ : ∃ lower : ℝ,
      lower = (-(degree : ℝ) / 2 - 1 + parameter.re) / 2 := ⟨_, rfl⟩
  obtain ⟨upper, upperSpec⟩ : ∃ upper : ℝ, upper = parameter.re + 1 := ⟨_, rfl⟩
  have lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower := by rw [lowerSpec]; linarith
  have ordered : lower ≤ upper := by rw [lowerSpec, upperSpec]; linarith
  obtain ⟨constant, _, bounded⟩ := localScalarIntegrand_bound data extension flat lower upper
    lowerHalfPlane ordered argument integral
  refine AnalyticParameterIntegral.integral_analyticAt localRadicalMeasure
    (fun spectral coordinates => localScalarIntegrand data spectral (extension spectral)
      (flat.1 spectral) argument binary coordinates)
    (fun spectral => (localScalarIntegrand_continuous data spectral (extension spectral)
      (flat.1 spectral) argument binary).aestronglyMeasurable)
    {spectral : ℂ | lower < spectral.re ∧ spectral.re < upper}
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    (fun coordinates spectral _ =>
      (localScalarIntegrand_analyticAt data extension flat argument binary coordinates
        spectral).differentiableAt.differentiableWithinAt)
    (hcMajorant degree lower constant) (hcMajorant_integrable lower constant lowerHalfPlane)
    (fun coordinates spectral membership =>
      bounded spectral membership.1.le membership.2.le binary coordinates)
    parameter ⟨?_, ?_⟩
  · rw [lowerSpec]
    linarith
  · rw [upperSpec]
    linarith

/-- **Input 2 (`LocalScalarAnalytic`).** -/
theorem localScalarAnalytic {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EdgeInputs.LocalScalarAnalytic data holomorphic := by
  intro sectionValue argument integral binary parameter halfPlane
  have analytic := localScalarIntegral_analyticAt data
    (EdgeInputs.flatFamily data holomorphic sectionValue)
    (EdgeInputs.flatFamily_flat data holomorphic sectionValue) parameter halfPlane argument
    integral binary
  apply analytic.congr
  have open_ : IsOpen {spectral : ℂ | -(degree : ℝ) / 2 - 1 < spectral.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [open_.mem_nhds halfPlane] with spectral membership
  have memberSmooth := localVectorsSmooth data holomorphic sectionValue spectral membership
    argument integral
  have equality : EdgeInputs.localScalar data holomorphic sectionValue spectral argument binary =
      data.cusp.realize ⟨EdgeInputs.localVector data holomorphic sectionValue spectral argument,
        memberSmooth⟩ binary := by
    unfold EdgeInputs.localScalar
    exact EdgeInputs.vecScalar_of_mem data memberSmooth binary
  rw [equality]
  exact (localValue_realizes data (EdgeInputs.flatFamily data holomorphic sectionValue)
    (EdgeInputs.flatFamily_flat data holomorphic sectionValue) spectral membership argument
    integral binary).symm

/-- Version of `localScalarAnalytic` taking the smoothness input as a hypothesis. -/
theorem localScalarAnalytic_of_smooth {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (_localVectorsSmooth : EdgeInputs.LocalVectorsSmooth data holomorphic) :
    EdgeInputs.LocalScalarAnalytic data holomorphic :=
  localScalarAnalytic data holomorphic

end TernaryPeriodPolynomials.EdgeConvergence
