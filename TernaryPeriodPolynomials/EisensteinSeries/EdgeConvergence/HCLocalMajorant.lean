module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.TaylorProducer
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.SupMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatNormStrip

@[expose] public section


/-!
# Sup-norm majorant of the local standard integrand, uniform on vertical strips

Original work by Claude Sonnet 5.5.

For a flat family of plane-induced sections and an argument `g` with integral finite part, the
sup-norm seminorm `cuspSupNorm` (the supremum over all binary adeles of the realization) of the plane
cusp lift at `w⁻¹ n(u) g` is bounded, uniformly for the parameter in a vertical strip
`lower ≤ Re s ≤ upper` inside the half plane `Re s > -n/2 - 1`, by a constant times
`localHeight u ^ (-(n/2 + 3 + lower))`, which is integrable on the local radical.
The plane weight of a decomposition is `exp (offset + rate * Re s)`, hence at most the sum of its
values on the two boundary lines of the strip.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

theorem one_le_localHeight (coordinates : LocalLine × LocalLine) : 1 ≤ localHeight coordinates := by
  unfold localHeight
  have root : 1 ≤ Real.sqrt (1 + coordinates.1.1 ^ 2 + coordinates.2.1 ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg coordinates.1.1, sq_nonneg coordinates.2.1]
  exact one_le_mul_of_one_le_of_one_le root (le_max_left _ _)

/-- The plane weight of a fixed decomposition is the exponential of an affine function of the real
part of the parameter. -/
theorem planeWeight_exp_affine (degree : ℕ) (binary : BinaryAdelicGL) (unit : Adelesˣ) :
    ∃ offset rate : ℝ, ∀ parameter : ℂ,
      CuspTaylorBounds.planeWeight degree parameter binary unit =
        Real.exp (offset + rate * parameter.re) := by
  refine ⟨-Real.log (adeleNorm unit : ℝ) +
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) * ((degree : ℝ) + 4) / 2,
    (-2 * Real.log (adeleNorm unit : ℝ) +
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) / 3, ?_⟩
  intro parameter
  unfold CuspTaylorBounds.planeWeight
  have unitPositive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  have binaryPositive : (0 : ℝ) < (adeleNorm (GeneralLinearGroup.det binary) : ℝ) :=
    adeleNorm_pos (GeneralLinearGroup.det binary)
  rw [Real.rpow_def_of_pos unitPositive, Real.rpow_def_of_pos binaryPositive, ← Real.exp_add]
  congr 1
  simp [inductionExponent, binaryInductionExponent, Complex.mul_re]
  ring

/-- The plane weight on a vertical strip is at most the sum of its values on the boundary lines. -/
theorem planeWeight_strip_bound (degree : ℕ) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (lower upper : ℝ) (parameter : ℂ) (lowerBound : lower ≤ parameter.re)
    (upperBound : parameter.re ≤ upper) :
    CuspTaylorBounds.planeWeight degree parameter binary unit ≤
      CuspTaylorBounds.planeWeight degree (lower : ℂ) binary unit +
        CuspTaylorBounds.planeWeight degree (upper : ℂ) binary unit := by
  obtain ⟨offset, rate, formula⟩ := planeWeight_exp_affine degree binary unit
  rw [formula parameter, formula (lower : ℂ), formula (upper : ℂ), Complex.ofReal_re,
    Complex.ofReal_re]
  have strip := FlatNormStrip.exp_affine_strip_bound 1 offset rate lower upper parameter.re
    zero_le_one lowerBound upperBound
  simpa only [mul_one] using strip

/-- **Strip majorant.** Uniform bound of the sup-norm seminorm of the local standard integrand of a
flat family. -/
theorem localSize_strip_le {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower) (ordered : lower ≤ upper)
    (argument : AdelicGL) (integral : argument ∈ integralArguments) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : ℂ, lower ≤ parameter.re →
      parameter.re ≤ upper → ∀ coordinates : LocalLine × LocalLine,
        cuspSupNorm (CuspLift.vector data .plane parameter (extension parameter)
          (flat.1 parameter) (weyl⁻¹ * localRadical coordinates * argument)) ≤
        constant * localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower)) := by
  obtain ⟨integralArgument, finite⟩ := integral
  obtain ⟨supBound, supNonneg, supBounded⟩ :=
    CompactScalarRealization.flat_uniform_binary_bound data extension flat
  have upperHalfPlane : -(degree : ℝ) / 2 - 1 < upper := lowerHalfPlane.trans_le ordered
  have lowerComplex : -(degree : ℝ) / 2 - 1 < ((lower : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact lowerHalfPlane
  have upperComplex : -(degree : ℝ) / 2 - 1 < ((upper : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact upperHalfPlane
  refine ⟨(localTaylorConstant degree (lower : ℂ) argument +
      localTaylorConstant degree (upper : ℂ) argument) * supBound,
    mul_nonneg (add_nonneg (localTaylorConstant_nonneg degree (lower : ℂ) argument)
      (localTaylorConstant_nonneg degree (upper : ℂ) argument)) supNonneg, ?_⟩
  intro parameter lowerBound upperBound coordinates
  obtain ⟨first, second, binary, unit, compact, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition (weyl⁻¹ * localRadical coordinates * argument)
  have sizeCompact : cuspSupNorm (CuspLift.vector data .plane parameter (extension parameter)
      (flat.1 parameter) compact) ≤ supBound :=
    cuspSupNorm_le _ _ (supBounded parameter compact compactMembership)
  have weightLower := planeWeight_le_localHeight (lower : ℂ) lowerComplex argument
    integralArgument finite coordinates first second binary unit compact compactMembership
    decomposition
  have weightUpper := planeWeight_le_localHeight (upper : ℂ) upperComplex argument
    integralArgument finite coordinates first second binary unit compact compactMembership
    decomposition
  have exponentLower : -((degree : ℝ) + 6) / 2 - ((lower : ℝ) : ℂ).re =
      -((degree : ℝ) / 2 + 3 + lower) := by
    rw [Complex.ofReal_re]
    ring
  have exponentUpper : -((degree : ℝ) + 6) / 2 - ((upper : ℝ) : ℂ).re =
      -((degree : ℝ) / 2 + 3 + upper) := by
    rw [Complex.ofReal_re]
    ring
  rw [exponentLower] at weightLower
  rw [exponentUpper] at weightUpper
  have strip := planeWeight_strip_bound degree binary unit lower upper parameter lowerBound
    upperBound
  have equality : cuspSupNorm (CuspLift.vector data .plane parameter (extension parameter)
      (flat.1 parameter) (weyl⁻¹ * localRadical coordinates * argument)) =
      CuspTaylorBounds.planeWeight degree parameter binary unit *
        cuspSupNorm (CuspLift.vector data .plane parameter (extension parameter)
          (flat.1 parameter) compact) := by
    rw [decomposition]
    exact CuspSupMajorant.plane_decomposition data parameter (extension parameter)
      (flat.1 parameter) first second binary unit compact
  rw [equality]
  have heightPositive : 0 < localHeight coordinates := localHeight_pos coordinates
  have exponentOrder : -((degree : ℝ) / 2 + 3 + upper) ≤ -((degree : ℝ) / 2 + 3 + lower) := by
    linarith
  have powerOrder : localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + upper)) ≤
      localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower)) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_localHeight coordinates) exponentOrder
  calc CuspTaylorBounds.planeWeight degree parameter binary unit *
        cuspSupNorm (CuspLift.vector data .plane parameter (extension parameter)
          (flat.1 parameter) compact)
      ≤ (CuspTaylorBounds.planeWeight degree (lower : ℂ) binary unit +
          CuspTaylorBounds.planeWeight degree (upper : ℂ) binary unit) * supBound :=
        mul_le_mul strip sizeCompact (cuspSupNorm_nonneg _)
          (add_nonneg (CuspTaylorBounds.planeWeight_nonnegative degree (lower : ℂ) binary unit)
            (CuspTaylorBounds.planeWeight_nonnegative degree (upper : ℂ) binary unit))
    _ ≤ ((localTaylorConstant degree (lower : ℂ) argument *
            localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))) +
          (localTaylorConstant degree (upper : ℂ) argument *
            localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + upper)))) * supBound :=
        mul_le_mul_of_nonneg_right (add_le_add weightLower weightUpper) supNonneg
    _ ≤ ((localTaylorConstant degree (lower : ℂ) argument *
            localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))) +
          (localTaylorConstant degree (upper : ℂ) argument *
            localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower)))) * supBound :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left powerOrder
          (localTaylorConstant_nonneg degree (upper : ℂ) argument))) supNonneg
    _ = _ := by ring

/-- The strip majorant is integrable on the local radical. -/
theorem localHeight_strip_integrable {degree : ℕ} (lower : ℝ)
    (lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower) :
    Integrable (fun coordinates : LocalLine × LocalLine =>
      localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))) localRadicalMeasure :=
  localHeight_rpow_integrable ((degree : ℝ) / 2 + 3 + lower) (by linarith)

end TernaryPeriodPolynomials.EdgeConvergence
