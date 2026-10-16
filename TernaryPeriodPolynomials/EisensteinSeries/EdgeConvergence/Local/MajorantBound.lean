module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Height
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Height
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Decomposition

@[expose] public section


/-!
# Power majorant of the local standard integrand

For plane-induced data of degree `n` at the parameter `s`, the norm of the local standard integrand
at the coordinates `u` is at most a constant times the local height of `u` to the power
`-(n + 6) / 2 - Re s`, for every argument integral at the finite places.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The determinant of the Weyl-translated local argument has the norm of the determinant of the
argument. -/
theorem standardArgument_det_norm (coordinates : LocalLine × LocalLine) (argument : AdelicGL) :
    adeleNorm (GeneralLinearGroup.det (weyl⁻¹ * localRadical coordinates * argument)) =
      adeleNorm (GeneralLinearGroup.det argument) := by
  have weylInverse : rationalGroup ((weyl : RationalGL3)⁻¹) = (weyl⁻¹ : AdelicGL) := by
    rw [map_inv]
    congr 1
    exact map_weyl rationalAdele
  have translated := HeightMajorant.translated_det_norm ((weyl : RationalGL3)⁻¹)
    (localAdele coordinates.1, localAdele coordinates.2) argument
  rw [weylInverse] at translated
  rw [mul_assoc]
  exact translated

/-- The norm of the local standard integrand is bounded by a power of the local height, with a
constant given by explicit bounds for the argument. -/
theorem localIntegrand_norm_le_of_bounds {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite : finiteGroup argument = GeneralLinearGroup.map integralEmbedding integral)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact →
      ‖(CuspLift.vector data .plane parameter function induced compact).val‖ ≤ bound)
    (discriminant : ℝ)
    (discriminantBound : ∑ index, ∑ column, ((realGroup argument).inv column index) ^ 2 ≤
      discriminant)
    (determinantBound : ℝ)
    (determinantControl : (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
      (binaryInductionExponent degree .plane parameter).re ≤ determinantBound)
    (coordinates : LocalLine × LocalLine) :
    ‖localIntegrand data parameter function induced argument coordinates‖ ≤
      (determinantBound * ((3 * Real.sqrt (discriminant + 1)) ^
        (-(-((degree : ℝ) + 6) / 2 - parameter.re))) * max bound 0) *
        localHeight coordinates ^ (-((degree : ℝ) + 6) / 2 - parameter.re) := by
  have exponentNonpositive : -((degree : ℝ) + 6) / 2 - parameter.re ≤ 0 := by linarith
  have discriminantNonneg : 0 ≤ ∑ index, ∑ column, ((realGroup argument).inv column index) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have rootPositive : 0 < Real.sqrt (discriminant + 1) :=
    Real.sqrt_pos.mpr (by linarith)
  have scalePositive : 0 < 3 * Real.sqrt (discriminant + 1) := mul_pos three_pos rootPositive
  have determinantNonneg : 0 ≤ (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
      (binaryInductionExponent degree .plane parameter).re :=
    Real.rpow_nonneg (adeleNorm _).property _
  obtain ⟨first, second, binary, unit, compact, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition
      (weyl⁻¹ * localRadical coordinates * argument)
  have estimate := HilbertHeight.decomposition_bound data parameter function induced (max bound 0)
    (fun compact membership => (bounded compact membership).trans (le_max_left _ _))
    first second binary unit compact compactMembership
  rw [← decomposition, standardArgument_det_norm] at estimate
  have heightPositive : 0 < localHeight coordinates := localHeight_pos coordinates
  have cornerLower := corner_lower_bound argument integral finite discriminant discriminantBound
    coordinates first second binary unit compact compactMembership decomposition
  have lower : localHeight coordinates ≤ (3 * Real.sqrt (discriminant + 1)) *
      (adeleNorm unit : ℝ) := (inv_mul_le_iff₀ scalePositive).mp cornerLower
  have powerBound := HeightMajorant.negative_power_bound heightPositive scalePositive lower
    exponentNonpositive
  change ‖(CuspLift.vector data .plane parameter function induced
    (weyl⁻¹ * localRadical coordinates * argument)).val‖ ≤ _
  refine estimate.trans ?_
  have unitNonneg : 0 ≤ (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re) :=
    Real.rpow_nonneg (adeleNorm unit).property _
  calc (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re *
        (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re) * max bound 0
      ≤ (determinantBound * ((3 * Real.sqrt (discriminant + 1)) ^
          (-(-((degree : ℝ) + 6) / 2 - parameter.re)) *
            localHeight coordinates ^ (-((degree : ℝ) + 6) / 2 - parameter.re))) * max bound 0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul determinantControl powerBound unitNonneg
          (determinantNonneg.trans determinantControl)) (le_max_right _ _)
    _ = _ := by ring

/-- The norm of the local standard integrand is bounded by a power of the local height. -/
theorem localIntegrand_norm_le {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite : finiteGroup argument = GeneralLinearGroup.map integralEmbedding integral) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ coordinates : LocalLine × LocalLine,
      ‖localIntegrand data parameter function induced argument coordinates‖ ≤
        constant * localHeight coordinates ^ (-((degree : ℝ) + 6) / 2 - parameter.re) := by
  obtain ⟨bound, bounded⟩ := CuspLift.bounded data .plane parameter function induced
  refine ⟨_, ?_, localIntegrand_norm_le_of_bounds data parameter function induced halfPlane
    argument integral finite bound bounded _ le_rfl _ le_rfl⟩
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (adeleNorm _).property _)
    (Real.rpow_nonneg (mul_pos three_pos (Real.sqrt_pos.mpr (by
      have : 0 ≤ ∑ index, ∑ column, ((realGroup argument).inv column index) ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith))).le _)) (le_max_right _ _)

/-- The local standard integrand is integrable on the local radical for parameters with
`Re s > -n/2 - 1`, in particular at the edge `Re s = -n/2`. -/
theorem localIntegrand_integrable {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite : finiteGroup argument = GeneralLinearGroup.map integralEmbedding integral) :
    Integrable (localIntegrand data parameter function induced argument) localRadicalMeasure := by
  obtain ⟨constant, -, dominated⟩ :=
    localIntegrand_norm_le data parameter function induced halfPlane argument integral finite
  refine integrable_of_norm_le_localHeight_rpow _
    (localIntegrand_continuous data parameter function induced argument).aestronglyMeasurable
    ((degree : ℝ) / 2 + 3 + parameter.re) constant (by linarith) ?_
  intro coordinates
  have exponent : -((degree : ℝ) + 6) / 2 - parameter.re =
      -((degree : ℝ) / 2 + 3 + parameter.re) := by ring
  rw [← exponent]
  exact dominated coordinates

end TernaryPeriodPolynomials.EdgeConvergence
