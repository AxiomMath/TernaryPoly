module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.Denominators
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.NormContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.HeightMajorant
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactMajorant

theorem geometric_majorant (set : Set AdelicGL) (compact : IsCompact set)
    (exponent : ℝ) (negative : exponent < -3) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ argument ∈ set, ∀ flag : Flags .plane,
      ∀ first second : Adeles, ∀ binary : BinaryAdelicGL, ∀ unit : Adelesˣ,
      ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
          (IntegerRows.flagRepresentative flag))⁻¹) * argument =
        planeUnipotent first second * planeLevi binary unit * compactElement →
      (adeleNorm unit : ℝ) ^ exponent ≤ majorant flag := by
  obtain ⟨constant, positive, bounded⟩ := CompactDenominators.compact_height_bound set compact
  refine ⟨fun flag => constant ^ (-exponent) * FlagSummability.flagHeight flag ^ exponent,
    fun flag => mul_nonneg (Real.rpow_nonneg positive.le _)
      (Real.rpow_nonneg (FlagSummability.flagHeight_pos flag).le _),
    (FlagSummability.flagHeight_summable exponent negative).mul_left _, ?_⟩
  intro argument argumentMembership flag first second binary unit compactElement membership decomposition
  exact HeightMajorant.negative_power_bound (FlagSummability.flagHeight_pos flag) positive
    (bounded argument argumentMembership (IntegerRows.flagRepresentative flag)
      first second binary unit compactElement membership decomposition) (by linarith)

theorem rational_mul_det_norm (rational : RationalGL3) (argument : AdelicGL) :
    adeleNorm (GeneralLinearGroup.det (rationalGroup rational * argument)) =
      adeleNorm (GeneralLinearGroup.det argument) := by
  simp only [map_mul, HeightMajorant.rational_det_norm, one_mul]

theorem scalar_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ argument ∈ set, ∀ flag,
        ‖eisensteinSummand extension parameter argument flag‖ ≤ majorant flag := by
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := geometric_majorant set compact
    (-((degree : ℝ) + 6) / 2 - parameter.re) (HeightMajorant.exponent_lt degree parameter halfPlane)
  obtain ⟨determinantBound, determinantBounded⟩ := compact.exists_bound_of_continuousOn
    (AdelicNormContinuity.determinant_weight_continuous
      (binaryInductionExponent degree .plane parameter).re).continuousOn
  let factor : ℝ := |determinantBound| + 1
  have factorNonnegative : 0 ≤ factor := by dsimp [factor]; positivity
  refine ⟨fun flag => (factor * majorant flag) * max bound 0,
    fun flag => mul_nonneg (mul_nonneg factorNonnegative (nonnegative flag)) (le_max_right _ _),
    (summable.mul_left factor).mul_right _, ?_⟩
  intro argument argumentMembership flag
  obtain ⟨first, second, binary, unit, compactElement, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition
      (rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
        (IntegerRows.flagRepresentative flag))⁻¹) * argument)
  have estimate := HeightMajorant.scalar_decomposition_bound data extension flat (max bound 0)
    (fun compactElement membership binary =>
      (bounded compactElement membership binary).trans (le_max_left _ _))
    parameter first second binary unit compactElement membership
  rw [← decomposition, rational_mul_det_norm] at estimate
  have determinantEstimate :
      (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re ≤ factor := by
    have normBound := determinantBounded argument argumentMembership
    rw [Real.norm_eq_abs] at normBound
    exact ((le_abs_self _).trans normBound).trans
      (by dsimp [factor]; linarith [le_abs_self determinantBound])
  rw [HeightMajorant.summand_integralRepresentative data extension parameter (flat.1 parameter)]
  apply estimate.trans
  apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
  exact mul_le_mul determinantEstimate
    (dominates argument argumentMembership flag first second binary unit compactElement membership decomposition)
    (Real.rpow_nonneg (adeleNorm unit).property _) factorNonnegative

theorem summable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Summable (eisensteinSummand extension parameter argument) := by
  obtain ⟨majorant, _, converges, dominates⟩ := scalar_majorant data extension flat bound bounded
    parameter halfPlane {argument} isCompact_singleton
  exact converges.of_norm_bounded (dominates argument (Set.mem_singleton argument))

theorem uniformOn_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (set : Set AdelicGL) (compact : IsCompact set) :
    TendstoUniformlyOn
      (fun finite : Finset (Flags .plane) => fun argument =>
        ∑ flag ∈ finite, eisensteinSummand extension parameter argument flag)
      (fun argument => ∑' flag : Flags .plane, eisensteinSummand extension parameter argument flag)
      atTop set := by
  obtain ⟨majorant, _, converges, dominates⟩ :=
    scalar_majorant data extension flat bound bounded parameter halfPlane set compact
  exact tendstoUniformlyOn_tsum converges (fun flag argument membership => dominates argument membership flag)

theorem continuousOn_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ContinuousOn (fun argument => ∑' flag : Flags .plane,
      eisensteinSummand extension parameter argument flag) set := by
  obtain ⟨majorant, _, converges, dominates⟩ :=
    scalar_majorant data extension flat bound bounded parameter halfPlane set compact
  apply continuousOn_tsum _ converges (fun flag argument membership => dominates argument membership flag)
  intro flag
  exact ((InducedContinuity.induced_continuous data .plane parameter _ (flat.1 parameter)).comp
    (continuous_const.mul continuous_id)).continuousOn

theorem continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Continuous (fun argument => ∑' flag : Flags .plane,
      eisensteinSummand extension parameter argument flag) := by
  apply continuous_iff_continuousAt.mpr
  intro argument
  obtain ⟨set, compact, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds argument
  exact (continuousOn_compact data extension flat bound bounded parameter halfPlane set compact).continuousAt
    neighborhood

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactMajorant
