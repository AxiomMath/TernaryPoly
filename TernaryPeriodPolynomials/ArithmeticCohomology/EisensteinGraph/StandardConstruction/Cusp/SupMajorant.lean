module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.TaylorMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.CompactOrbitIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspSupMajorant

def size {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) : ℝ :=
  cuspSupNorm (CuspLift.vector data .plane parameter function induced argument)

theorem plane_decomposition {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (argument : AdelicGL) :
    size data parameter function induced (planeUnipotent first second * planeLevi binary unit * argument) =
      CuspTaylorBounds.planeWeight degree parameter binary unit * size data parameter function induced argument := by
  unfold size
  rw [AdelicCompactOrbitIntegral.vector_plane_decomposition, cuspSupNorm_smul]
  change ‖_‖ * cuspSupNorm
    (⟨data.cusp.π binary (CuspLift.vector data .plane parameter function induced argument).val,
      data.cusp.smooth_stable _ _ (CuspLift.vector data .plane parameter function induced argument).property⟩ :
        data.cusp.smooth) = _
  rw [cuspSupNorm_translate, norm_mul, norm_mul, data.chi.unitary, one_mul,
    NormPower.normPower_norm, NormPower.normPower_norm]
  rfl

theorem planeRational {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) (argument : AdelicGL) :
    size data parameter function induced (rationalGroup element * argument) =
      size data parameter function induced argument := by
  have decomposition : rationalGroup element =
      planeUnipotent (rationalAdele (element.val 0 2 / element.val 2 2))
        (rationalAdele (element.val 1 2 / element.val 2 2)) *
      planeLevi (GeneralLinearGroup.map rationalAdele
        (PlaneDecomposition.binaryLeviBlock element membership))
        (Units.map rationalAdele (PlaneDecomposition.rankOneBlock element membership)) := by
    conv_lhs => rw [PlaneDecomposition.plane_decomposition element membership]
    rw [map_mul]
    exact congrArg₂ (fun first second : AdelicGL => first * second)
      (PlaneDecomposition.map_planeUnipotent rationalAdele _ _)
      (PlaneDecomposition.map_planeLevi rationalAdele _ _)
  rw [decomposition, plane_decomposition, CuspTaylorBounds.planeWeight,
    GeneralLinearGroup.map_det, RationalNorm.rational_norm, RationalNorm.rational_norm]
  simp

theorem representative {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : RationalGL3) (related : first⁻¹ * second ∈ planeParabolic ℚ) (argument : AdelicGL) :
    size data parameter function induced (rationalGroup first⁻¹ * argument) =
      size data parameter function induced (rationalGroup second⁻¹ * argument) := by
  have equality := planeRational data parameter function induced (first⁻¹ * second) related
    (rationalGroup second⁻¹ * argument)
  have product : rationalGroup (first⁻¹ * second) * (rationalGroup second⁻¹ * argument) =
      rationalGroup first⁻¹ * argument := by
    rw [← mul_assoc, ← map_mul, mul_assoc, mul_inv_cancel, mul_one]
  rwa [product] at equality

theorem domain_majorant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain, ∀ element : RationalGL3,
        size data parameter function induced
          (rationalGroup element⁻¹ * (lineUnipotent coordinates.1 coordinates.2 * argument)) ≤
            majorant (QuotientGroup.mk element) := by
  obtain ⟨constant, constantNonnegative, bounded⟩ :=
    CompactScalarRealization.induced_uniform_binary_bound data parameter function induced
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := HeightMajorant.domain_majorant argument
    (-((degree : ℝ) + 6) / 2 - parameter.re) (HeightMajorant.exponent_lt degree parameter halfPlane)
  let factor := (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
    (binaryInductionExponent degree .plane parameter).re
  have factorNonnegative : 0 ≤ factor := Real.rpow_nonneg (adeleNorm _).property _
  refine ⟨fun flag => (factor * majorant flag) * constant,
    fun flag => mul_nonneg (mul_nonneg factorNonnegative (nonnegative flag)) constantNonnegative,
    (summable.mul_left factor).mul_right constant, ?_⟩
  intro coordinates membership element
  let flag : Flags .plane := QuotientGroup.mk element
  let integralRepresentative := GeneralLinearGroup.map (Int.castRingHom ℚ) (IntegerRows.flagRepresentative flag)
  have related : element⁻¹ * integralRepresentative ∈ planeParabolic ℚ :=
    QuotientGroup.eq.mp (IntegerRows.flagRepresentative_spec flag).symm
  rw [representative data parameter function induced element integralRepresentative related]
  obtain ⟨first, second, binary, unit, compact, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition
      (rationalGroup integralRepresentative⁻¹ * (lineUnipotent coordinates.1 coordinates.2 * argument))
  have weight : CuspTaylorBounds.planeWeight degree parameter binary unit ≤ factor * majorant flag := by
    unfold CuspTaylorBounds.planeWeight
    rw [InducedHeight.plane_weight_identity degree parameter first second binary unit compact compactMembership,
      ← decomposition, HeightMajorant.translated_det_norm]
    exact mul_le_mul_of_nonneg_left
      (dominates coordinates membership flag first second binary unit compact compactMembership decomposition)
      factorNonnegative
  rw [decomposition, plane_decomposition]
  exact mul_le_mul weight (cuspSupNorm_le _ constant (bounded compact compactMembership))
    (cuspSupNorm_nonneg _) (mul_nonneg factorNonnegative (nonnegative flag))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspSupMajorant
