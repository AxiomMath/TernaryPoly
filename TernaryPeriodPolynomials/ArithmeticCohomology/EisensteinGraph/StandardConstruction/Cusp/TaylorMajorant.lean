module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.TaylorBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Height

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspTaylorMajorant

open CompactTaylorBounds CuspTaylorBounds

def coefficient {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (order : ℕ) (argument : AdelicGL) :=
  coefficients (matrixOrbit data .plane parameter function induced argument) 1 order

theorem planeRational_norm_le {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (element : RationalGL3) (membership : element ∈ planeParabolic ℚ)
    (argument : AdelicGL) (order : ℕ) :
    ‖coefficient data parameter function induced order (rationalGroup element * argument)‖ ≤
      ‖coefficient data parameter function induced order argument‖ := by
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
  unfold coefficient
  rw [decomposition]
  have estimate := plane_coefficient_norm_le data parameter function induced
    (rationalAdele (element.val 0 2 / element.val 2 2))
    (rationalAdele (element.val 1 2 / element.val 2 2))
    (GeneralLinearGroup.map rationalAdele (PlaneDecomposition.binaryLeviBlock element membership))
    (Units.map rationalAdele (PlaneDecomposition.rankOneBlock element membership)) argument order
  simpa only [planeWeight, GeneralLinearGroup.map_det, RationalNorm.rational_norm,
    NNReal.coe_one, Real.one_rpow, one_mul] using estimate

theorem representative_norm_le {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : RationalGL3) (related : first⁻¹ * second ∈ planeParabolic ℚ)
    (argument : AdelicGL) (order : ℕ) :
    ‖coefficient data parameter function induced order (rationalGroup first⁻¹ * argument)‖ ≤
      ‖coefficient data parameter function induced order (rationalGroup second⁻¹ * argument)‖ := by
  have estimate := planeRational_norm_le data parameter function induced (first⁻¹ * second)
    related (rationalGroup second⁻¹ * argument) order
  have equality : rationalGroup (first⁻¹ * second) * (rationalGroup second⁻¹ * argument) =
      rationalGroup first⁻¹ * argument := by
    rw [← mul_assoc, ← map_mul, mul_assoc, mul_inv_cancel, mul_one]
  rwa [equality] at estimate

/-- One summable flag majorant controls every Taylor coefficient, with geometric
dependence on its order and a radius independent of the adelic argument. -/
theorem domain_majorant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ majorant : Flags .plane → ℝ,
      (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      (∀ point, HasFPowerSeriesOnBall (matrixOrbit data .plane parameter function induced point)
        (coefficients (matrixOrbit data .plane parameter function induced point) 1) 1 radius) ∧
      ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain, ∀ representative : RationalGL3,
      ∀ order, ‖coefficient data parameter function induced order
        (rationalGroup representative⁻¹ * (lineUnipotent coordinates.1 coordinates.2 * argument))‖ ≤
          majorant (QuotientGroup.mk representative) * (radius : ℝ)⁻¹ ^ order := by
  obtain ⟨radius, positive, constant, constantNonnegative, bounded⟩ :=
    maximalCompact_uniform data .plane parameter function induced
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := HeightMajorant.domain_majorant argument
    (-((degree : ℝ) + 6) / 2 - parameter.re) (HeightMajorant.exponent_lt degree parameter halfPlane)
  let factor := (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
    (binaryInductionExponent degree .plane parameter).re
  have factorNonnegative : 0 ≤ factor := Real.rpow_nonneg (adeleNorm _).property _
  refine ⟨radius, positive, fun flag => (factor * majorant flag) * constant,
    fun flag => mul_nonneg (mul_nonneg factorNonnegative (nonnegative flag)) constantNonnegative,
    (summable.mul_left factor).mul_right constant, ?_, ?_⟩
  · intro point
    obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition point
    rw [decomposition]
    exact (plane_decomposition_bound data parameter function induced positive constant bounded
      first second binary unit compact membership).1
  · intro coordinates membership representative order
    let flag : Flags .plane := QuotientGroup.mk representative
    let integralRepresentative := GeneralLinearGroup.map (Int.castRingHom ℚ)
      (IntegerRows.flagRepresentative flag)
    have related : representative⁻¹ * integralRepresentative ∈ planeParabolic ℚ :=
      QuotientGroup.eq.mp (IntegerRows.flagRepresentative_spec flag).symm
    apply (representative_norm_le data parameter function induced representative integralRepresentative
      related (lineUnipotent coordinates.1 coordinates.2 * argument) order).trans
    obtain ⟨first, second, binary, unit, compact, compactMembership, decomposition⟩ :=
      AdelicDecomposition.adelic_planeDecomposition
        (rationalGroup integralRepresentative⁻¹ * (lineUnipotent coordinates.1 coordinates.2 * argument))
    have estimate := (plane_decomposition_bound data parameter function induced positive constant bounded
      first second binary unit compact compactMembership).2 order
    have weight : planeWeight degree parameter binary unit ≤ factor * majorant flag := by
      unfold planeWeight
      rw [InducedHeight.plane_weight_identity degree parameter first second binary unit compact compactMembership,
        ← decomposition, HeightMajorant.translated_det_norm]
      exact mul_le_mul_of_nonneg_left
        (dominates coordinates membership flag first second binary unit compact compactMembership decomposition)
        factorNonnegative
    change ‖coefficients (matrixOrbit data .plane parameter function induced _) 1 order‖ ≤ _
    rw [decomposition]
    exact estimate.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right weight constantNonnegative)
      (pow_nonneg (inv_nonneg.mpr radius.property) order))

theorem open_shift {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (rational : ℚ × ℚ) (shift : Adeles × Adeles) (order : ℕ) :
    coefficient data parameter function induced order
        (rationalGroup (BruhatCells.openRepresentative rational)⁻¹ *
          (lineUnipotent shift.1 shift.2 * argument)) =
      coefficient data parameter function induced order
        (weyl⁻¹ * lineUnipotent (rationalAdele rational.1 + shift.1)
          (rationalAdele rational.2 + shift.2) * argument) := by
  rw [BruhatCells.openRepresentative_inv, map_mul, map_inv]
  change coefficient data parameter function induced order
    ((GeneralLinearGroup.map rationalAdele (weyl : RationalGL3))⁻¹ *
      GeneralLinearGroup.map rationalAdele (lineUnipotent rational.1 rational.2) *
        (lineUnipotent shift.1 shift.2 * argument)) = _
  rw [map_weyl, LineDecomposition.map_lineUnipotent,
    mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _), ← lineUnipotent_add]
  simp only [mul_assoc]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspTaylorMajorant
