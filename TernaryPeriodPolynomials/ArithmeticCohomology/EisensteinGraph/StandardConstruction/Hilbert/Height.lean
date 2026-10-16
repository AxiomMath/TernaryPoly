module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.HeightMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ConstantTerm

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertHeight

theorem planeRational_norm {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) (argument : AdelicGL) :
    ‖(CuspLift.vector data .plane parameter function induced (rationalGroup element * argument)).val‖ =
      ‖(CuspLift.vector data .plane parameter function induced argument).val‖ := by
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
  rw [decomposition, CuspLiftCovariance.vector_plane_decomposition_norm,
    GeneralLinearGroup.map_det, RationalNorm.rational_norm, RationalNorm.rational_norm]
  simp

theorem inverseRepresentative_norm {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (first second : RationalGL3) (related : first⁻¹ * second ∈ planeParabolic ℚ) (argument : AdelicGL) :
    ‖(CuspLift.vector data .plane parameter function induced (rationalGroup first⁻¹ * argument)).val‖ =
      ‖(CuspLift.vector data .plane parameter function induced (rationalGroup second⁻¹ * argument)).val‖ := by
  have invariant := planeRational_norm data parameter function induced
    ((first⁻¹ * second)⁻¹) ((planeParabolic ℚ).inv_mem related) (rationalGroup first⁻¹ * argument)
  have equality : rationalGroup ((first⁻¹ * second)⁻¹) * (rationalGroup first⁻¹ * argument) =
      rationalGroup second⁻¹ * argument := by
    rw [← mul_assoc, ← map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [equality] at invariant
  exact invariant.symm

def normSummand {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (flag : Flags .plane) : ℝ :=
  ‖(CuspLift.vector data .plane parameter function induced (rationalGroup flag.out⁻¹ * argument)).val‖

theorem normSummand_mk {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (representative : RationalGL3) :
    normSummand data parameter function induced argument (QuotientGroup.mk representative) =
      ‖(CuspLift.vector data .plane parameter function induced
        (rationalGroup representative⁻¹ * argument)).val‖ := by
  let flag : Flags .plane := QuotientGroup.mk representative
  have related : flag.out⁻¹ * representative ∈ planeParabolic ℚ := by
    apply QuotientGroup.eq.mp
    exact Quotient.out_eq flag
  exact inverseRepresentative_norm data parameter function induced flag.out representative related argument

theorem normSummand_integer {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (flag : Flags .plane) :
    normSummand data parameter function induced argument flag =
      ‖(CuspLift.vector data .plane parameter function induced
        (rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
          (IntegerRows.flagRepresentative flag))⁻¹) * argument)).val‖ := by
  conv_lhs => rw [← IntegerRows.flagRepresentative_spec flag]
  exact normSummand_mk data parameter function induced argument _

theorem normSummand_open_shift {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (rational : ℚ × ℚ) (shift : Adeles × Adeles) :
    normSummand data parameter function induced
        (lineUnipotent shift.1 shift.2 * argument) (BruhatCells.openFlag rational) =
      ‖(CuspLift.vector data .plane parameter function induced
        (weyl⁻¹ * lineUnipotent (rationalAdele rational.1 + shift.1)
          (rationalAdele rational.2 + shift.2) * argument)).val‖ := by
  rw [BruhatCells.openFlag, normSummand_mk, BruhatCells.openRepresentative_inv, map_mul, map_inv]
  change ‖(CuspLift.vector data .plane parameter function induced
    ((GeneralLinearGroup.map rationalAdele (weyl : RationalGL3))⁻¹ *
      GeneralLinearGroup.map rationalAdele (lineUnipotent rational.1 rational.2) *
        (lineUnipotent shift.1 shift.2 * argument))).val‖ = _
  rw [map_weyl, LineDecomposition.map_lineUnipotent,
    mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _), ← lineUnipotent_add]
  simp only [mul_assoc]

theorem decomposition_bound {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact →
      ‖(CuspLift.vector data .plane parameter function induced compact).val‖ ≤ bound)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    ‖(CuspLift.vector data .plane parameter function induced
      (planeUnipotent first second * planeLevi binary unit * compact)).val‖ ≤
      ((adeleNorm (GeneralLinearGroup.det
        (planeUnipotent first second * planeLevi binary unit * compact)) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re *
        (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re)) * bound := by
  rw [← InducedHeight.plane_weight_identity degree parameter first second binary unit compact membership,
    CuspLiftCovariance.vector_plane_decomposition_norm]
  exact mul_le_mul_of_nonneg_left (bounded compact membership)
    (mul_nonneg (Real.rpow_nonneg (adeleNorm unit).property _)
      (Real.rpow_nonneg (adeleNorm (GeneralLinearGroup.det binary)).property _))

theorem domain_majorant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain, ∀ flag,
        normSummand data parameter function induced
          (lineUnipotent coordinates.1 coordinates.2 * argument) flag ≤ majorant flag := by
  obtain ⟨bound, bounded⟩ := CuspLift.bounded data .plane parameter function induced
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := HeightMajorant.domain_majorant argument
    (-((degree : ℝ) + 6) / 2 - parameter.re) (HeightMajorant.exponent_lt degree parameter halfPlane)
  let factor := (adeleNorm (GeneralLinearGroup.det argument) : ℝ) ^
    (binaryInductionExponent degree .plane parameter).re
  have factorNonnegative : 0 ≤ factor := Real.rpow_nonneg (adeleNorm _).property _
  refine ⟨fun flag => (factor * majorant flag) * max bound 0,
    fun flag => mul_nonneg (mul_nonneg factorNonnegative (nonnegative flag)) (le_max_right _ _),
    (summable.mul_left factor).mul_right _, ?_⟩
  intro coordinates membership flag
  obtain ⟨first, second, binary, unit, compact, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition
      (rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ)
        (IntegerRows.flagRepresentative flag))⁻¹) *
          (lineUnipotent coordinates.1 coordinates.2 * argument))
  have estimate := decomposition_bound data parameter function induced (max bound 0)
    (fun compact membership => (bounded compact membership).trans (le_max_left _ _))
    first second binary unit compact compactMembership
  rw [← decomposition, HeightMajorant.translated_det_norm] at estimate
  rw [normSummand_integer]
  exact estimate.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (dominates coordinates membership flag first second binary unit compact compactMembership decomposition)
      factorNonnegative) (le_max_right _ _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertHeight
