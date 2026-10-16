module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.HeightBounds
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.PSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem integer_rows_summable_rpow (dimension : ℕ) (exponent : ℝ) (small : exponent < -(dimension : ℝ)) :
    Summable (fun row : Fin dimension → ℤ => ‖(fun index => (row index : ℝ))‖ ^ exponent) := by
  let lattice : Submodule ℤ (Fin dimension → ℝ) :=
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin dimension)))
  have member (row : Fin dimension → ℤ) : (fun index => (row index : ℝ)) ∈ lattice := by
    rw [← (Pi.basisFun ℝ (Fin dimension)).sum_repr (fun index => (row index : ℝ))]
    apply Submodule.sum_mem
    intro index _
    simp only [Pi.basisFun_repr, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem lattice (row index) (Submodule.subset_span ⟨index, rfl⟩)
  let embedding : (Fin dimension → ℤ) → lattice := fun row => ⟨_, member row⟩
  have injective : Function.Injective embedding := by
    intro first second equality
    funext index
    exact Int.cast_injective (congrFun (congrArg Subtype.val equality) index)
  have rank : Module.finrank ℤ lattice = dimension := by
    simpa only [Fintype.card_fin] using
      finrank_span_eq_card ((Pi.basisFun ℝ (Fin dimension)).linearIndependent.restrict_scalars' (R := ℤ))
  have summable := ZLattice.summable_norm_rpow lattice exponent (by rw [rank]; exact small)
  simpa only [Function.comp_def, embedding, ← Submodule.norm_coe] using summable.comp_injective injective

noncomputable def planeFlagIntegralMatrix (flag : Flags .plane) : IntegralGL3 :=
  Classical.choose (planeFlag_integral_representative flag)

theorem planeFlagIntegralMatrix_spec (flag : Flags .plane) :
    (QuotientGroup.mk (integralRational (planeFlagIntegralMatrix flag)) : Flags .plane) = flag :=
  Classical.choose_spec (planeFlag_integral_representative flag)

noncomputable def planeFlagIntegerRow (flag : Flags .plane) : Fin 3 → ℤ :=
  (planeFlagIntegralMatrix flag).inv 2

theorem planeFlagIntegerRow_injective : Function.Injective planeFlagIntegerRow := by
  intro first second same_row
  rw [← planeFlagIntegralMatrix_spec first, ← planeFlagIntegralMatrix_spec second]
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic
    ((integralRational (planeFlagIntegralMatrix first))⁻¹ * integralRational (planeFlagIntegralMatrix second))
  have row_product (column : Fin 3) :
      (((planeFlagIntegralMatrix first)⁻¹ * planeFlagIntegralMatrix second).val) 2 column =
        (1 : Matrix (Fin 3) (Fin 3) ℤ) 2 column := by
    change ((planeFlagIntegralMatrix first).inv * (planeFlagIntegralMatrix second).val) 2 column = _
    rw [Matrix.mul_apply]
    change (∑ index, planeFlagIntegerRow first index * (planeFlagIntegralMatrix second).val index column) = _
    rw [same_row]
    change (((planeFlagIntegralMatrix second).inv * (planeFlagIntegralMatrix second).val) 2 column) = _
    rw [(planeFlagIntegralMatrix second).inv_val]
  have zero_first : (((planeFlagIntegralMatrix first)⁻¹ * planeFlagIntegralMatrix second).val) 2 0 = 0 := by
    simpa using row_product 0
  have zero_second : (((planeFlagIntegralMatrix first)⁻¹ * planeFlagIntegralMatrix second).val) 2 1 = 0 := by
    simpa using row_product 1
  rw [← map_inv, ← map_mul]
  exact ⟨congrArg (fun value : ℤ => (value : ℚ)) zero_first,
    congrArg (fun value : ℤ => (value : ℚ)) zero_second⟩

theorem planeFlagIntegerRow_ne_zero (flag : Flags .plane) : planeFlagIntegerRow flag ≠ 0 := by
  intro zero
  have inverse_eq := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ => matrix 2 2)
    (planeFlagIntegralMatrix flag).inv_val
  change (∑ index, planeFlagIntegerRow flag index * (planeFlagIntegralMatrix flag).val index 2) = 1 at inverse_eq
  simp only [zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at inverse_eq
  norm_num at inverse_eq

theorem planeFlagIntegerRow_summable (exponent : ℝ) (small : exponent < -3) :
    Summable (fun flag : Flags .plane =>
      ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ exponent) := by
  exact (integer_rows_summable_rpow 3 exponent (by norm_num; exact small)).comp_injective
    planeFlagIntegerRow_injective

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
