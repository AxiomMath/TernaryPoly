module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalAutomorphy
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Tactic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Valuation.IsTrivialOn

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem rational_pair_integral_elimination (first second : ℚ) :
    ∃ matrix : GeneralLinearGroup (Fin 2) ℤ,
      first * (matrix.val 0 0 : ℚ) + second * (matrix.val 1 0 : ℚ) = 0 := by
  by_cases second_zero : second = 0
  · let matrix : GeneralLinearGroup (Fin 2) ℤ :=
      ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by decide, by decide⟩
    exact ⟨matrix, by simp [matrix, second_zero]⟩
  · obtain ⟨matrix, first_column, second_column⟩ :=
      (Rat.isCoprime_num_den (first / second)).symm.neg_right.exists_SL2_col 0
    refine ⟨SpecialLinearGroup.toGL matrix, ?_⟩
    change first * (matrix.val 0 0 : ℚ) + second * (matrix.val 1 0 : ℚ) = 0
    rw [first_column, second_column]
    have denominator_nonzero : ((first / second).den : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (first / second).den_nz
    have ratio := (div_eq_div_iff denominator_nonzero second_zero).mp
      (Rat.num_div_den (first / second))
    push_cast
    nlinarith

theorem rational_first_integral_elimination (matrix : RationalGL3) :
    ∃ integralMatrix : IntegralGL3,
      (matrix * integralRational integralMatrix).val 2 0 = 0 := by
  obtain ⟨binary, elimination⟩ := rational_pair_integral_elimination (matrix.val 2 0) (matrix.val 2 1)
  refine ⟨planeLevi binary 1, ?_⟩
  change (matrix.val * (integralRational (planeLevi binary 1)).val) 2 0 = 0
  simpa [integralRational, GeneralLinearGroup.map_apply, planeLevi, planeBlock,
    Matrix.mul_apply, Fin.sum_univ_three] using elimination

theorem rational_integral_elimination (matrix : RationalGL3) :
    ∃ integralMatrix : IntegralGL3, InPlaneParabolic (matrix * integralRational integralMatrix) := by
  obtain ⟨first, first_zero⟩ := rational_first_integral_elimination matrix
  let intermediate := matrix * integralRational first
  obtain ⟨binary, elimination⟩ :=
    rational_pair_integral_elimination (intermediate.val 2 1) (intermediate.val 2 2)
  refine ⟨first * lineLevi 1 binary, ?_⟩
  rw [map_mul, ← mul_assoc]
  constructor
  · change (intermediate.val * (integralRational (lineLevi 1 binary)).val) 2 0 = 0
    simpa [integralRational, GeneralLinearGroup.map_apply, lineLevi_val,
      Matrix.mul_apply, Fin.sum_univ_three] using (show intermediate.val 2 0 = 0 from first_zero)
  · change (intermediate.val * (integralRational (lineLevi 1 binary)).val) 2 1 = 0
    simpa [integralRational, GeneralLinearGroup.map_apply, lineLevi_val,
      Matrix.mul_apply, Fin.sum_univ_three] using elimination

theorem rational_integral_plane_decomposition (matrix : RationalGL3) :
    ∃ (parabolic : RationalGL3) (integralMatrix : IntegralGL3),
      matrix = parabolic * integralRational integralMatrix ∧ InPlaneParabolic parabolic := by
  obtain ⟨integralMatrix, parabolic⟩ := rational_integral_elimination matrix
  exact ⟨matrix * integralRational integralMatrix, integralMatrix⁻¹, by simp, parabolic⟩

theorem planeFlag_integral_representative (flag : Flags .plane) :
    ∃ integralMatrix : IntegralGL3, (QuotientGroup.mk (integralRational integralMatrix) : Flags .plane) = flag := by
  obtain ⟨integralMatrix, parabolic⟩ := rational_integral_elimination flag.out⁻¹
  have same_coset : (QuotientGroup.mk flag.out : Flags .plane) =
      QuotientGroup.mk (integralRational integralMatrix) := QuotientGroup.eq.mpr parabolic
  exact ⟨integralMatrix, same_coset.symm.trans (QuotientGroup.out_eq' flag)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
