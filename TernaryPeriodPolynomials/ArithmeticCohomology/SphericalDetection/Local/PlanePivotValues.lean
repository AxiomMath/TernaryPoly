module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ValuedPlanePivotCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem localPlanePivotCoordinates_parabolic {K : Type*} [Field K] {integers : Subring K}
    {first second : K} (coordinates : LocalPlanePivotCoordinates integers first second) :
    planeOppositeStandardMatrix first second *
      (GeneralLinearGroup.map integers.subtype coordinates.compact)⁻¹ =
        (planeInductionParabolic coordinates.radicalFirst coordinates.radicalSecond
          coordinates.scalar coordinates.block).val := by
  rw [coordinates.factorization]
  change _ = planeUnipotent _ _ * (planeLevi _ _ * planeLevi _ _)
  group

theorem localPlanePivotCoordinates_parabolic_mem {K : Type*} [Field K] {integers : Subring K}
    {first second : K} (coordinates : LocalPlanePivotCoordinates integers first second) :
    planeOppositeStandardMatrix first second *
      (GeneralLinearGroup.map integers.subtype coordinates.compact)⁻¹ ∈ planeParabolic K := by
  rw [localPlanePivotCoordinates_parabolic]
  exact (planeInductionParabolic _ _ _ _).property

theorem localPlanePivotCoordinates_block_entry {K : Type*} [Field K] {integers : Subring K}
    {first second : K} (coordinates : LocalPlanePivotCoordinates integers first second)
    (row column : Fin 2) :
    (planeOppositeStandardMatrix first second *
      (GeneralLinearGroup.map integers.subtype coordinates.compact)⁻¹).val row.castSucc column.castSucc =
        coordinates.block.val row column := by
  rw [localPlanePivotCoordinates_parabolic]
  exact planeInduction_block_entry _ _ _ _ row column

theorem valuedPlanePivotCoordinates_integral {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) (first second : K) (first_integral : valuation first ≤ 1)
    (second_integral : valuation second ≤ 1) :
    valuedPlanePivotCoordinates valuation first second =
      localPlaneIntegralCoordinates valuation.valuationSubring.toSubring
        ⟨first, first_integral⟩ ⟨second, second_integral⟩ := by
  unfold valuedPlanePivotCoordinates
  exact dite_eq_left (And.intro first_integral second_integral)

theorem valuedPlanePivotCoordinates_first {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) (first second : K) (large : 1 < valuation first)
    (dominant : valuation second ≤ valuation first) :
    valuedPlanePivotCoordinates valuation first second =
      localPlaneFirstPivotCoordinates valuation.valuationSubring.toSubring
        (Units.mk0 first (valuation_pivot_ne_zero valuation large)) second
        (valuation_pivot_ratio_integral valuation dominant)
        (valuation_pivot_inverse_integral valuation large.le) := by
  have nonintegral : ¬(valuation first ≤ 1 ∧ valuation second ≤ 1) :=
    fun integral => (not_le_of_gt large) integral.1
  unfold valuedPlanePivotCoordinates
  rw [dite_eq_right nonintegral]
  exact dite_eq_left dominant

theorem valuedPlanePivotCoordinates_second {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) (first second : K) (large : 1 < valuation second)
    (dominant : valuation first < valuation second) :
    valuedPlanePivotCoordinates valuation first second =
      localPlaneSecondPivotCoordinates valuation.valuationSubring.toSubring
        (Units.mk0 second (valuation_pivot_ne_zero valuation large)) first
        (valuation_pivot_ratio_integral valuation dominant.le)
        (valuation_pivot_inverse_integral valuation large.le) := by
  have nonintegral : ¬(valuation first ≤ 1 ∧ valuation second ≤ 1) :=
    fun integral => (not_le_of_gt large) integral.2
  unfold valuedPlanePivotCoordinates
  rw [dite_eq_right nonintegral]
  exact dite_eq_right (not_le_of_gt dominant)

theorem valuedPlanePivotCoordinates_det {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) (first second : K) :
    valuation (GeneralLinearGroup.det (valuedPlanePivotCoordinates valuation first second).block).val =
      (max 1 (max (valuation first) (valuation second)))⁻¹ := by
  by_cases integral : valuation first ≤ 1 ∧ valuation second ≤ 1
  · rw [valuedPlanePivotCoordinates_integral valuation first second integral.1 integral.2]
    simp only [localPlaneIntegralCoordinates, map_one,
      max_le_iff.mpr integral, max_eq_left, inv_one, Units.val_one]
  · by_cases dominant : valuation second ≤ valuation first
    · have large : 1 < valuation first := by
        by_contra! small
        exact integral ⟨small, dominant.trans small⟩
      rw [valuedPlanePivotCoordinates_first valuation first second large dominant]
      simp only [localPlaneFirstPivotCoordinates, planeFirstPivotBinary_det, Units.val_inv_eq_inv_val,
        Units.val_mk0, map_inv₀, max_eq_left dominant, max_eq_right large.le]
    · have strict := lt_of_not_ge dominant
      have large : 1 < valuation second := by
        by_contra! small
        exact integral ⟨strict.le.trans small, small⟩
      rw [valuedPlanePivotCoordinates_second valuation first second large strict]
      simp only [localPlaneSecondPivotCoordinates, planeSecondPivotBinary_det, Units.val_neg,
        valuation.map_neg, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀,
        max_eq_right strict.le, max_eq_right large.le]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
