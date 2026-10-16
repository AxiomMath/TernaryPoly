module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.PlanePivotMatrices

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

structure LocalPlanePivotCoordinates {K : Type*} [Field K] (integers : Subring K)
    (first second : K) where
  radicalFirst : K
  radicalSecond : K
  scalar : Kˣ
  block : GeneralLinearGroup (Fin 2) K
  compact : GeneralLinearGroup (Fin 3) integers
  factorization : planeOppositeStandardMatrix first second =
    planeUnipotent radicalFirst radicalSecond *
      (planeLevi 1 scalar * (planeLevi block 1 * GeneralLinearGroup.map integers.subtype compact))

theorem planeOppositeStandardMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (first second : R) :
    GeneralLinearGroup.map hom (planeOppositeStandardMatrix first second) =
      planeOppositeStandardMatrix (hom first) (hom second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeOppositeStandardMatrix, GeneralLinearGroup.map_apply]

def localPlaneIntegralCoordinates {K : Type*} [Field K] (integers : Subring K)
    (first second : integers) : LocalPlanePivotCoordinates integers first.val second.val where
  radicalFirst := 0
  radicalSecond := 0
  scalar := 1
  block := 1
  compact := planeOppositeStandardMatrix first second
  factorization := by
    rw [planeOppositeStandardMatrix_map]
    have radical : planeUnipotent (0 : K) 0 = 1 := (planeUnipotentHom K).map_one
    have levi : planeLevi (1 : GeneralLinearGroup (Fin 2) K) 1 = 1 := (planeLeviHom K).map_one
    simp only [radical, levi, one_mul, Subring.coe_subtype]

def localPlaneFirstPivotCoordinates {K : Type*} [Field K] (integers : Subring K)
    (pivot : Kˣ) (other : K) (ratio : other * pivot.inv ∈ integers)
    (reciprocal : pivot.inv ∈ integers) : LocalPlanePivotCoordinates integers pivot.val other where
  radicalFirst := pivot.inv
  radicalSecond := 0
  scalar := pivot
  block := planeFirstPivotBinary pivot other
  compact := planeFirstPivotCompact ⟨other * pivot.inv, ratio⟩ ⟨pivot.inv, reciprocal⟩
  factorization := by
    rw [planeFirstPivotCompact_map]
    exact planeOppositeStandard_first_pivot pivot other

def localPlaneSecondPivotCoordinates {K : Type*} [Field K] (integers : Subring K)
    (pivot : Kˣ) (other : K) (ratio : other * pivot.inv ∈ integers)
    (reciprocal : pivot.inv ∈ integers) : LocalPlanePivotCoordinates integers other pivot.val where
  radicalFirst := 0
  radicalSecond := pivot.inv
  scalar := pivot
  block := planeSecondPivotBinary pivot other
  compact := planeSecondPivotCompact ⟨other * pivot.inv, ratio⟩ ⟨pivot.inv, reciprocal⟩
  factorization := by
    rw [planeSecondPivotCompact_map]
    exact planeOppositeStandard_second_pivot pivot other

theorem valuation_pivot_ne_zero {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) {pivot : K} (large : 1 < valuation pivot) : pivot ≠ 0 := by
  intro zero
  rw [zero, map_zero] at large
  exact (not_lt_of_ge zero_le_one) large

theorem valuation_pivot_inverse_integral {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) {pivot : K} (large : 1 ≤ valuation pivot) :
    pivot⁻¹ ∈ valuation.valuationSubring := by
  rw [valuation.mem_valuationSubring_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ large

theorem valuation_pivot_ratio_integral {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) {pivot other : K} (dominant : valuation other ≤ valuation pivot) :
    other * pivot⁻¹ ∈ valuation.valuationSubring := by
  rw [valuation.mem_valuationSubring_iff, ← div_eq_mul_inv, valuation.map_div]
  exact div_le_one_of_le₀ dominant zero_le

def valuedPlanePivotCoordinates {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (valuation : Valuation K Γ) (first second : K) :
    LocalPlanePivotCoordinates valuation.valuationSubring.toSubring first second := by
  classical
  by_cases integral : valuation first ≤ 1 ∧ valuation second ≤ 1
  · exact localPlaneIntegralCoordinates valuation.valuationSubring.toSubring
      ⟨first, integral.1⟩ ⟨second, integral.2⟩
  · by_cases dominant : valuation second ≤ valuation first
    · have large : 1 < valuation first := by
        by_contra! small
        exact integral ⟨small, dominant.trans small⟩
      exact localPlaneFirstPivotCoordinates valuation.valuationSubring.toSubring
        (Units.mk0 first (valuation_pivot_ne_zero valuation large)) second
        (valuation_pivot_ratio_integral valuation dominant)
        (valuation_pivot_inverse_integral valuation large.le)
    · have large : 1 < valuation second := by
        by_contra! small
        exact integral ⟨(le_of_not_ge dominant).trans small, small⟩
      exact localPlaneSecondPivotCoordinates valuation.valuationSubring.toSubring
        (Units.mk0 second (valuation_pivot_ne_zero valuation large)) first
        (valuation_pivot_ratio_integral valuation (le_of_not_ge dominant))
        (valuation_pivot_inverse_integral valuation large.le)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
