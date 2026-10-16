module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicDecomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LocalDecomposition

variable {K : Type} [Field K]

theorem reduceLastColumn (element : GL3 K) (integers : Subring K)
    (corner : element.val 2 2 ≠ 0)
    (firstIntegral : element.val 2 0 / element.val 2 2 ∈ integers)
    (secondIntegral : element.val 2 1 / element.val 2 2 ∈ integers) :
    ∃ compact : GL3 integers,
      element * (GeneralLinearGroup.map integers.subtype compact)⁻¹ ∈ planeParabolic K := by
  let first : integers := ⟨element.val 2 0 / element.val 2 2, firstIntegral⟩
  let second : integers := ⟨element.val 2 1 / element.val 2 2, secondIntegral⟩
  refine ⟨lowerPlaneUnipotent first second, ?_⟩
  change (element.val * !![1, 0, 0; 0, 1, 0;
      -(element.val 2 0 / element.val 2 2), -(element.val 2 1 / element.val 2 2), 1]) 2 0 = 0 ∧
    (element.val * !![1, 0, 0; 0, 1, 0;
      -(element.val 2 0 / element.val 2 2), -(element.val 2 1 / element.val 2 2), 1]) 2 1 = 0
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv, mul_left_comm,
      corner]

theorem reduceAfterRotation (element : GL3 K) (integers : Subring K)
    (rotation : GL3 integers)
    (corner : (element * GeneralLinearGroup.map integers.subtype rotation).val 2 2 ≠ 0)
    (firstIntegral : (element * GeneralLinearGroup.map integers.subtype rotation).val 2 0 /
      (element * GeneralLinearGroup.map integers.subtype rotation).val 2 2 ∈ integers)
    (secondIntegral : (element * GeneralLinearGroup.map integers.subtype rotation).val 2 1 /
      (element * GeneralLinearGroup.map integers.subtype rotation).val 2 2 ∈ integers) :
    ∃ compact : GL3 integers,
      element * (GeneralLinearGroup.map integers.subtype compact)⁻¹ ∈ planeParabolic K := by
  obtain ⟨compact, membership⟩ := reduceLastColumn
    (element * GeneralLinearGroup.map integers.subtype rotation) integers corner
    firstIntegral secondIntegral
  refine ⟨compact * rotation⁻¹, ?_⟩
  simpa only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, ← mul_assoc] using membership

variable {Value : Type} [LinearOrderedCommGroupWithZero Value]

theorem ratio_integral (valuation : Valuation K Value) (first second : K)
    (nonzero : second ≠ 0) (domination : valuation first ≤ valuation second) :
    first / second ∈ valuation.integer := by
  change valuation (first / second) ≤ 1
  rw [valuation.map_div]
  exact (div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm
    ((map_ne_zero valuation).mpr nonzero)))).mpr domination

theorem valuation_planeCompact (valuation : Valuation K Value) (element : GL3 K) :
    ∃ compact : GL3 valuation.integer,
      element * (GeneralLinearGroup.map valuation.integer.subtype compact)⁻¹ ∈
        planeParabolic K := by
  obtain ⟨pivot, _, maximal⟩ := Finset.exists_max_image Finset.univ
    (fun index : Fin 3 => valuation (element.val 2 index)) Finset.univ_nonempty
  have dominates : ∀ index : Fin 3,
      valuation (element.val 2 index) ≤ valuation (element.val 2 pivot) :=
    fun index => maximal index (Finset.mem_univ index)
  have nonzero : element.val 2 pivot ≠ 0 := by
    intro vanishes
    have rowZero : ∀ index : Fin 3, element.val 2 index = 0 := by
      intro index
      apply (map_eq_zero valuation).mp
      have bounded := dominates index
      rw [vanishes, map_zero] at bounded
      exact le_antisymm bounded zero_le
    have impossible := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) K => matrix 2 2)
      element.mul_inv
    simp [Matrix.mul_apply, rowZero] at impossible
  fin_cases pivot
  · apply reduceAfterRotation element valuation.integer (weyl : GL3 valuation.integer)
    · simpa [GeneralLinearGroup.map_apply, weyl, Matrix.mul_apply, Fin.sum_univ_three] using nonzero
    · simpa [GeneralLinearGroup.map_apply, weyl, Matrix.mul_apply, Fin.sum_univ_three] using
        ratio_integral valuation (element.val 2 1) (element.val 2 0) nonzero (dominates 1)
    · simpa [GeneralLinearGroup.map_apply, weyl, Matrix.mul_apply, Fin.sum_univ_three] using
        ratio_integral valuation (element.val 2 2) (element.val 2 0) nonzero (dominates 2)
  · apply reduceAfterRotation element valuation.integer (weyl⁻¹ : GL3 valuation.integer)
    · simpa [GeneralLinearGroup.map_apply, weyl, Matrix.mul_apply, Fin.sum_univ_three] using nonzero
    · simpa [GeneralLinearGroup.map_apply, weyl, Matrix.mul_apply, Fin.sum_univ_three] using
        ratio_integral valuation (element.val 2 2) (element.val 2 1) nonzero (dominates 2)
    · simpa [GeneralLinearGroup.map_apply, weyl, Matrix.mul_apply, Fin.sum_univ_three] using
        ratio_integral valuation (element.val 2 0) (element.val 2 1) nonzero (dominates 0)
  · exact reduceLastColumn element valuation.integer nonzero
      (ratio_integral valuation _ _ nonzero (dominates 0))
      (ratio_integral valuation _ _ nonzero (dominates 1))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LocalDecomposition
