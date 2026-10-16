module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.FlagBlocks

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def generalLinearTranspose {index R : Type*} [Fintype index] [DecidableEq index] [CommRing R]
    (matrix : GeneralLinearGroup index R) : GeneralLinearGroup index R where
  val := matrix.val.transpose
  inv := matrix.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, matrix.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, matrix.val_inv, Matrix.transpose_one]

theorem generalLinearTranspose_twice {index R : Type*} [Fintype index] [DecidableEq index] [CommRing R]
    (matrix : GeneralLinearGroup index R) : generalLinearTranspose (generalLinearTranspose matrix) = matrix := by
  apply Units.ext
  rfl

theorem generalLinearTranspose_mul {index R : Type*} [Fintype index] [DecidableEq index] [CommRing R]
    (first second : GeneralLinearGroup index R) :
    generalLinearTranspose (first * second) = generalLinearTranspose second * generalLinearTranspose first := by
  apply Units.ext
  exact Matrix.transpose_mul first.val second.val

theorem generalLinearTranspose_planeLevi {R : Type*} [CommRing R]
    (block : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    generalLinearTranspose (planeLevi block scalar) = planeLevi (generalLinearTranspose block) scalar := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem generalLinearTranspose_planeUnipotent {R : Type*} [CommRing R] (first second : R) :
    generalLinearTranspose (planeUnipotent first second) = lowerPlaneUnipotent first second := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem arithmeticLevel_lastRow (matrix : arithmeticLevel) :
    (matrix.val.val 2 0 : ZMod 3) = 0 ∧ (matrix.val.val 2 1 : ZMod 3) = 0 := by
  constructor
  · have fixed := congrFun matrix.property 0
    simpa [lastRow, reductionThree, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three] using fixed
  · have fixed := congrFun matrix.property 1
    simpa [lastRow, reductionThree, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three] using fixed

theorem arithmeticGoodLine_exists_blocks (matrix : arithmeticLevel)
    (column_zero : matrix.val.val 0 2 = 0 ∧ matrix.val.val 1 2 = 0) :
    ∃ (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ),
      matrix.val = planeLevi block 1 * lowerPlaneUnipotent (3 * first) (3 * second) := by
  have transpose_level : generalLinearTranspose matrix.val ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree (generalLinearTranspose matrix.val)).val = lastRow
    funext column
    have last_entry := arithmeticLevel_lastEntry matrix
    fin_cases column <;>
      simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three, reductionThree,
        GeneralLinearGroup.map_apply, generalLinearTranspose, Matrix.transpose_apply,
        column_zero.1, column_zero.2, last_entry]
  have transpose_plane : generalLinearTranspose matrix.val ∈ planeParabolic ℤ := column_zero
  obtain ⟨first, second, block, factors⟩ :=
    arithmeticPlane_exists_blocks ⟨generalLinearTranspose matrix.val, transpose_level⟩ transpose_plane
  have original := congrArg generalLinearTranspose factors
  rw [generalLinearTranspose_twice, generalLinearTranspose_mul, generalLinearTranspose_planeLevi,
    generalLinearTranspose_planeUnipotent] at original
  have first_entry : matrix.val.val 2 0 = first := by
    rw [original]
    simp [planeLevi, planeBlock, lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
  have second_entry : matrix.val.val 2 1 = second := by
    rw [original]
    simp [planeLevi, planeBlock, lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
  have entries := arithmeticLevel_lastRow matrix
  rw [first_entry, second_entry] at entries
  obtain ⟨first_quotient, first_eq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd first 3).mp entries.1
  obtain ⟨second_quotient, second_eq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd second 3).mp entries.2
  exact ⟨first_quotient, second_quotient, generalLinearTranspose block,
    original.trans (by rw [first_eq, second_eq]; rfl)⟩

theorem goodLine_stabilizer_exists_blocks
    (matrix : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
    ∃ (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ),
      matrix.val = GeneralLinearGroup.map (Int.castRingHom ℚ)
        (planeLevi block 1 * lowerPlaneUnipotent (3 * first) (3 * second)) := by
  have member := (goodLine_stabilizer_iff matrix.val).mp matrix.property
  obtain ⟨integer, equality⟩ := member.1
  have column_zero : integer.val.val 0 2 = 0 ∧ integer.val.val 1 2 = 0 := by
    have rational_zero := member.2
    rw [← equality] at rational_zero
    constructor
    · have first : (integer.val.val 0 2 : ℚ) = 0 := rational_zero.1
      exact_mod_cast first
    · have second : (integer.val.val 1 2 : ℚ) = 0 := rational_zero.2
      exact_mod_cast second
  obtain ⟨first, second, block, factors⟩ := arithmeticGoodLine_exists_blocks integer column_zero
  refine ⟨first, second, block, ?_⟩
  rw [← factors, ← equality]
  rfl

theorem goodLineBlocks_arithmeticLevel (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ) :
    planeLevi block 1 * lowerPlaneUnipotent (3 * first) (3 * second) ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (planeLevi block 1 * lowerPlaneUnipotent (3 * first) (3 * second))).val = lastRow
  funext column
  fin_cases column <;>
    simp [lastRow, reductionThree, lowerPlaneUnipotent, planeLevi,
      planeBlock, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three,
      show (3 : ZMod 3) = 0 by decide]

theorem goodLine_stabilizer_blocks_iff (matrix : RationalGL3) :
    matrix ∈ flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ↔
      ∃ (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ),
        matrix = GeneralLinearGroup.map (Int.castRingHom ℚ)
          (planeLevi block 1 * lowerPlaneUnipotent (3 * first) (3 * second)) := by
  constructor
  · intro member
    exact goodLine_stabilizer_exists_blocks ⟨matrix, member⟩
  · rintro ⟨first, second, block, rfl⟩
    apply goodLine_stabilizer_iff _ |>.mpr
    constructor
    · exact ⟨⟨planeLevi block 1 * lowerPlaneUnipotent (3 * first) (3 * second),
        goodLineBlocks_arithmeticLevel first second block⟩, rfl⟩
    · constructor <;>
        simp [lowerPlaneUnipotent, planeLevi, planeBlock,
          Matrix.mul_apply, Fin.sum_univ_three]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
