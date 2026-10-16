module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem quotient_stabilizer_iff {G : Type*} [Group G] (subgroup : Subgroup G)
    (representative element : G) :
    element ∈ MulAction.stabilizer G (QuotientGroup.mk representative : G ⧸ subgroup) ↔
      representative⁻¹ * element * representative ∈ subgroup := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (element * representative) : G ⧸ subgroup) =
    QuotientGroup.mk representative ↔ _
  rw [eq_comm, QuotientGroup.eq, ← mul_assoc]

theorem identityPlane_stabilizer_iff (matrix : RationalGL3) :
    matrix ∈ flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) ↔
      matrix ∈ rationalLevel ∧ matrix ∈ planeParabolic ℚ := by
  change (matrix ∈ rationalLevel ∧
    matrix ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk (1 : RationalGL3) : Flags .plane)) ↔ _
  rw [quotient_stabilizer_iff]
  simp only [inv_one, one_mul, mul_one]
  rfl

theorem goodLine_stabilizer_iff (matrix : RationalGL3) :
    matrix ∈ flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ↔
      matrix ∈ rationalLevel ∧ matrix.val 0 2 = 0 ∧ matrix.val 1 2 = 0 := by
  change (matrix ∈ rationalLevel ∧
    matrix ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk rationalGoodLine : Flags .line)) ↔ _
  rw [quotient_stabilizer_iff, rationalGoodLine_inverse]
  change (matrix ∈ rationalLevel ∧
    (rationalGoodLine * matrix * rationalGoodLine).val 1 0 = 0 ∧
    (rationalGoodLine * matrix * rationalGoodLine).val 2 0 = 0) ↔ _
  simp [rationalGoodLine, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
    and_comm]

theorem integerUnit_eq_one_of_reduce_three (unit : ℤˣ) (reduction : (unit.val : ZMod 3) = 1) :
    unit = 1 := by
  apply Units.ext
  rcases Int.isUnit_iff.mp unit.isUnit with positive | negative
  · exact positive
  · rw [negative] at reduction
    exact (show (-1 : ZMod 3) ≠ 1 by decide).elim reduction

theorem arithmeticLevel_lastEntry (matrix : arithmeticLevel) :
    (matrix.val.val 2 2 : ZMod 3) = 1 := by
  have fixed := congrFun matrix.property 2
  simpa [lastRow, reductionThree, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three] using fixed

theorem arithmeticPlane_exists_blocks (matrix : arithmeticLevel)
    (plane : matrix.val ∈ planeParabolic ℤ) :
    ∃ (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ),
      matrix.val = planeUnipotent first second * planeLevi block 1 := by
  obtain ⟨first, second, scalar, block, factorization⟩ :=
    planeParabolic_exists_decomposition ⟨matrix.val, plane⟩
  have last_entry : matrix.val.val 2 2 = scalar.val := by
    rw [factorization]
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have scalar_one := integerUnit_eq_one_of_reduce_three scalar (by
    rw [← last_entry]
    exact arithmeticLevel_lastEntry matrix)
  refine ⟨first, second, block, ?_⟩
  rw [scalar_one] at factorization
  have identity : planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) 1 = 1 := by
    apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  simpa only [identity, one_mul] using factorization

theorem identityPlane_stabilizer_exists_blocks
    (matrix : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    ∃ (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ),
      matrix.val = GeneralLinearGroup.map (Int.castRingHom ℚ)
        (planeUnipotent first second * planeLevi block 1) := by
  have member := (identityPlane_stabilizer_iff matrix.val).mp matrix.property
  obtain ⟨integer, equality⟩ := member.1
  have plane : integer.val ∈ planeParabolic ℤ := by
    have rational_plane := member.2
    rw [← equality] at rational_plane
    constructor
    · have first : (integer.val.val 2 0 : ℚ) = 0 := rational_plane.1
      exact_mod_cast first
    · have second : (integer.val.val 2 1 : ℚ) = 0 := rational_plane.2
      exact_mod_cast second
  obtain ⟨first, second, block, factors⟩ := arithmeticPlane_exists_blocks integer plane
  refine ⟨first, second, block, ?_⟩
  rw [← factors, ← equality]
  rfl

theorem planeBlocks_arithmeticLevel (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ) :
    planeUnipotent first second * planeLevi block 1 ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (planeUnipotent first second * planeLevi block 1)).val = lastRow
  funext column
  fin_cases column <;>
    simp [lastRow, reductionThree, planeUnipotent, planeLevi,
      planeBlock, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three]

theorem identityPlane_stabilizer_blocks_iff (matrix : RationalGL3) :
    matrix ∈ flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) ↔
      ∃ (first second : ℤ) (block : GeneralLinearGroup (Fin 2) ℤ),
        matrix = GeneralLinearGroup.map (Int.castRingHom ℚ)
          (planeUnipotent first second * planeLevi block 1) := by
  constructor
  · intro member
    exact identityPlane_stabilizer_exists_blocks ⟨matrix, member⟩
  · rintro ⟨first, second, block, rfl⟩
    apply identityPlane_stabilizer_iff _ |>.mpr
    constructor
    · exact ⟨⟨planeUnipotent first second * planeLevi block 1,
        planeBlocks_arithmeticLevel first second block⟩, rfl⟩
    · constructor <;>
        simp [planeUnipotent, planeLevi, planeBlock,
          Matrix.mul_apply, Fin.sum_univ_three]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
