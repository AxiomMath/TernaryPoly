module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.LeviProjection
public import Mathlib.GroupTheory.GroupExtension.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem planeUnipotent_zero {R : Type*} [CommRing R] : planeUnipotent (0 : R) 0 = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem lowerPlaneUnipotent_zero {R : Type*} [CommRing R] : lowerPlaneUnipotent (0 : R) 0 = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

def arithmeticLeviHom : GeneralLinearGroup (Fin 2) ℤ →* RationalGL3 where
  toFun := arithmeticLevi
  map_one' := by
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi 1 1) = 1
    rw [show planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) 1 = 1 from (planeLeviHom ℤ).map_one, map_one]
  map_mul' first second := by
    have equality := (planeLeviHom ℤ).map_mul (first, 1) (second, 1)
    change planeLevi (first * second) (1 * 1) = planeLevi first 1 * planeLevi second 1 at equality
    rw [one_mul] at equality
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi (first * second) 1) = _
    rw [equality, map_mul]
    rfl

theorem arithmeticLevi_identityPlane (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    arithmeticLevi matrix ∈ flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) := by
  apply (identityPlane_stabilizer_blocks_iff _).mpr
  exact ⟨0, 0, matrix, by rw [planeUnipotent_zero, one_mul]; rfl⟩

theorem arithmeticLevi_goodLine (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    arithmeticLevi matrix ∈ flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) := by
  apply (goodLine_stabilizer_blocks_iff _).mpr
  exact ⟨0, 0, matrix, by rw [mul_zero, lowerPlaneUnipotent_zero, mul_one]; rfl⟩

def identityPlaneRadicalInclusion :
    RadicalLattice →* flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) :=
  upperRadicalLattice.codRestrict _ upperRadicalLattice_stabilizer

def goodLineRadicalInclusion :
    RadicalLattice →* flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) :=
  lowerRadicalLattice.codRestrict _ lowerRadicalLattice_stabilizer

def identityPlaneLeviSection :
    GeneralLinearGroup (Fin 2) ℤ →* flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) :=
  arithmeticLeviHom.codRestrict _ arithmeticLevi_identityPlane

def goodLineLeviSection :
    GeneralLinearGroup (Fin 2) ℤ →* flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) :=
  arithmeticLeviHom.codRestrict _ arithmeticLevi_goodLine

theorem upperLeftBlock_arithmeticLevi (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    upperLeftBlock (arithmeticLevi matrix).val = integralBinaryMatrix matrix := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperLeftBlock, arithmeticLevi, integralBinaryMatrix, GeneralLinearGroup.map_apply, planeLevi, planeBlock]

theorem identityPlaneLeviProjection_section (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    identityPlaneLeviProjection (identityPlaneLeviSection matrix) = matrix := by
  apply integralBinaryMatrix_injective
  rw [identityPlaneLeviProjection_spec]
  exact upperLeftBlock_arithmeticLevi matrix

theorem goodLineLeviProjection_section (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineLeviProjection (goodLineLeviSection matrix) = matrix := by
  apply integralBinaryMatrix_injective
  rw [goodLineLeviProjection_spec]
  exact upperLeftBlock_arithmeticLevi matrix

theorem identityPlaneLeviProjection_radical (element : RadicalLattice) :
    identityPlaneLeviProjection (identityPlaneRadicalInclusion element) = 1 := by
  apply integralBinaryMatrix_injective
  rw [identityPlaneLeviProjection_spec, map_one]
  change upperLeftBlock (planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ)).val = 1
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem goodLineLeviProjection_radical (element : RadicalLattice) :
    goodLineLeviProjection (goodLineRadicalInclusion element) = 1 := by
  apply integralBinaryMatrix_injective
  rw [goodLineLeviProjection_spec, map_one]
  change upperLeftBlock (lowerPlaneUnipotent (3 * (element.toAdd.1 : ℚ)) (3 * (element.toAdd.2 : ℚ))).val = 1
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem identityPlaneLeviProjection_blocks
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (first second : ℤ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (factorization : element.val = GeneralLinearGroup.map (Int.castRingHom ℚ)
      (planeUnipotent first second * planeLevi matrix 1)) : identityPlaneLeviProjection element = matrix := by
  apply integralBinaryMatrix_injective
  rw [identityPlaneLeviProjection_spec, factorization]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperLeftBlock, integralBinaryMatrix, GeneralLinearGroup.map_apply,
      planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem goodLineLeviProjection_blocks
    (element : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (first second : ℤ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (factorization : element.val = GeneralLinearGroup.map (Int.castRingHom ℚ)
      (planeLevi matrix 1 * lowerPlaneUnipotent (3 * first) (3 * second))) : goodLineLeviProjection element = matrix := by
  apply integralBinaryMatrix_injective
  rw [goodLineLeviProjection_spec, factorization]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperLeftBlock, integralBinaryMatrix, GeneralLinearGroup.map_apply,
      lowerPlaneUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem identityPlaneRadicalInclusion_injective : Function.Injective identityPlaneRadicalInclusion := by
  intro first second equality
  exact upperRadicalLattice_injective (congrArg Subtype.val equality)

theorem goodLineRadicalInclusion_injective : Function.Injective goodLineRadicalInclusion := by
  intro first second equality
  exact lowerRadicalLattice_injective (congrArg Subtype.val equality)

theorem identityPlaneRadical_range : identityPlaneRadicalInclusion.range = identityPlaneLeviProjection.ker := by
  ext element
  constructor
  · rintro ⟨radical, rfl⟩
    exact identityPlaneLeviProjection_radical radical
  · intro member
    obtain ⟨first, second, matrix, factorization⟩ := identityPlane_stabilizer_exists_blocks element
    have matrix_one : matrix = 1 := (identityPlaneLeviProjection_blocks element first second matrix factorization).symm.trans member
    refine ⟨Multiplicative.ofAdd (first, second), ?_⟩
    apply Subtype.ext
    rw [factorization, matrix_one,
      show planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) 1 = 1 from (planeLeviHom ℤ).map_one,
      mul_one, map_planeUnipotent]
    rfl

theorem goodLineRadical_range : goodLineRadicalInclusion.range = goodLineLeviProjection.ker := by
  ext element
  constructor
  · rintro ⟨radical, rfl⟩
    exact goodLineLeviProjection_radical radical
  · intro member
    obtain ⟨first, second, matrix, factorization⟩ := goodLine_stabilizer_exists_blocks element
    have matrix_one : matrix = 1 := (goodLineLeviProjection_blocks element first second matrix factorization).symm.trans member
    refine ⟨Multiplicative.ofAdd (first, second), ?_⟩
    apply Subtype.ext
    rw [factorization, matrix_one,
      show planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) 1 = 1 from (planeLeviHom ℤ).map_one,
      one_mul, map_lowerPlaneUnipotent]
    simp [goodLineRadicalInclusion, lowerRadicalLattice]

def identityPlaneExtension : GroupExtension RadicalLattice
    (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) (GeneralLinearGroup (Fin 2) ℤ) :=
  ⟨identityPlaneRadicalInclusion, identityPlaneLeviProjection, identityPlaneRadicalInclusion_injective,
    identityPlaneRadical_range, fun matrix => ⟨identityPlaneLeviSection matrix, identityPlaneLeviProjection_section matrix⟩⟩

def goodLineExtension : GroupExtension RadicalLattice
    (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) (GeneralLinearGroup (Fin 2) ℤ) :=
  ⟨goodLineRadicalInclusion, goodLineLeviProjection, goodLineRadicalInclusion_injective,
    goodLineRadical_range, fun matrix => ⟨goodLineLeviSection matrix, goodLineLeviProjection_section matrix⟩⟩

def identityPlaneSplitting : identityPlaneExtension.Splitting :=
  ⟨identityPlaneLeviSection, identityPlaneLeviProjection_section⟩

def goodLineSplitting : goodLineExtension.Splitting :=
  ⟨goodLineLeviSection, goodLineLeviProjection_section⟩

def identityPlaneSemidirectEquiv :
    RadicalLattice ⋊[identityPlaneSplitting.conjAct] GeneralLinearGroup (Fin 2) ℤ ≃*
      flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) :=
  identityPlaneSplitting.semidirectProductMulEquiv

def goodLineSemidirectEquiv :
    RadicalLattice ⋊[goodLineSplitting.conjAct] GeneralLinearGroup (Fin 2) ℤ ≃*
      flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) :=
  goodLineSplitting.semidirectProductMulEquiv

end TernaryPeriodPolynomials.SphericalDetection.Helpers
