module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CocycleParity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.DeterminantGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.OneCocycleExtension

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem integralDeterminant_conj_neg_one (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    integralDeterminantSplitting.conjAct (-1) matrix = modularReflection matrix := by
  apply SpecialLinearGroup.toGL_injective
  have relation := integralDeterminantExtension.inl_conjAct_comm
    (e := integralDeterminantSection (-1)) (n := matrix)
  change SpecialLinearGroup.toGL (integralDeterminantSplitting.conjAct (-1) matrix) =
    integralDeterminantSection (-1) * SpecialLinearGroup.toGL matrix *
      (integralDeterminantSection (-1))⁻¹ at relation
  rw [relation, ← map_inv]
  simp only [inv_neg_one]
  apply Units.ext
  change !![-1, 0; 0, 1] * matrix.val * !![-1, 0; 0, 1] =
    !![matrix.val 0 0, -matrix.val 0 1; -matrix.val 1 0, matrix.val 1 1]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem arithmeticBinaryRep_section_neg_one (degree : ℕ) (twist : ℤ) (even : Even degree)
    (polynomial : Binary.HomogeneousPoly degree) :
    (arithmeticBinaryRep degree twist).ρ (integralDeterminantSection (-1)) polynomial =
      (-1 : ℂ) ^ twist • binaryParityReflection degree polynomial := by
  apply Subtype.ext
  change (Binary.homogeneousAction degree twist
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (integralDeterminantSection (-1))) polynomial).val = _
  rw [Binary.homogeneousAction_coe, Binary.action_apply]
  have determinant : Binary.determinantCharacter twist
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (integralDeterminantSection (-1))) = (-1 : ℂ) ^ twist := by
    change (((integralDeterminantSection (-1)).val.map (Int.castRingHom ℂ)).det) ^ twist = _
    congr 1
    norm_num [integralDeterminantSection, Matrix.det_fin_two, Matrix.map]
  have inverse_matrix :
      ((GeneralLinearGroup.map (Int.castRingHom ℂ) (integralDeterminantSection (-1)))⁻¹).val =
        !![(-1 : ℂ), 0; 0, 1] := by
    rw [← map_inv, ← map_inv]
    simp only [inv_neg_one]
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [GeneralLinearGroup.map_apply, integralDeterminantSection, Matrix.map]
  have reflected : Binary.substitute !![(-1 : ℂ), 0; 0, 1] polynomial.val =
      Binary.substitute !![(1 : ℂ), 0; 0, -1] polynomial.val := by
    have matrix_eq : Matrix.scalar (Fin 2) (-1 : ℂ) * !![1, 0; 0, -1] = !![-1, 0; 0, 1] := by
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← matrix_eq, ← Binary.substitute_comp]
    change Binary.substitute !![(1 : ℂ), 0; 0, -1]
      (Binary.substitute (Matrix.scalar (Fin 2) (-1 : ℂ)) polynomial.val) = _
    rw [binary_substitute_scalar, even.neg_one_pow, one_smul]
  rw [determinant, inverse_matrix, reflected]
  rfl

theorem modularCocycleParity_reflection (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    modularCocycleReflection degree twist (modularCocycleParity degree twist parity cycle) =
      (-1 : ℂ) ^ parity • modularCocycleParity degree twist parity cycle := by
  change modularCocycleReflection degree twist
    ((2 : ℂ)⁻¹ • (cycle + (-1 : ℂ) ^ parity • modularCocycleReflection degree twist cycle)) =
      (-1 : ℂ) ^ parity • ((2 : ℂ)⁻¹ • (cycle + (-1 : ℂ) ^ parity • modularCocycleReflection degree twist cycle))
  rw [map_smul, map_add, map_smul, modularCocycleReflection_involutive degree twist cycle]
  have square : (-1 : ℂ) ^ parity * (-1 : ℂ) ^ parity = 1 := by
    rw [← pow_add]
    exact (show Even (parity + parity) from ⟨parity, rfl⟩).neg_one_pow
  rw [smul_comm ((-1 : ℂ) ^ parity) ((2 : ℂ)⁻¹)]
  congr 1
  rw [smul_add, smul_smul, square, one_smul, add_comm]

theorem modularCocycleParity_conj (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    modularCocycleParity degree twist parity cycle (modularReflection matrix) =
      (-1 : ℂ) ^ parity • binaryParityReflection degree
        (modularCocycleParity degree twist parity cycle matrix) := by
  let reflected := modularCocycleParity degree twist parity cycle
  have eigen := congrArg (fun cocycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist) =>
    cocycle matrix) (modularCocycleParity_reflection degree twist parity cycle)
  change binaryParityReflection degree (reflected (modularReflection matrix)) =
    (-1 : ℂ) ^ parity • reflected matrix at eigen
  have twice := congrArg (binaryParityReflection degree) eigen
  rw [binaryParityReflection_involutive degree (reflected (modularReflection matrix))] at twice
  exact twice.trans (map_smul (binaryParityReflection degree) ((-1 : ℂ) ^ parity) (reflected matrix))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
