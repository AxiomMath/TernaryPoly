module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Lie.Norms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieNorms

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir

noncomputable def casimir (data : CuspidalRepresentation) : Module.End ℂ data.smooth :=
  diagonalOperator data ^ 2 + symmetricOperator data ^ 2 - rotationOperator data ^ 2

theorem casimir_commutator (data : CuspidalRepresentation) (operator : Module.End ℂ data.smooth) :
    casimir data * operator - operator * casimir data =
      diagonalOperator data * (diagonalOperator data * operator - operator * diagonalOperator data) +
      (diagonalOperator data * operator - operator * diagonalOperator data) * diagonalOperator data +
      symmetricOperator data * (symmetricOperator data * operator - operator * symmetricOperator data) +
      (symmetricOperator data * operator - operator * symmetricOperator data) * symmetricOperator data -
      (rotationOperator data * (rotationOperator data * operator - operator * rotationOperator data) +
      (rotationOperator data * operator - operator * rotationOperator data) * rotationOperator data) := by
  simp only [casimir, pow_two, add_mul, sub_mul, mul_add, mul_sub, mul_assoc]
  abel

theorem casimir_rotation (data : CuspidalRepresentation) : Commute (casimir data) (rotationOperator data) := by
  have diagonalReverse : diagonalOperator data * rotationOperator data - rotationOperator data * diagonalOperator data =
      (-2 : ℂ) • symmetricOperator data := by
    calc
      _ = -(rotationOperator data * diagonalOperator data - diagonalOperator data * rotationOperator data) := by abel
      _ = _ := by rw [rotation_diagonal]; module
  have symmetricReverse : symmetricOperator data * rotationOperator data - rotationOperator data * symmetricOperator data =
      (2 : ℂ) • diagonalOperator data := by
    calc
      _ = -(rotationOperator data * symmetricOperator data - symmetricOperator data * rotationOperator data) := by abel
      _ = _ := by rw [rotation_symmetric]; module
  apply sub_eq_zero.mp
  rw [casimir_commutator, diagonalReverse, symmetricReverse, sub_self]
  simp only [mul_smul_comm, smul_mul_assoc, mul_zero, zero_mul]
  module

theorem casimir_diagonal (data : CuspidalRepresentation) : Commute (casimir data) (diagonalOperator data) := by
  have symmetricReverse : symmetricOperator data * diagonalOperator data - diagonalOperator data * symmetricOperator data =
      (2 : ℂ) • rotationOperator data := by
    calc
      _ = -(diagonalOperator data * symmetricOperator data - symmetricOperator data * diagonalOperator data) := by abel
      _ = _ := by rw [diagonal_symmetric]; module
  apply sub_eq_zero.mp
  rw [casimir_commutator, sub_self, symmetricReverse, rotation_diagonal]
  simp only [mul_smul_comm, smul_mul_assoc, mul_zero, zero_mul]
  module

theorem casimir_symmetric (data : CuspidalRepresentation) : Commute (casimir data) (symmetricOperator data) := by
  apply sub_eq_zero.mp
  rw [casimir_commutator, sub_self, diagonal_symmetric, rotation_symmetric]
  simp only [mul_smul_comm, smul_mul_assoc, mul_zero, zero_mul]
  module

theorem casimir_raising (data : CuspidalRepresentation) : Commute (casimir data) (raising data) := by
  change casimir data * raising data = raising data * casimir data
  simp only [raising, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [(casimir_diagonal data).eq, (casimir_symmetric data).eq]

theorem casimir_lowering (data : CuspidalRepresentation) : Commute (casimir data) (lowering data) := by
  change casimir data * lowering data = lowering data * casimir data
  simp only [lowering, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [(casimir_diagonal data).eq, (casimir_symmetric data).eq]

theorem lowering_mul_raising (data : CuspidalRepresentation) :
    lowering data * raising data = casimir data + rotationOperator data ^ 2 + (2 * Complex.I) • rotationOperator data := by
  have expansion : lowering data * raising data =
      diagonalOperator data ^ 2 + symmetricOperator data ^ 2 -
        Complex.I • (diagonalOperator data * symmetricOperator data - symmetricOperator data * diagonalOperator data) := by
    simp only [lowering, raising, add_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
      smul_sub, smul_add, smul_smul, Complex.I_mul_I, neg_smul, one_smul, pow_two]
    abel
  rw [expansion, diagonal_symmetric]
  simp only [casimir, smul_smul]
  module

theorem raising_mul_lowering (data : CuspidalRepresentation) :
    raising data * lowering data = casimir data + rotationOperator data ^ 2 - (2 * Complex.I) • rotationOperator data := by
  have equality := lowering_raising data
  rw [lowering_mul_raising] at equality
  have rearranged := sub_eq_iff_eq_add.mp equality
  have solved : raising data * lowering data =
      casimir data + rotationOperator data ^ 2 + (2 * Complex.I) • rotationOperator data -
      (4 * Complex.I) • rotationOperator data := by
    rw [rearranged]
    abel
  rw [solved]
  module

theorem rotation_sq_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) :
    (rotationOperator data ^ 2) vector = (-(index : ℂ) ^ 2) • vector := by
  rw [pow_two, Module.End.mul_apply, eigen, map_smul, eigen, smul_smul]
  congr 1
  calc
    _ = Complex.I * Complex.I * (index : ℂ) ^ 2 := by ring
    _ = _ := by rw [Complex.I_mul_I, neg_one_mul]

theorem lowering_raising_of_eigen (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (value : ℂ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (casimirEigen : casimir data vector = value • vector) :
    lowering data (raising data vector) = (value - (index : ℂ) * (index + 2)) • vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (lowering_mul_raising data)
  change lowering data (raising data vector) = casimir data vector +
    (rotationOperator data ^ 2) vector + (2 * Complex.I) • rotationOperator data vector at equality
  rw [casimirEigen, rotation_sq_eigen data vector index rotationEigen, rotationEigen, smul_smul] at equality
  rw [equality]
  simp only [mul_assoc, ← mul_assoc Complex.I, Complex.I_mul_I, neg_mul, one_mul, mul_neg]
  module

theorem raising_lowering_of_eigen (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (value : ℂ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (casimirEigen : casimir data vector = value • vector) :
    raising data (lowering data vector) = (value - (index : ℂ) * (index - 2)) • vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (raising_mul_lowering data)
  change raising data (lowering data vector) = casimir data vector +
    (rotationOperator data ^ 2) vector - (2 * Complex.I) • rotationOperator data vector at equality
  rw [casimirEigen, rotation_sq_eigen data vector index rotationEigen, rotationEigen, smul_smul] at equality
  rw [equality]
  simp only [mul_assoc, ← mul_assoc Complex.I, Complex.I_mul_I, neg_mul, one_mul, mul_neg]
  module

theorem raising_casimir_eigen (data : CuspidalRepresentation) (vector : data.smooth) (value : ℂ)
    (eigen : casimir data vector = value • vector) :
    casimir data (raising data vector) = value • raising data vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (casimir_raising data).eq
  change casimir data (raising data vector) = raising data (casimir data vector) at equality
  rw [equality, eigen, map_smul]

theorem lowering_casimir_eigen (data : CuspidalRepresentation) (vector : data.smooth) (value : ℂ)
    (eigen : casimir data vector = value • vector) :
    casimir data (lowering data vector) = value • lowering data vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (casimir_lowering data).eq
  change casimir data (lowering data vector) = lowering data (casimir data vector) at equality
  rw [equality, eigen, map_smul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir
