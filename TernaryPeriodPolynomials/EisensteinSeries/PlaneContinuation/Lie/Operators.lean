module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Infinitesimal
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RotationTypes

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

def rotationMatrix : BinaryMatrix := !![0, -1; 1, 0]

def diagonalMatrix : BinaryMatrix := !![1, 0; 0, -1]

def symmetricMatrix : BinaryMatrix := !![0, 1; 1, 0]

theorem rotation_diagonal_commutator :
    rotationMatrix * diagonalMatrix - diagonalMatrix * rotationMatrix = (2 : ℝ) • symmetricMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [rotationMatrix, diagonalMatrix, symmetricMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotation_symmetric_commutator :
    rotationMatrix * symmetricMatrix - symmetricMatrix * rotationMatrix = (-2 : ℝ) • diagonalMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [rotationMatrix, diagonalMatrix, symmetricMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_symmetric_commutator :
    diagonalMatrix * symmetricMatrix - symmetricMatrix * diagonalMatrix = (-2 : ℝ) • rotationMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [rotationMatrix, diagonalMatrix, symmetricMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem generator_eq : generator = (2 * Real.pi) • rotationMatrix := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixRotationSpan.generator_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [rotationMatrix]

noncomputable def rotationOperator (data : CuspidalRepresentation) : Module.End ℂ data.smooth :=
  directionalOperator data rotationMatrix

noncomputable def diagonalOperator (data : CuspidalRepresentation) : Module.End ℂ data.smooth :=
  directionalOperator data diagonalMatrix

noncomputable def symmetricOperator (data : CuspidalRepresentation) : Module.End ℂ data.smooth :=
  directionalOperator data symmetricMatrix

noncomputable def raising (data : CuspidalRepresentation) : Module.End ℂ data.smooth :=
  diagonalOperator data - Complex.I • symmetricOperator data

noncomputable def lowering (data : CuspidalRepresentation) : Module.End ℂ data.smooth :=
  diagonalOperator data + Complex.I • symmetricOperator data

theorem rotation_diagonal (data : CuspidalRepresentation) :
    rotationOperator data * diagonalOperator data - diagonalOperator data * rotationOperator data =
      (2 : ℂ) • symmetricOperator data := by
  unfold rotationOperator diagonalOperator
  rw [directionalOperator_commutator, rotation_diagonal_commutator, directionalOperator_real_smul]
  norm_num [symmetricOperator]

theorem rotation_symmetric (data : CuspidalRepresentation) :
    rotationOperator data * symmetricOperator data - symmetricOperator data * rotationOperator data =
      (-2 : ℂ) • diagonalOperator data := by
  unfold rotationOperator symmetricOperator
  rw [directionalOperator_commutator, rotation_symmetric_commutator, directionalOperator_real_smul]
  norm_num [diagonalOperator]

theorem diagonal_symmetric (data : CuspidalRepresentation) :
    diagonalOperator data * symmetricOperator data - symmetricOperator data * diagonalOperator data =
      (-2 : ℂ) • rotationOperator data := by
  unfold diagonalOperator symmetricOperator
  rw [directionalOperator_commutator, diagonal_symmetric_commutator, directionalOperator_real_smul]
  norm_num [rotationOperator]

theorem rotation_raising (data : CuspidalRepresentation) :
    rotationOperator data * raising data - raising data * rotationOperator data =
      (2 * Complex.I) • raising data := by
  calc
    _ = (rotationOperator data * diagonalOperator data - diagonalOperator data * rotationOperator data) -
        Complex.I • (rotationOperator data * symmetricOperator data - symmetricOperator data * rotationOperator data) := by
      simp only [raising, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = _ := by
      rw [rotation_diagonal, rotation_symmetric]
      simp only [raising, smul_sub, smul_smul, mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
      module

theorem rotation_lowering (data : CuspidalRepresentation) :
    rotationOperator data * lowering data - lowering data * rotationOperator data =
      (-2 * Complex.I) • lowering data := by
  calc
    _ = (rotationOperator data * diagonalOperator data - diagonalOperator data * rotationOperator data) +
        Complex.I • (rotationOperator data * symmetricOperator data - symmetricOperator data * rotationOperator data) := by
      simp only [lowering, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = _ := by
      rw [rotation_diagonal, rotation_symmetric]
      simp only [lowering, smul_add, smul_smul, mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
      module

theorem lowering_raising (data : CuspidalRepresentation) :
    lowering data * raising data - raising data * lowering data =
      (4 * Complex.I) • rotationOperator data := by
  calc
    _ = (-2 * Complex.I) •
        (diagonalOperator data * symmetricOperator data - symmetricOperator data * diagonalOperator data) := by
      simp only [lowering, raising, add_mul, sub_mul, mul_add, mul_sub,
        smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
      module
    _ = _ := by
      rw [diagonal_symmetric, smul_smul]
      congr 1
      ring

theorem rotationDerivative_eq (data : CuspidalRepresentation) :
    rotationDerivative data = (2 * Real.pi : ℂ) • rotationOperator data := by
  unfold rotationDerivative
  rw [generator_eq, directionalOperator_real_smul]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, rotationOperator]

theorem rotation_eigen_iff (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ) :
    rotationOperator data vector = (Complex.I * index) • vector ↔
      ∀ parameter : Parameter, data.π (atInfinity (rotation parameter)) vector.val =
        fourier index parameter • vector.val := by
  rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationInfinitesimal.derivative_eigen_iff, rotationDerivative_eq]
  change _ ↔ (2 * Real.pi : ℂ) • rotationOperator data vector = frequency index • vector
  have nonzero : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have scalarEquality : frequency index = (2 * Real.pi : ℂ) * (Complex.I * index) := by
    unfold frequency
    ring
  rw [scalarEquality]
  rw [mul_smul (2 * Real.pi : ℂ) (Complex.I * (index : ℂ)) vector]
  exact (smul_right_inj (M := data.smooth) (r := (2 * Real.pi : ℂ)) nonzero).symm

theorem raising_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) :
    rotationOperator data (raising data vector) = (Complex.I * (index + 2 : ℤ)) • raising data vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (rotation_raising data)
  change rotationOperator data (raising data vector) - raising data (rotationOperator data vector) =
    (2 * Complex.I) • raising data vector at equality
  rw [eigen, map_smul] at equality
  rw [sub_eq_iff_eq_add] at equality
  rw [equality]
  push_cast
  module

theorem lowering_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) :
    rotationOperator data (lowering data vector) = (Complex.I * (index - 2 : ℤ)) • lowering data vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (rotation_lowering data)
  change rotationOperator data (lowering data vector) - lowering data (rotationOperator data vector) =
    (-2 * Complex.I) • lowering data vector at equality
  rw [eigen, map_smul] at equality
  rw [sub_eq_iff_eq_add] at equality
  rw [equality]
  push_cast
  module

theorem raising_preserves_fixed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (fixed : vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    (raising data vector).val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level := by
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).sub_mem
    (directionalOperator_preserves_fixed data level diagonalMatrix vector fixed)
    ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).smul_mem Complex.I
      (directionalOperator_preserves_fixed data level symmetricMatrix vector fixed))

theorem lowering_preserves_fixed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (fixed : vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    (lowering data vector).val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level := by
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).add_mem
    (directionalOperator_preserves_fixed data level diagonalMatrix vector fixed)
    ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).smul_mem Complex.I
      (directionalOperator_preserves_fixed data level symmetricMatrix vector fixed))

theorem raising_mem_fixedMode (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (index : ℤ) (membership : vector ∈ FiniteRotationTypes.fixedMode data level index) :
    raising data vector ∈ FiniteRotationTypes.fixedMode data level (index + 2) := by
  rw [FiniteRotationTypes.mem_fixedMode_iff] at membership ⊢
  exact ⟨raising_preserves_fixed data level vector membership.1,
    (rotation_eigen_iff data _ _).mp (raising_eigen data vector index
      ((rotation_eigen_iff data vector index).mpr membership.2))⟩

theorem lowering_mem_fixedMode (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (index : ℤ) (membership : vector ∈ FiniteRotationTypes.fixedMode data level index) :
    lowering data vector ∈ FiniteRotationTypes.fixedMode data level (index - 2) := by
  rw [FiniteRotationTypes.mem_fixedMode_iff] at membership ⊢
  exact ⟨lowering_preserves_fixed data level vector membership.1,
    (rotation_eigen_iff data _ _).mp (lowering_eigen data vector index
      ((rotation_eigen_iff data vector index).mpr membership.2))⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators
