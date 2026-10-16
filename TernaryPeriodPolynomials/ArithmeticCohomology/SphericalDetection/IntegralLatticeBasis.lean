module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.AdelicApproximation
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section


open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A full integer lattice has an integer basis matrix with nonzero determinant. -/
theorem integer_lattice_exists_basis_matrix {index : Type*} [Fintype index] [DecidableEq index]
    (lattice : Submodule ℤ (index → ℤ)) (denominator : ℤ) (nonzero : denominator ≠ 0)
    (contains : ∀ vector : index → ℤ, denominator • vector ∈ lattice) :
    ∃ matrix : Matrix index index ℤ, matrix.det ≠ 0 ∧
      ∀ vector, vector ∈ lattice ↔ ∃ coordinates : index → ℤ, matrix.mulVec coordinates = vector := by
  have rank_eq : Module.finrank ℤ lattice = Module.finrank ℤ (index → ℤ) := by
    apply le_antisymm lattice.finrank_le
    have lower := LinearMap.finrank_le_of_isSMulRegular (⊤ : Submodule ℤ (index → ℤ)) lattice
      (IsSMulRegular.of_ne_zero nonzero) (fun vector _ => contains vector)
    simpa only [finrank_top] using lower
  let basis := lattice.smithNormalFormBotBasis (Pi.basisFun ℤ index) rank_eq
  let matrix : Matrix index index ℤ := fun row column => (basis column).val row
  have spanning (vector : lattice) : matrix.mulVec (fun column => basis.repr vector column) = vector.val := by
    have equality := congrArg Subtype.val (basis.sum_repr vector)
    funext row
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, matrix, Matrix.mulVec, dotProduct, mul_comm] using congrFun equality row
  let coordinates : Matrix index index ℤ := fun row column =>
    basis.repr ⟨denominator • Pi.single column 1, contains (Pi.single column 1)⟩ row
  have product : matrix * coordinates = denominator • (1 : Matrix index index ℤ) := by
    ext row column
    change (∑ position, matrix row position * coordinates position column) =
      denominator * (if row = column then 1 else 0)
    have equality := congrFun (spanning ⟨denominator • Pi.single column 1, contains (Pi.single column 1)⟩) row
    simpa only [coordinates, Matrix.mulVec, dotProduct,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul] using equality
  have determinant_nonzero : matrix.det ≠ 0 := by
    have determinant := congrArg Matrix.det product
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at determinant
    intro zero
    rw [zero, zero_mul] at determinant
    exact pow_ne_zero _ nonzero determinant.symm
  refine ⟨matrix, determinant_nonzero, fun vector => ?_⟩
  constructor
  · intro member
    exact ⟨fun column => basis.repr ⟨vector, member⟩ column, spanning ⟨vector, member⟩⟩
  · rintro ⟨coordinates, rfl⟩
    have equality : matrix.mulVec coordinates = ∑ column, coordinates column • (basis column).val := by
      funext row
      simp only [Matrix.mulVec, dotProduct, matrix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [equality]
    exact lattice.sum_mem (fun column _ => lattice.smul_mem _ (basis column).property)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
