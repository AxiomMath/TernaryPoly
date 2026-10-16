module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteWeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def planeParabolicBinaryMatrix {R : Type*} [CommRing R] (matrix : planeParabolic R) : Matrix (Fin 2) (Fin 2) R :=
  fun row column => matrix.val.val row.castSucc column.castSucc

theorem planeParabolicBinaryMatrix_one {R : Type*} [CommRing R] :
    planeParabolicBinaryMatrix (1 : planeParabolic R) = 1 := by
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem planeParabolicBinaryMatrix_mul {R : Type*} [CommRing R] (first second : planeParabolic R) :
    planeParabolicBinaryMatrix (first * second) = planeParabolicBinaryMatrix first * planeParabolicBinaryMatrix second := by
  funext row column
  change (∑ position : Fin 3, first.val.val row.castSucc position * second.val.val position column.castSucc) =
    ∑ position : Fin 2, first.val.val row.castSucc position.castSucc * second.val.val position.castSucc column.castSucc
  fin_cases row <;> fin_cases column <;>
    simp [Fin.sum_univ_three, Fin.sum_univ_two, second.property.1, second.property.2]

def planeParabolicBinary {R : Type*} [CommRing R] : planeParabolic R →* GeneralLinearGroup (Fin 2) R where
  toFun matrix :=
    ⟨planeParabolicBinaryMatrix matrix, planeParabolicBinaryMatrix matrix⁻¹, by
      rw [← planeParabolicBinaryMatrix_mul, mul_inv_cancel, planeParabolicBinaryMatrix_one], by
      rw [← planeParabolicBinaryMatrix_mul, inv_mul_cancel, planeParabolicBinaryMatrix_one]⟩
  map_one' := Units.ext planeParabolicBinaryMatrix_one
  map_mul' first second := Units.ext (planeParabolicBinaryMatrix_mul first second)

theorem planeParabolicBinary_apply {R : Type*} [CommRing R] (matrix : planeParabolic R) (row column : Fin 2) :
    (planeParabolicBinary matrix).val row column = matrix.val.val row.castSucc column.castSucc := rfl

def planeInductionParabolic {R : Type*} [CommRing R]
    (first second : R) (scalar : Rˣ) (block : GeneralLinearGroup (Fin 2) R) : planeParabolic R :=
  ⟨planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1),
    (planeParabolic R).mul_mem ⟨rfl, rfl⟩
      ((planeParabolic R).mul_mem (planeLevi_mem 1 scalar) (planeLevi_mem block 1))⟩

theorem planeParabolicBinary_induction {R : Type*} [CommRing R]
    (first second : R) (scalar : Rˣ) (block : GeneralLinearGroup (Fin 2) R) :
    planeParabolicBinary (planeInductionParabolic first second scalar block) = block := by
  apply Units.ext
  funext row column
  exact planeInduction_block_entry first second scalar block row column

theorem planeParabolicBinary_finite_integral (matrix : planeParabolic FiniteAdeles)
    (integral : matrix.val ∈ finiteIntegralGLLevel 3) : planeParabolicBinary matrix ∈ finiteIntegralGLLevel 2 := by
  have entries := (finiteIntegralGLLevel_mem_iff matrix.val).mp integral
  apply (finiteIntegralGLLevel_mem_iff _).mpr
  constructor
  · intro row column
    exact entries.1 row.castSucc column.castSucc
  · intro row column
    exact entries.2 row.castSucc column.castSucc

end TernaryPeriodPolynomials.SphericalDetection.Helpers
