module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.FiniteDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.LowestIntegralAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def binaryRealComponent : BinaryAdelicGL →* BinaryRealGL :=
  GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)

noncomputable def binaryFiniteComponent : BinaryAdelicGL →* BinaryFiniteGL :=
  GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)

theorem binaryAdelic_eq_of_components {first second : BinaryAdelicGL}
    (real_equal : binaryRealComponent first = binaryRealComponent second)
    (finite_equal : binaryFiniteComponent first = binaryFiniteComponent second) : first = second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · exact congrArg (fun matrix : BinaryRealGL => matrix.val row column) real_equal
  · exact congrArg (fun matrix : BinaryFiniteGL => matrix.val row column) finite_equal

theorem binaryRealComponent_atInfinity (matrix : BinaryRealGL) :
    binaryRealComponent (atInfinity matrix) = matrix := by apply Units.ext; rfl

theorem binaryRealComponent_atFinite (matrix : BinaryFiniteGL) :
    binaryRealComponent (atFinite matrix) = 1 := by apply Units.ext; rfl

theorem binaryFiniteComponent_atInfinity (matrix : BinaryRealGL) :
    binaryFiniteComponent (atInfinity matrix) = 1 := by apply Units.ext; rfl

theorem binaryFiniteComponent_atFinite (matrix : BinaryFiniteGL) :
    binaryFiniteComponent (atFinite matrix) = matrix := by apply Units.ext; rfl

theorem binaryRealComponent_rational (matrix : GeneralLinearGroup (Fin 2) ℚ) :
    binaryRealComponent (GeneralLinearGroup.map rationalAdele matrix) =
      GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix := by apply Units.ext; rfl

theorem binaryFiniteComponent_rational (matrix : GeneralLinearGroup (Fin 2) ℚ) :
    binaryFiniteComponent (GeneralLinearGroup.map rationalAdele matrix) =
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix := by apply Units.ext; rfl

theorem binary_rational_adelic_factor (matrix : GeneralLinearGroup (Fin 2) ℚ) :
    GeneralLinearGroup.map rationalAdele matrix =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix) *
        atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix) := by
  apply binaryAdelic_eq_of_components
  · rw [map_mul, binaryRealComponent_atInfinity, binaryRealComponent_atFinite,
      mul_one, binaryRealComponent_rational]
  · rw [map_mul, binaryFiniteComponent_atInfinity, binaryFiniteComponent_atFinite,
      one_mul, binaryFiniteComponent_rational]

theorem binary_adelic_rational_real_integral (matrix : BinaryAdelicGL) :
    ∃ rational : GeneralLinearGroup (Fin 2) ℚ, ∃ realMatrix : BinaryRealGL,
      ∃ integralMatrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
        matrix = GeneralLinearGroup.map rationalAdele rational * atInfinity realMatrix *
          atFinite (GeneralLinearGroup.map integralEmbedding integralMatrix) := by
  obtain ⟨rational, integralMatrix, decomposition⟩ :=
    binary_finite_rational_integral_decomposition (binaryFiniteComponent matrix)
  refine ⟨rational, (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)⁻¹ * binaryRealComponent matrix,
    integralMatrix, ?_⟩
  apply binaryAdelic_eq_of_components
  · rw [map_mul, map_mul, binaryRealComponent_rational, binaryRealComponent_atInfinity,
      binaryRealComponent_atFinite, mul_one, mul_inv_cancel_left]
  · rw [map_mul, map_mul, binaryFiniteComponent_rational, binaryFiniteComponent_atInfinity,
      binaryFiniteComponent_atFinite, mul_one]
    exact decomposition

def binarySignMatrix (R : Type*) [CommRing R] : GeneralLinearGroup (Fin 2) R :=
  binaryUnitDiagonal (-1) 1

theorem binarySignMatrix_square (R : Type*) [CommRing R] :
    binarySignMatrix R * binarySignMatrix R = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [binarySignMatrix, binaryUnitDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem map_binarySignMatrix {R S : Type*} [CommRing R] [CommRing S] (ringMap : R →+* S) :
    GeneralLinearGroup.map ringMap (binarySignMatrix R) = binarySignMatrix S := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, binarySignMatrix, binaryUnitDiagonal]

theorem binarySignMatrix_det (R : Type*) [CommRing R] :
    (GeneralLinearGroup.det (binarySignMatrix R)).val = -1 := by
  simp [GeneralLinearGroup.val_det_apply, binarySignMatrix, binaryUnitDiagonal, Matrix.det_fin_two]

theorem binary_adelic_rational_positive_integral (matrix : BinaryAdelicGL) :
    ∃ rational : GeneralLinearGroup (Fin 2) ℚ, ∃ realMatrix : BinaryRealGL,
      ∃ integralMatrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
        0 < (GeneralLinearGroup.det realMatrix : ℝ) ∧
        matrix = GeneralLinearGroup.map rationalAdele rational * atInfinity realMatrix *
          atFinite (GeneralLinearGroup.map integralEmbedding integralMatrix) := by
  obtain ⟨rational, realMatrix, integralMatrix, decomposition⟩ :=
    binary_adelic_rational_real_integral matrix
  by_cases positive : 0 < (GeneralLinearGroup.det realMatrix : ℝ)
  · exact ⟨rational, realMatrix, integralMatrix, positive, decomposition⟩
  have negative : (GeneralLinearGroup.det realMatrix : ℝ) < 0 :=
    lt_of_le_of_ne (le_of_not_gt positive) (GeneralLinearGroup.det realMatrix).ne_zero
  refine ⟨rational * binarySignMatrix ℚ, binarySignMatrix ℝ * realMatrix,
    binarySignMatrix IntegralAdeles * integralMatrix, ?_, ?_⟩
  · rw [map_mul, Units.val_mul, binarySignMatrix_det]
    linarith
  · apply binaryAdelic_eq_of_components
    · rw [decomposition]
      simp only [map_mul, binaryRealComponent_rational, binaryRealComponent_atInfinity,
        binaryRealComponent_atFinite, mul_one, map_binarySignMatrix]
      simp only [binaryRealComponent, map_binarySignMatrix]
      rw [mul_assoc, ← mul_assoc (binarySignMatrix ℝ), binarySignMatrix_square, one_mul]
    · rw [decomposition]
      simp only [map_mul, binaryFiniteComponent_rational, binaryFiniteComponent_atInfinity,
        binaryFiniteComponent_atFinite, mul_one, map_binarySignMatrix]
      simp only [binaryFiniteComponent, map_binarySignMatrix]
      rw [mul_assoc, ← mul_assoc (binarySignMatrix FiniteAdeles), binarySignMatrix_square, one_mul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
