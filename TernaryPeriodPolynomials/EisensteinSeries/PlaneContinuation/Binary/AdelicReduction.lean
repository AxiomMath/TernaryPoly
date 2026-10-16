module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.StrongApproximation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ClassicalComponents

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryAdelicReduction

theorem rational_decomposition (matrix : BinaryRationalGL) :
    GeneralLinearGroup.map rationalAdele matrix =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix) *
        atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix) :=
  CasimirIrreducibility.binaryAdelic_decomposition (GeneralLinearGroup.map rationalAdele matrix)

theorem exists_rational_integral_real (matrix : BinaryAdelicGL) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL, ∃ realMatrix : BinaryRealGL,
      matrix = GeneralLinearGroup.map rationalAdele rational *
        (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity realMatrix) := by
  let realPart := GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) matrix
  let finitePart := GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) matrix
  obtain ⟨rational, integral, factorization⟩ := BinaryStrongApproximation.exists_rational_integral finitePart
  let rationalReal := GeneralLinearGroup.map (algebraMap ℚ ℝ) rational
  refine ⟨rational, integral, rationalReal⁻¹ * realPart, ?_⟩
  rw [rational_decomposition]
  calc
    matrix = atInfinity realPart * atFinite finitePart :=
      CasimirIrreducibility.binaryAdelic_decomposition matrix
    _ = atFinite finitePart * atInfinity realPart := (atFinite_atInfinity_commute finitePart realPart).symm
    _ = atFinite finitePart * (atInfinity rationalReal * atInfinity (rationalReal⁻¹ * realPart)) := by
      rw [← Height.atInfinity_mul, mul_inv_cancel_left]
    _ = atInfinity rationalReal * (atFinite finitePart * atInfinity (rationalReal⁻¹ * realPart)) := by
      rw [← mul_assoc, atFinite_atInfinity_commute, mul_assoc]
    _ = _ := by
      rw [factorization, atFinite_mul]
      simp only [rationalReal, mul_assoc]

def flip {ring : Type*} [CommRing ring] : GeneralLinearGroup (Fin 2) ring :=
  BinaryStrongApproximation.diagonal 1 (-1)

theorem flip_mul_self {ring : Type*} [CommRing ring] : (flip : GeneralLinearGroup (Fin 2) ring) * flip = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [flip, BinaryStrongApproximation.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem flip_map {source target : Type*} [CommRing source] [CommRing target] (hom : source →+* target) :
    GeneralLinearGroup.map hom flip = flip := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [flip, BinaryStrongApproximation.diagonal, GeneralLinearGroup.map_apply]

theorem flip_det : (GeneralLinearGroup.det (flip : BinaryRealGL)).val = -1 := by
  simp [flip, BinaryStrongApproximation.diagonal, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem flip_adelic : GeneralLinearGroup.map rationalAdele (flip : BinaryRationalGL) =
    atInfinity (flip : BinaryRealGL) * atFinite (GeneralLinearGroup.map integralEmbedding (flip : IntegralBinaryGL)) := by
  rw [rational_decomposition, flip_map, flip_map, flip_map]

theorem positive_after_flip (matrix : BinaryRealGL) (nonpositive : ¬0 < (GeneralLinearGroup.det matrix).val) :
    0 < (GeneralLinearGroup.det (flip * matrix)).val := by
  rw [map_mul, Units.val_mul, flip_det, neg_one_mul]
  exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt nonpositive) (GeneralLinearGroup.det matrix).ne_zero)

theorem flip_cancellation (integral : IntegralBinaryGL) (realMatrix : BinaryRealGL) :
    GeneralLinearGroup.map rationalAdele (flip : BinaryRationalGL) *
        (atFinite (GeneralLinearGroup.map integralEmbedding (flip * integral)) * atInfinity (flip * realMatrix)) =
      atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity realMatrix := by
  rw [flip_adelic, map_mul, atFinite_mul, Height.atInfinity_mul]
  have finiteSquare : atFinite (GeneralLinearGroup.map integralEmbedding (flip : IntegralBinaryGL)) *
      atFinite (GeneralLinearGroup.map integralEmbedding (flip : IntegralBinaryGL)) = 1 := by
    rw [← atFinite_mul, ← map_mul, flip_mul_self, map_one, CompactAveraging.atFinite_one]
  have realSquare : atInfinity (flip : BinaryRealGL) * atInfinity (flip : BinaryRealGL) = 1 := by
    rw [← Height.atInfinity_mul, flip_mul_self, AveragingSmooth.atInfinity_one]
  calc
    _ = atInfinity (flip : BinaryRealGL) *
        (atFinite (GeneralLinearGroup.map integralEmbedding (flip : IntegralBinaryGL)) *
          atFinite (GeneralLinearGroup.map integralEmbedding (flip : IntegralBinaryGL))) *
        (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity flip) *
        atInfinity realMatrix := by group
    _ = _ := by
      rw [finiteSquare, mul_one, atFinite_atInfinity_commute, ← mul_assoc,
        realSquare, one_mul]

theorem exists_rational_integral_positive (matrix : BinaryAdelicGL) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL, ∃ realMatrix : BinaryRealGL,
      0 < (GeneralLinearGroup.det realMatrix).val ∧
      matrix = GeneralLinearGroup.map rationalAdele rational *
        (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity realMatrix) := by
  obtain ⟨rational, integral, realMatrix, equality⟩ := exists_rational_integral_real matrix
  by_cases positive : 0 < (GeneralLinearGroup.det realMatrix).val
  · exact ⟨rational, integral, realMatrix, positive, equality⟩
  · refine ⟨rational * flip, flip * integral, flip * realMatrix, positive_after_flip realMatrix positive, ?_⟩
    rw [map_mul, mul_assoc, flip_cancellation]
    exact equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryAdelicReduction
