module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePlaneCoordinateKernel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFirstProjection_levi (real : ℝ × ℝ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (pivot : (goodLineLeviRealInput matrix real).2 ≠ 0) :
    realPlaneFirstProjection (standardGoodLineRealArgument real *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)) =
      SemidirectProduct.inr
          (binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) matrix * binaryPivotSwap) *
        realPlaneFirstProjection (standardGoodLineRealArgument (goodLineLeviRealInput matrix real)) := by
  rw [standardGoodLineRealArgument_levi, goodLineConjugateRealLevi, ← realPlaneMatrix_inr]
  apply realPlaneFirstProjection_equivariant
  rw [standardGoodLineRealArgument_val]
  exact pivot

theorem goodLineFirstProjection_mixed_vertices_left (real : ℝ × ℝ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice)
    (pivot : (goodLineLeviRealInput matrix real).2 ≠ 0)
    (shift_pivot : (goodLineLeviRealInput matrix (goodLineRadicalRealShift radical real)).2 ≠ 0) :
    let levi : RealPlaneGroup := SemidirectProduct.inr
      (binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) matrix * binaryPivotSwap)
    (fun index => realPlaneFirstProjection (standardGoodLineRealArgument real *
      goodLineRealVertices (goodLineLeviSection matrix,
        goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)) index)) =
      ![realPlaneFirstProjection (standardGoodLineRealArgument real),
        levi * realPlaneFirstProjection (standardGoodLineRealArgument (goodLineLeviRealInput matrix real)),
        levi * realPlaneFirstProjection (standardGoodLineRealArgument
          (goodLineLeviRealInput matrix (goodLineRadicalRealShift radical real)))] := by
  funext index
  fin_cases index
  · change realPlaneFirstProjection (standardGoodLineRealArgument real *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) 1) = _
    rw [map_one, mul_one]
    rfl
  · exact goodLineFirstProjection_levi real matrix pivot
  · change realPlaneFirstProjection (standardGoodLineRealArgument real *
        GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (arithmeticLevi matrix * lowerRadicalLattice (lowerLeviLatticeInput matrix radical))) = _
    rw [← lowerLeviLatticeInput_conjugation, map_mul, ← mul_assoc, standardGoodLineRealArgument_radical]
    exact goodLineFirstProjection_levi _ matrix shift_pivot

theorem goodLineFirstProjection_mixed_vertices_right (real : ℝ × ℝ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice)
    (shift_pivot : (goodLineLeviRealInput matrix (goodLineRadicalRealShift radical real)).2 ≠ 0) :
    let levi : RealPlaneGroup := SemidirectProduct.inr
      (binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) matrix * binaryPivotSwap)
    (fun index => realPlaneFirstProjection (standardGoodLineRealArgument real *
      goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix) index)) =
      ![realPlaneFirstProjection (standardGoodLineRealArgument real),
        realPlaneFirstProjection (standardGoodLineRealArgument (goodLineRadicalRealShift radical real)),
        levi * realPlaneFirstProjection (standardGoodLineRealArgument
          (goodLineLeviRealInput matrix (goodLineRadicalRealShift radical real)))] := by
  funext index
  fin_cases index
  · change realPlaneFirstProjection (standardGoodLineRealArgument real *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) 1) = _
    rw [map_one, mul_one]
    rfl
  · change realPlaneFirstProjection (standardGoodLineRealArgument real *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)) = _
    rw [standardGoodLineRealArgument_radical]
    rfl
  · change realPlaneFirstProjection (standardGoodLineRealArgument real *
        GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (lowerRadicalLattice radical * arithmeticLevi matrix)) = _
    rw [map_mul, ← mul_assoc, standardGoodLineRealArgument_radical]
    exact goodLineFirstProjection_levi _ matrix shift_pivot

end TernaryPeriodPolynomials.SphericalDetection.Helpers
