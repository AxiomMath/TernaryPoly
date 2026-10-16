module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Theta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularFrames

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularCuspidality

theorem realize_stabilizer (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (basis : BinaryRationalGL) (parameter : Adeles) (binary : BinaryAdelicGL) :
    cusp.realize vector (stabilizer basis parameter * binary) =
      cusp.realize vector (binaryUnipotent parameter * ((GeneralLinearGroup.map rationalAdele basis)⁻¹ * binary)) := by
  simp only [stabilizer, mul_assoc, cusp.leftRational]

theorem stabilizer_integrable (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (basis : BinaryRationalGL) (binary : BinaryAdelicGL) :
    IntegrableOn (fun parameter => cusp.realize vector (stabilizer basis parameter * binary))
      additiveDomain adeleMeasure := by
  simpa only [realize_stabilizer] using
    (cusp.cuspidal vector ((GeneralLinearGroup.map rationalAdele basis)⁻¹ * binary)).1

theorem stabilizer_integral_zero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (basis : BinaryRationalGL) (binary : BinaryAdelicGL) :
    (∫ parameter in additiveDomain,
      cusp.realize vector (stabilizer basis parameter * binary) ∂adeleMeasure) = 0 := by
  simpa only [realize_stabilizer] using
    (cusp.cuspidal vector ((GeneralLinearGroup.map rationalAdele basis)⁻¹ * binary)).2

noncomputable def weightedMatrixTerm (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (test : Rectangular Adeles → ℂ) (character : Adelesˣ →* ℂ) (point : AdelicGL)
    (matrix : Rectangular ℚ) (binary : BinaryAdelicGL) : ℂ :=
  matrixTerm test point binary matrix * character (GeneralLinearGroup.det binary) * cusp.realize vector binary

theorem weightedMatrixTerm_stabilizer (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (test : Rectangular Adeles → ℂ) (character : Adelesˣ →* ℂ) (point : AdelicGL)
    (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) (parameter : Adeles) :
    weightedMatrixTerm cusp vector test character point matrix (stabilizer basis parameter * binary) =
      (matrixTerm test point binary matrix * character (GeneralLinearGroup.det binary)) *
        cusp.realize vector (stabilizer basis parameter * binary) := by
  simp only [weightedMatrixTerm, matrixTerm_stabilizer test point binary matrix basis zeroFirst,
    map_mul, stabilizer_det, one_mul]

theorem weighted_stabilizer_integrable (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (test : Rectangular Adeles → ℂ) (character : Adelesˣ →* ℂ) (point : AdelicGL)
    (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) :
    IntegrableOn (fun parameter => weightedMatrixTerm cusp vector test character point matrix
      (stabilizer basis parameter * binary)) additiveDomain adeleMeasure := by
  simp only [weightedMatrixTerm_stabilizer cusp vector test character point matrix basis zeroFirst]
  exact (stabilizer_integrable cusp vector basis binary).const_mul _

theorem weighted_stabilizer_integral_zero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (test : Rectangular Adeles → ℂ) (character : Adelesˣ →* ℂ) (point : AdelicGL)
    (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (binary : BinaryAdelicGL) :
    (∫ parameter in additiveDomain, weightedMatrixTerm cusp vector test character point matrix
      (stabilizer basis parameter * binary) ∂adeleMeasure) = 0 := by
  simp only [weightedMatrixTerm_stabilizer cusp vector test character point matrix basis zeroFirst,
    integral_const_mul, stabilizer_integral_zero, mul_zero]

theorem singular_average_zero (matrix : Rectangular ℚ) (singular : ¬ FullRank matrix) :
    ∃ basis : BinaryRationalGL, ∀ (cusp : CuspidalRepresentation) (vector : cusp.smooth)
      (test : Rectangular Adeles → ℂ) (character : Adelesˣ →* ℂ) (point : AdelicGL) (binary : BinaryAdelicGL),
      IntegrableOn (fun parameter => weightedMatrixTerm cusp vector test character point matrix
        (stabilizer basis parameter * binary)) additiveDomain adeleMeasure ∧
      (∫ parameter in additiveDomain, weightedMatrixTerm cusp vector test character point matrix
        (stabilizer basis parameter * binary) ∂adeleMeasure) = 0 := by
  obtain ⟨basis, zeroFirst⟩ := exists_zero_first_column matrix singular
  exact ⟨basis, fun cusp vector test character point binary =>
    ⟨weighted_stabilizer_integrable cusp vector test character point matrix basis zeroFirst binary,
      weighted_stabilizer_integral_zero cusp vector test character point matrix basis zeroFirst binary⟩⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularCuspidality
