module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Siegel.ChartFunctions

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AbsoluteTheta

def tailTerm (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (matrix : Rectangular ℚ) : ℂ :=
  if matrix = 0 then 0 else RectangularTheta.matrixTerm test point binary matrix

def tail (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℝ :=
  ∑' matrix, ‖tailTerm test point binary matrix‖

theorem tail_nonnegative (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    0 ≤ tail test point binary := tsum_nonneg (fun _ => norm_nonneg _)

theorem tailTerm_chart (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane)
    (right : BinaryRealGL) (matrix : Rectangular ℚ) :
    tailTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point (AdelicSiegelCover.chart integral scale argument right) matrix =
      RationalDistortionDecay.tailTerm realTest
        (FiniteParameterThetaDecay.pullback finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral))
        (realTransform (realGroup point) (unit argument argument.im_pos * right)).toContinuousLinearMap scale.val matrix := by
  classical
  unfold tailTerm RationalDistortionDecay.tailTerm
  split_ifs
  · rfl
  · exact SiegelChartFunctions.matrixTerm_chart realTest finiteTest point integral scale argument right matrix

theorem tail_chart (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point (AdelicSiegelCover.chart integral scale argument right) =
      UniformAbsoluteTheta.absoluteTail realTest finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)
        (realTransform (realGroup point) (unit argument argument.im_pos * right)).toContinuousLinearMap scale.val := by
  unfold tail UniformAbsoluteTheta.absoluteTail
  apply tsum_congr
  exact fun matrix => congrArg norm (tailTerm_chart realTest finiteTest point integral scale argument right matrix)

theorem rightEquiv_zero (rational : BinaryRationalGL) : RectangularTheta.rightEquiv rational 0 = 0 := by
  change (0 : Rectangular ℚ) * rational.val = 0
  exact Matrix.zero_mul _

theorem tailTerm_rational_binary (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) (matrix : Rectangular ℚ) :
    tailTerm test point (GeneralLinearGroup.map rationalAdele rational * binary) matrix =
      tailTerm test point binary (RectangularTheta.rightEquiv rational matrix) := by
  classical
  have nonzero : RectangularTheta.rightEquiv rational matrix = 0 ↔ matrix = 0 := by
    conv_lhs => rw [← rightEquiv_zero rational]
    exact (RectangularTheta.rightEquiv rational).injective.eq_iff
  simp only [tailTerm, nonzero, RectangularTheta.matrixTerm_rational_binary]

theorem tail_rational_binary (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) :
    tail test point (GeneralLinearGroup.map rationalAdele rational * binary) = tail test point binary := by
  simp only [tail, tailTerm_rational_binary]
  exact (RectangularTheta.rightEquiv rational).tsum_eq (fun matrix => ‖tailTerm test point binary matrix‖)

theorem term_continuous (test : Rectangular Adeles → ℂ) (continuousTest : Continuous test)
    (point : AdelicGL) (matrix : Rectangular ℚ) : Continuous (tailTerm test point · matrix) := by
  classical
  by_cases zero : matrix = 0
  · simp only [tailTerm, zero, ite_true]
    exact continuous_const
  · simp only [tailTerm, ite_eq_right zero, RectangularTheta.matrixTerm]
    exact continuousTest.comp (continuous_const.matrix_mul
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) Adeles)))

theorem tail_measurable (test : Rectangular Adeles → ℂ) (continuousTest : Continuous test) (point : AdelicGL) :
    Measurable (tail test point) := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  exact Measurable.tsum (fun matrix => (term_continuous test continuousTest point matrix).norm.measurable)

theorem summable (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun matrix => ‖tailTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary matrix‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun matrix => ?_)
    (AdelicSchwartzTheta.summable_norm realTest finiteTest finiteContinuous finiteSupport point binary)
  classical
  by_cases zero : matrix = 0
  · simp only [tailTerm, zero, ite_true, norm_zero]
    exact norm_nonneg _
  · simp only [tailTerm, ite_eq_right zero, le_refl]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AbsoluteTheta
