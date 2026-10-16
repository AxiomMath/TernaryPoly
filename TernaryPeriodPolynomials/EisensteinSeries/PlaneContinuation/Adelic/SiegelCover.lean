module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.SiegelSet

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicSiegelCover

theorem arithmetic_shift (rational : SpecialLinearGroup (Fin 2) ℤ)
    (integral : IntegralBinaryGL) (realPoint : BinaryRealGL) :
    atFinite (GeneralLinearGroup.map integralEmbedding integral) *
        atInfinity ((SpecialLinearGroup.mapGL ℝ rational)⁻¹ * realPoint) =
      GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ rational)⁻¹ *
        (atFinite (GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles rational * integral)) *
          atInfinity realPoint) := by
  have decomposition : GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ rational) =
      atFinite (GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles rational)) *
        atInfinity (SpecialLinearGroup.mapGL ℝ rational) := by
    rw [ArithmeticModularity.rational_decomposition, atFinite_atInfinity_commute]
  rw [map_inv, decomposition, _root_.mul_inv_rev, map_mul, atFinite_mul,
    Height.atInfinity_mul, AveragingSmooth.atInfinity_inv]
  have commute := atFinite_atInfinity_commute
    (GeneralLinearGroup.map integralEmbedding integral) (SpecialLinearGroup.mapGL ℝ rational)⁻¹
  rw [AveragingSmooth.atInfinity_inv] at commute
  rw [← mul_assoc, commute]
  group

def chart (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) : BinaryAdelicGL :=
  atFinite (GeneralLinearGroup.map integralEmbedding integral) *
    atInfinity (GeneralLinearGroup.scalar (Fin 2) scale * (unit argument argument.im_pos * right))

def region : Set BinaryAdelicGL :=
  {point | ∃ integral : IntegralBinaryGL, ∃ scale : ℝˣ, 0 < scale.val ∧
    ∃ argument : UpperHalfPlane, 1 ≤ argument.im ∧ |argument.re| ≤ 1 ∧
      ∃ right ∈ RealSiegelSet.rightSet, point = chart integral scale argument right}

theorem decomposition (point : BinaryAdelicGL) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL, ∃ scale : ℝˣ, 0 < scale.val ∧
      ∃ argument : UpperHalfPlane, 1 ≤ argument.im ∧ |argument.re| ≤ 1 ∧ ∃ right ∈ RealSiegelSet.rightSet,
        point = GeneralLinearGroup.map rationalAdele rational * chart integral scale argument right := by
  obtain ⟨rational, integral, realPoint, positive, equality⟩ :=
    BinaryAdelicReduction.exists_rational_integral_positive point
  obtain ⟨integer, scale, scalePositive, argument, height, horizontal, right, rightMem, realEquality⟩ :=
    RealSiegelSet.decomposition realPoint positive
  refine ⟨rational * (SpecialLinearGroup.mapGL ℚ integer)⁻¹,
    SpecialLinearGroup.mapGL IntegralAdeles integer * integral, scale, scalePositive,
    argument, height, horizontal, right, rightMem, ?_⟩
  rw [equality, realEquality, arithmetic_shift]
  simp only [map_mul, chart, mul_assoc]

theorem covers (point : BinaryAdelicGL) :
    ∃ rational : BinaryRationalGL, GeneralLinearGroup.map rationalAdele rational * point ∈ region := by
  obtain ⟨rational, integral, scale, positive, argument, height, horizontal, right, rightMem, equality⟩ := decomposition point
  refine ⟨rational⁻¹, integral, scale, positive, argument, height, horizontal, right, rightMem, ?_⟩
  rw [equality, map_inv, inv_mul_cancel_left]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicSiegelCover
