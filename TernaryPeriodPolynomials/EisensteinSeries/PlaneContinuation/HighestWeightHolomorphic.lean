module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UpperTriangularChart
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators
open scoped Manifold

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic

noncomputable def normalization (weight : ℤ) (argument : ℂ) : ℂ :=
  Complex.exp (-(weight : ℂ) / 2 * (Real.log argument.im : ℂ))

theorem normalization_hasFDerivAt (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) :
    HasFDerivAt (normalization weight)
      (normalization weight argument • ((-(weight : ℂ) / 2) •
        (Complex.ofRealCLM.comp (argument.im⁻¹ • Complex.imCLM)))) argument := by
  have logDerivative := Complex.imCLM.hasFDerivAt.log (ne_of_gt positive)
  have castDerivative := Complex.ofRealCLM.hasFDerivAt.comp argument logDerivative
  exact (castDerivative.const_mul (-(weight : ℂ) / 2)).cexp

theorem normalization_fderiv (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) (tangent : ℂ) :
    fderiv ℝ (normalization weight) argument tangent =
      normalization weight argument * (-(weight : ℂ) / 2) * (argument.im⁻¹ : ℝ) * (tangent.im : ℂ) := by
  rw [(normalization_hasFDerivAt weight argument positive).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, Complex.ofRealCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem normalization_fderiv_one (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) :
    fderiv ℝ (normalization weight) argument 1 = 0 := by
  rw [normalization_fderiv weight argument positive]
  simp

theorem normalization_fderiv_I (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) :
    fderiv ℝ (normalization weight) argument Complex.I =
      -((weight : ℂ) / (2 * (argument.im : ℂ))) * normalization weight argument := by
  rw [normalization_fderiv weight argument positive]
  simp only [Complex.I_im, Complex.ofReal_one, Complex.ofReal_inv, mul_one]
  ring

theorem raw_cauchyRiemann {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (weight : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (highest : raising data.cusp vector = 0) (argument : ℂ) (positive : 0 < argument.im) :
    fderiv ℝ (raw data.cusp point vector) argument Complex.I =
      Complex.I * fderiv ℝ (raw data.cusp point vector) argument 1 +
        (weight : ℂ) / (2 * (argument.im : ℂ)) * raw data.cusp point vector argument := by
  have diagonal : diagonalOperator data.cusp vector = Complex.I • symmetricOperator data.cusp vector :=
    sub_eq_zero.mp highest
  rw [raw_fderiv_I data point vector argument positive, raw_fderiv_one data point vector argument positive,
    diagonal, eigen, map_smul, map_sub, map_smul, raw_eq data.cusp point vector argument positive]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Int.cast_neg]
  push_cast
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

noncomputable def function (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (weight : ℤ) (argument : ℂ) : ℂ :=
  normalization weight argument * raw data point vector argument

theorem function_fderiv (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) (tangent : ℂ) :
    fderiv ℝ (function data point vector weight) argument tangent =
      normalization weight argument * fderiv ℝ (raw data point vector) argument tangent +
        raw data point vector argument * fderiv ℝ (normalization weight) argument tangent := by
  have normalizationDerivative := (normalization_hasFDerivAt weight argument positive).differentiableAt.hasFDerivAt
  have rawDerivative := (raw_hasFDerivAt data point vector argument positive).differentiableAt.hasFDerivAt
  have equality := congrArg (fun linear : ℂ →L[ℝ] ℂ => linear tangent) (normalizationDerivative.mul rawDerivative).fderiv
  exact equality

/-- Highest-weight vectors give holomorphic scalar functions on the upper half-plane. -/
theorem differentiableAt {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (weight : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (highest : raising data.cusp vector = 0) (argument : ℂ) (positive : 0 < argument.im) :
    DifferentiableAt ℂ (function data.cusp point vector weight) argument := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(normalization_hasFDerivAt weight argument positive).differentiableAt.mul
    (raw_hasFDerivAt data.cusp point vector argument positive).differentiableAt, ?_⟩
  rw [function_fderiv data.cusp point vector weight argument positive Complex.I,
    function_fderiv data.cusp point vector weight argument positive 1,
    normalization_fderiv_one weight argument positive, normalization_fderiv_I weight argument positive,
    raw_cauchyRiemann data point vector weight eigen highest argument positive]
  simp only [smul_eq_mul]
  ring

theorem differentiableOn {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (weight : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (highest : raising data.cusp vector = 0) :
    DifferentiableOn ℂ (function data.cusp point vector weight) {argument : ℂ | 0 < argument.im} :=
  fun argument positive => (differentiableAt data point vector weight eigen highest argument positive).differentiableWithinAt

theorem mdifferentiable {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (weight : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (highest : raising data.cusp vector = 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun argument : UpperHalfPlane => function data.cusp point vector weight argument) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply (differentiableOn data point vector weight eigen highest).congr
  intro argument positive
  exact UpperHalfPlane.comp_ofComplex_of_im_pos _ argument positive

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic
