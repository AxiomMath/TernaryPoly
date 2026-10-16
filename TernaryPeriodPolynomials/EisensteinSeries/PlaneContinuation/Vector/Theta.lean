module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.AdelicTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.CuspContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorTheta

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

def term {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL)
    (matrix : Rectangular ℚ) : ℂ :=
  data.cusp.realize (family (BanachAdelicTheta.matrixTerm test point binary matrix)).val binary

def fullTheta {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  data.cusp.realize (family (BanachAdelicTheta.fullTheta test point binary)).val binary

theorem hasSum {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    HasSum (term data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary)
      (fullTheta data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary) :=
  (evaluation data family continuous binary).hasSum
    (BanachAdelicTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary).hasSum

theorem summable_norm {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun matrix => ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary matrix‖) := by
  apply ((BanachAdelicTheta.summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).mul_left
    ‖evaluation data family continuous binary‖).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro matrix
  exact (evaluation data family continuous binary).le_opNorm _

theorem term_continuous {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test) (matrix : Rectangular ℚ) :
    Continuous (fun parameter : Parameter => term data family test parameter.1 parameter.2 matrix) :=
  (BanachCuspContinuity.joint_continuous data family continuous).comp
    ((BanachAdelicTheta.matrixTerm_continuous test testContinuous matrix).prodMk continuous_snd)

theorem fullTheta_continuous {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) :
    Continuous (fun parameter : Parameter => fullTheta data family
      (BanachAdelicTheta.tensorTest realTest finiteTest) parameter.1 parameter.2) :=
  (BanachCuspContinuity.joint_continuous data family continuous).comp
    ((BanachAdelicTheta.fullTheta_continuous realTest finiteTest finiteContinuous finiteSupport).prodMk continuous_snd)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorTheta
