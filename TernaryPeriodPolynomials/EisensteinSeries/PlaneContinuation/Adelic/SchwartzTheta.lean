module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Transport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicSchwartzTheta

noncomputable def tensorTest (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (matrix : Rectangular Adeles) : ℂ :=
  realTest (archimedean matrix) * finiteTest (finite matrix)

noncomputable def realPullback (realTest : SchwartzMap RealSpace ℂ)
    (point : AdelicGL) (binary : BinaryAdelicGL) : SchwartzMap RealSpace ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (realTransform (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) point)
      (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) binary)) realTest

noncomputable def finitePullback (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (binary : BinaryAdelicGL) : Rectangular FiniteAdeles → ℂ :=
  finiteTest ∘ matrixHomeomorph (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) point)
    (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) binary)

theorem matrixTerm_factorization (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (matrix : Rectangular ℚ) :
    matrixTerm (tensorTest realTest finiteTest) point binary matrix =
      realPullback realTest point binary (realVector matrix) * finitePullback finiteTest point binary (finiteMatrix matrix) := by
  simp only [matrixTerm, tensorTest, archimedean_transport, finite_transport,
    archimedean_rational, finite_rational, realPullback, finitePullback,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

theorem finitePullback_continuous (finiteTest : Rectangular FiniteAdeles → ℂ)
    (continuousTest : Continuous finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Continuous (finitePullback finiteTest point binary) :=
  continuousTest.comp (matrixHomeomorph _ _).continuous

theorem finitePullback_compactSupport (finiteTest : Rectangular FiniteAdeles → ℂ)
    (compactSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    HasCompactSupport (finitePullback finiteTest point binary) :=
  compactSupport.comp_homeomorph (matrixHomeomorph _ _)

theorem summable_norm (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun matrix => ‖matrixTerm (tensorTest realTest finiteTest) point binary matrix‖) := by
  simpa only [matrixTerm_factorization] using
    summable_norm_product (realPullback realTest point binary) (finitePullback finiteTest point binary)
      (finitePullback_continuous finiteTest finiteContinuous point binary)
      (finitePullback_compactSupport finiteTest finiteSupport point binary)

theorem summable (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (matrixTerm (tensorTest realTest finiteTest) point binary) :=
  (summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).of_norm

theorem frame_summable_norm (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun frame : Frame => ‖RectangularKernel.term (tensorTest realTest finiteTest) point binary frame‖) :=
  (summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).subtype FullRank

theorem frame_summable (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (RectangularKernel.term (tensorTest realTest finiteTest) point binary) :=
  (frame_summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).of_norm

theorem decomposition (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    fullTheta (tensorTest realTest finiteTest) point binary =
      RectangularKernel.theta (tensorTest realTest finiteTest) point binary +
        singularTheta (tensorTest realTest finiteTest) point binary :=
  RectangularTheta.decomposition _ point binary (summable realTest finiteTest finiteContinuous finiteSupport point binary)

theorem archimedean_continuous : Continuous archimedean := by
  have coordinates : Continuous (fun matrix : Rectangular Adeles => matrix.map (RingHom.fst ℝ FiniteAdeles)) :=
    continuous_pi (fun row => continuous_pi (fun column =>
      continuous_fst.comp ((continuous_apply column).comp (continuous_apply row))))
  exact coordinateEquiv.toContinuousLinearEquiv.continuous.comp coordinates

theorem finite_continuous : Continuous finite :=
  continuous_pi (fun row => continuous_pi (fun column =>
    continuous_snd.comp ((continuous_apply column).comp (continuous_apply row))))

theorem tensorTest_continuous (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest) :
    Continuous (tensorTest realTest finiteTest) :=
  (realTest.continuous.comp archimedean_continuous).mul (finiteContinuous.comp finite_continuous)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicSchwartzTheta
