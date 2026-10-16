module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ConstantTermBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CuspidalConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AveragedGodementContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementConstantTermBounds

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementConstantTerm

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem average_literalSum {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : RectangularFrames.Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : AdelicGL) :
    average (ScalarSeries.literalSum (sections data family realTest finiteTest) parameter) point =
      sections data family realTest finiteTest parameter point := by
  have sectionMeasurable := section_measurable data family continuous realTest finiteTest finiteContinuous parameter
  have exponentBound := (RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane
  apply CuspidalConstantTerm.average_literalSum
    (GodementCuspIntegrability.relations data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane) point
  · intro slope
    exact sectionMeasurable.comp
      ((PlaneChartContinuity.leviUnipotent_continuous.comp continuous_fst).mul
        ((PlaneChartContinuity.affine_continuous.comp (continuous_const.prodMk continuous_snd)).mul continuous_const)).measurable
  · exact sectionMeasurable.comp
      ((PlaneChartContinuity.leviUnipotent_continuous.comp continuous_fst).mul
        ((PlaneChartContinuity.vertical_continuous.comp continuous_snd).mul continuous_const)).measurable
  · exact GodementConstantTermBounds.term_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter exponentBound point
  · exact integral_norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter exponentBound point

theorem average_continuation {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : AdelicGL) :
    average (fun value => VectorGodementContinuation.continuation data family realTest finiteScale offset parameter value) point =
      sections data family realTest (RectangularAdelicPoisson.finiteTest finiteScale offset) parameter point := by
  have equality : (fun value => VectorGodementContinuation.continuation data family realTest finiteScale offset parameter value) =
      ScalarSeries.literalSum (sections data family realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) parameter := by
    funext value
    exact (VectorGodementContinuation.eisenstein_hasSum data family continuous realTest finiteScale offset value parameter halfPlane).tsum_eq.symm
  rw [equality]
  exact average_literalSum data family continuous realTest _ (ZeroConstantThetaDecay.finiteTest_continuous finiteScale offset)
    (ZeroConstantThetaDecay.finiteTest_compactSupport finiteScale offset) parameter halfPlane point

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementConstantTerm
