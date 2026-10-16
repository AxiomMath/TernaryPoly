module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.RealCovariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleCuspLift

theorem levi_mul (first second : BinaryAdelicGL) :
    planeLevi (first * second) 1 = planeLevi first 1 * planeLevi second 1 := by
  change (planeLeviHom Adeles) (first * second, 1) = (planeLeviHom Adeles) (first, 1) * (planeLeviHom Adeles) (second, 1)
  rw [← map_mul]
  simp only [Prod.mk_mul_mk, one_mul]

theorem section_realize_product {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (finiteEvaluation : BinaryFiniteGL) (realEvaluation : BinaryRealGL) :
    FiniteSectionProjection.sectionFunction induced
      (planeLevi (atFinite finiteEvaluation * atInfinity realEvaluation) 1 * (inclusion point * atInfinity realPoint)) =
      normPower (GeneralLinearGroup.det (atFinite finiteEvaluation * atInfinity realEvaluation))
        (binaryInductionExponent degree .plane parameter) *
          (outerCharacter data parameter (GeneralLinearGroup.det (inclusion point * atInfinity realPoint)) *
            data.cusp.realize (SmoothTupleOperator.averagedRow data parameter halfPlane point
              (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))))
                (atFinite finiteEvaluation * atInfinity realEvaluation)) := by
  rw [levi_mul, mul_assoc, ← TupleRealCovariance.point_levi,
    TupleFiniteCusp.section_realize induced halfPlane point (planeLevi realEvaluation 1 * realPoint) finiteEvaluation,
    TupleRealCovariance.averagedRow_levi induced halfPlane point realPoint realEvaluation]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, DirectionalRealization.smoothTranslate_realize]
  have outer : outerCharacter data parameter
      (GeneralLinearGroup.det (inclusion point * atInfinity (planeLevi realEvaluation 1 * realPoint))) =
        outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realEvaluation)) *
          outerCharacter data parameter (GeneralLinearGroup.det (inclusion point * atInfinity realPoint)) := by
    rw [TupleRealCovariance.point_levi]
    simp only [map_mul, det_planeLevi, mul_one]
  rw [outer, map_mul GeneralLinearGroup.det (atFinite finiteEvaluation) (atInfinity realEvaluation), Helpers.normPower_mul,
    ← characters_product data parameter (GeneralLinearGroup.det (atInfinity realEvaluation))]
  ring

theorem section_realize {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryAdelicGL) :
    FiniteSectionProjection.sectionFunction induced
      (planeLevi evaluation 1 * (inclusion point * atInfinity realPoint)) =
      normPower (GeneralLinearGroup.det evaluation) (binaryInductionExponent degree .plane parameter) *
        (outerCharacter data parameter (GeneralLinearGroup.det (inclusion point * atInfinity realPoint)) *
          data.cusp.realize (SmoothTupleOperator.averagedRow data parameter halfPlane point
            (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))) evaluation) := by
  let realEvaluation := (BinaryProductHaar.combineEquiv.symm evaluation).1
  let finiteEvaluation := (BinaryProductHaar.combineEquiv.symm evaluation).2
  have split : evaluation = atFinite finiteEvaluation * atInfinity realEvaluation :=
    (BinaryProductHaar.combineEquiv.apply_symm_apply evaluation).symm.trans
      (BinaryProductHaar.combine_eq realEvaluation finiteEvaluation)
  rw [split]
  exact section_realize_product induced halfPlane point realPoint finiteEvaluation realEvaluation

def vector {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) : data.cusp.smooth :=
  outerCharacter data parameter (GeneralLinearGroup.det (inclusion point * atInfinity realPoint)) •
    SmoothTupleOperator.averagedRow data parameter halfPlane point
      (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))

theorem realize_vector {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (vector induced halfPlane point realPoint) evaluation =
      normPower (GeneralLinearGroup.det evaluation) (-binaryInductionExponent degree .plane parameter) *
        FiniteSectionProjection.sectionFunction induced (planeLevi evaluation 1 * (inclusion point * atInfinity realPoint)) := by
  rw [section_realize induced halfPlane point realPoint evaluation]
  simp only [vector, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Helpers.normPower_add]
  simp only [neg_add_cancel, Helpers.normPower_zero, one_mul]

theorem cuspFunctions_mem {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    (fun evaluation : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det evaluation) (-binaryInductionExponent degree .plane parameter) *
        FiniteSectionProjection.sectionFunction induced (planeLevi evaluation 1 * (inclusion point * atInfinity realPoint))) ∈
      cuspFunctions data.cusp := by
  refine ⟨vector induced halfPlane point realPoint, ?_⟩
  funext evaluation
  exact realize_vector induced halfPlane point realPoint evaluation

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleCuspLift
