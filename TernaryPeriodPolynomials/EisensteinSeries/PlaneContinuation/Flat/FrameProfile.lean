module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FrameCutoff

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatFrameProfile

theorem normalized_parabolic_realize {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (parabolic : planeParabolic Adeles) (point : AdelicGL) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (normalized induced (parabolic.val * point)) evaluation =
      innerCharacter data parameter (GeneralLinearGroup.det (planeBinaryBlock parabolic)) *
        data.cusp.realize (normalized induced point) (evaluation * planeBinaryBlock parabolic) := by
  simp only [normalized, planeCuspVector_planeParabolic, map_smul, Pi.smul_apply, smul_eq_mul,
    data.cusp.equivariant, map_mul, det_planeParabolic]
  change ((outerCharacter data parameter (GeneralLinearGroup.det (planeBinaryBlock parabolic)) *
      outerCharacter data parameter (planeCornerUnit parabolic) * outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹) *
    (outerCharacter data parameter (planeCornerUnit parabolic) *
      (normPower (GeneralLinearGroup.det (planeBinaryBlock parabolic)) (binaryInductionExponent degree .plane parameter) * _)) = _
  rw [← characters_product data parameter (GeneralLinearGroup.det (planeBinaryBlock parabolic))]
  have binaryNonzero := character_ne_zero (outerCharacter data parameter) (GeneralLinearGroup.det (planeBinaryBlock parabolic))
  have scalarNonzero := character_ne_zero (outerCharacter data parameter) (planeCornerUnit parabolic)
  field_simp

theorem inner_change_parameter {degree : ℕ} (data : InducingData degree)
    (parameter reference : ℂ) (scalar : Adelesˣ) :
    innerCharacter data parameter scalar = normPower scalar (parameter - reference) * innerCharacter data reference scalar := by
  have exponent : binaryInductionExponent degree .plane parameter + 2 * inductionExponent .plane parameter =
      (parameter - reference) + (binaryInductionExponent degree .plane reference + 2 * inductionExponent .plane reference) := by
    simp only [binaryInductionExponent, inductionExponent]
    ring
  change (data.chi.toMonoidHom scalar)⁻¹ * normPower scalar _ = _
  rw [exponent, normPower_add]
  unfold innerCharacter
  change _ = normPower scalar (parameter - reference) * ((data.chi.toMonoidHom scalar)⁻¹ * _)
  ring

theorem normalized_compact {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (parameter : ℂ) (compact : AdelicGL) (membership : inMaximalCompact compact) :
    normalized (flat.1 parameter) compact = normalized (flat.1 cohomologicalPoint) compact := by
  unfold normalized
  rw [flatSection_planeCuspVector_eq flat parameter compact membership]
  have outerEquality : outerCharacter data parameter (GeneralLinearGroup.det compact) =
      outerCharacter data cohomologicalPoint (GeneralLinearGroup.det compact) := by
    simp only [outerCharacter, MonoidHom.coe_mk, OneHom.coe_mk, normPower,
      Height.adeleNorm_det_maximalCompact compact membership, Real.log_one, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero]
  rw [outerEquality]

theorem normalized_parameter {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (parameter : ℂ) (point : AdelicGL) :
    normalized (flat.1 parameter) point =
      normPower (GeneralLinearGroup.det (planeBinaryBlock (parabolicPart point))) (parameter - cohomologicalPoint) •
        normalized (flat.1 cohomologicalPoint) point := by
  apply data.cusp.injective
  funext evaluation
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  have factorization := parabolicPart_mul_compactPart point
  conv_lhs => rw [factorization]
  conv_rhs => arg 2; rw [factorization]
  rw [normalized_parabolic_realize, normalized_parabolic_realize,
    normalized_compact flat parameter _ (compactPart_mem point), inner_change_parameter data parameter cohomologicalPoint,
    mul_assoc]

def height (value : RectangularFrames.Rectangular Adeles) : ℝ :=
  if existsPoint : ∃ point, frame point = value then
    Real.log (adeleNorm (GeneralLinearGroup.det (planeBinaryBlock (parabolicPart existsPoint.choose))) : ℝ)
  else 0

theorem profile_parameter {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (parameter : ℂ) (value : RectangularFrames.Rectangular Adeles) :
    profile (flat.1 parameter) value =
      Complex.exp ((parameter - cohomologicalPoint) * (height value : ℂ)) •
        profile (flat.1 cohomologicalPoint) value := by
  unfold profile height
  split_ifs with existsPoint
  · exact normalized_parameter flat parameter existsPoint.choose
  · simp only [smul_zero]

theorem profile_analytic {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (value : RectangularFrames.Rectangular Adeles) (parameter : ℂ) :
    AnalyticAt ℂ (fun parameter => (profile (flat.1 parameter) value).val) parameter := by
  have equality : (fun parameter => (profile (flat.1 parameter) value).val) =
      fun parameter => Complex.exp ((parameter - cohomologicalPoint) * (height value : ℂ)) •
        (profile (flat.1 cohomologicalPoint) value).val := by
    funext parameter
    exact congrArg Subtype.val (profile_parameter flat parameter value)
  rw [equality]
  exact (((analyticAt_id.sub analyticAt_const).mul analyticAt_const).cexp).smul analyticAt_const

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatFrameProfile
