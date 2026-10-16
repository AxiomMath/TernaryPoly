module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProductFormula
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegerReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance

noncomputable def rationalPlane (element : planeParabolic ℚ) : planeParabolic Adeles :=
  ⟨rationalGroup element.val, inPlane_map rationalAdele element.val element.property⟩

theorem corner_rational (element : planeParabolic ℚ) :
    planeCornerUnit (rationalPlane element) =
      Units.map rationalAdele.toMonoidHom (planeCornerUnit element) := by
  apply Units.ext
  rfl

theorem binaryBlock_rational (element : planeParabolic ℚ) :
    planeBinaryBlock (rationalPlane element) =
      Matrix.GeneralLinearGroup.map rationalAdele (planeBinaryBlock element) := by
  apply Units.ext
  rfl

theorem induced_rational_plane {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (element : planeParabolic ℚ) (basePoint : AdelicGL) :
    sectionFunction (rationalGroup element.val * basePoint) = sectionFunction basePoint := by
  have parabolicFormula := induced_planeParabolic_formula inducedSection
    (rationalPlane element) basePoint
  have cornerCharacter : data.chi.toMonoidHom (planeCornerUnit (rationalPlane element)) = 1 := by
    rw [corner_rational]
    exact data.chi.rational _
  have cornerNorm : normPower (planeCornerUnit (rationalPlane element))
      (-2 * inductionExponent .plane parameter) = 1 := by
    rw [corner_rational]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.normPower_rational _ _
  have binaryNorm : normPower (Matrix.GeneralLinearGroup.det
      (planeBinaryBlock (rationalPlane element)))
      (binaryInductionExponent degree .plane parameter) = 1 := by
    rw [binaryBlock_rational, Matrix.GeneralLinearGroup.map_det]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.normPower_rational _ _
  rw [cornerCharacter, cornerNorm, binaryNorm, one_mul, one_mul, one_mul, binaryBlock_rational]
    at parabolicFormula
  have rationalValue := data.cusp.leftRational (planeBinaryBlock element)
    (planeCuspVector inducedSection basePoint) 1
  rw [mul_one] at rationalValue
  rw [rationalValue, ← induced_eq_planeCuspVector_one inducedSection basePoint] at parabolicFormula
  exact parabolicFormula

theorem induced_eq_of_flag {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (first second : RationalGL3)
    (sameFlag : (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk second)
    (basePoint : AdelicGL) :
    sectionFunction (rationalGroup first⁻¹ * basePoint) =
      sectionFunction (rationalGroup second⁻¹ * basePoint) := by
  have parabolicMembership : first⁻¹ * second ∈ planeParabolic ℚ := QuotientGroup.eq.mp sameFlag
  have invariance := induced_rational_plane inducedSection
    ⟨first⁻¹ * second, parabolicMembership⟩ (rationalGroup second⁻¹ * basePoint)
  change sectionFunction (rationalGroup (first⁻¹ * second) *
    (rationalGroup second⁻¹ * basePoint)) = _ at invariance
  rw [← mul_assoc, ← map_mul, mul_inv_cancel_right] at invariance
  exact invariance

theorem eisensteinSummand_eq_integral {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (basePoint : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand sectionFamily parameter basePoint flag =
      sectionFamily parameter
        (rationalGroup (integralRational
          (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag))⁻¹ * basePoint) := by
  apply induced_eq_of_flag inducedSection
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative_mk]
  exact Quotient.out_eq flag

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance
