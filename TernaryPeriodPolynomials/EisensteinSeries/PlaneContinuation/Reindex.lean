module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Series

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Reindex

theorem eisensteinSummand_rational_left {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (rationalMatrix : RationalGL3) (basePoint : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand sectionFamily parameter (rationalGroup rationalMatrix * basePoint) flag =
      eisensteinSummand sectionFamily parameter basePoint (rationalMatrix⁻¹ • flag) := by
  have sameFlag : (QuotientGroup.mk (rationalMatrix⁻¹ * flag.out) : Flags .plane) =
      QuotientGroup.mk (rationalMatrix⁻¹ • flag : Flags .plane).out := by
    change rationalMatrix⁻¹ • (QuotientGroup.mk flag.out : Flags .plane) = _
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq']
  have invariance := TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.induced_eq_of_flag inducedSection
    _ _ sameFlag basePoint
  simpa only [eisensteinSummand, mul_inv_rev, inv_inv, map_mul, mul_assoc] using invariance

theorem eisensteinSummand_finiteLevel {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (basePoint : AdelicGL) (levelElement : finiteLevel) (flag : Flags .plane) :
    eisensteinSummand sectionFamily parameter (basePoint * atFinite levelElement.val) flag =
      eisensteinSummand sectionFamily parameter basePoint flag := by
  unfold eisensteinSummand
  rw [← mul_assoc, inducedSection.2.1 levelElement]

theorem summable_rational_left_iff {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (rationalMatrix : RationalGL3) (basePoint : AdelicGL) :
    Summable (eisensteinSummand sectionFamily parameter (rationalGroup rationalMatrix * basePoint)) ↔
      Summable (eisensteinSummand sectionFamily parameter basePoint) := by
  have reindexed : eisensteinSummand sectionFamily parameter (rationalGroup rationalMatrix * basePoint) =
      eisensteinSummand sectionFamily parameter basePoint ∘
        (MulAction.toPerm rationalMatrix⁻¹ : Equiv.Perm (Flags .plane)) :=
    funext (eisensteinSummand_rational_left inducedSection rationalMatrix basePoint)
  rw [reindexed]
  exact (MulAction.toPerm rationalMatrix⁻¹ : Equiv.Perm (Flags .plane)).summable_iff

theorem hasSum_rational_left_iff {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (rationalMatrix : RationalGL3) (basePoint : AdelicGL) (value : ℂ) :
    HasSum (eisensteinSummand sectionFamily parameter (rationalGroup rationalMatrix * basePoint)) value ↔
      HasSum (eisensteinSummand sectionFamily parameter basePoint) value := by
  have reindexed : eisensteinSummand sectionFamily parameter (rationalGroup rationalMatrix * basePoint) =
      eisensteinSummand sectionFamily parameter basePoint ∘
        (MulAction.toPerm rationalMatrix⁻¹ : Equiv.Perm (Flags .plane)) :=
    funext (eisensteinSummand_rational_left inducedSection rationalMatrix basePoint)
  rw [reindexed]
  exact (MulAction.toPerm rationalMatrix⁻¹ : Equiv.Perm (Flags .plane)).hasSum_iff

theorem literalSum_rational_left {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (rationalMatrix : RationalGL3) (basePoint : AdelicGL) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter (rationalGroup rationalMatrix * basePoint) =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint := by
  unfold TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum
  simp only [eisensteinSummand_rational_left inducedSection]
  exact (MulAction.toPerm rationalMatrix⁻¹ : Equiv.Perm (Flags .plane)).tsum_eq
    (eisensteinSummand sectionFamily parameter basePoint)

theorem literalSum_finiteLevel {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFamily : ℂ → AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter (sectionFamily parameter))
    (basePoint : AdelicGL) (levelElement : finiteLevel) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter (basePoint * atFinite levelElement.val) =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint := by
  unfold TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum
  simp only [eisensteinSummand_finiteLevel inducedSection]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Reindex
