module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CasimirScalar
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Casimir
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ReflectionModes

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalCasimir

/-- The exact inducing hypotheses determine the Casimir on every supplied smooth vector. -/
theorem scalar {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) :
    casimir data.cusp vector = ((degree + 3 : ℂ) * (degree + 1)) • vector := by
  obtain ⟨value, scalar⟩ := CasimirScalar.exists_scalar data
  rw [EndpointCasimir.forced_value data value scalar] at scalar
  exact scalar vector

theorem positive_endpoint_lowest {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (rotationEigen : rotationOperator data.cusp vector = (Complex.I * (degree + 3 : ℤ)) • vector) :
    lowering data.cusp vector = 0 :=
  EndpointCasimir.upper_killed data.cusp degree vector rotationEigen (scalar data vector)

theorem negative_endpoint_highest {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (rotationEigen : rotationOperator data.cusp vector = (Complex.I * (-(degree + 3 : ℤ))) • vector) :
    raising data.cusp vector = 0 :=
  EndpointCasimir.lower_killed data.cusp degree vector rotationEigen (scalar data vector)

/-- The nonzero cohomology class supplies a genuine analytic lowest-weight vector. -/
theorem exists_lowest_weight_fixed {degree : ℕ} (data : InducingData degree) :
    ∃ vector : data.cusp.smooth, vector ≠ 0 ∧
      rotationOperator data.cusp vector = (Complex.I * (degree + 3 : ℤ)) • vector ∧
      lowering data.cusp vector = 0 ∧
      ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ vector.val ∈ fixedSubspace data.cusp level := by
  obtain ⟨upper, lower, ⟨level, openness, compactness, upperFixed, lowerFixed⟩,
    upperRotation, lowerRotation, _, nontrivialClass⟩ := EndpointComplex.exists_nontrivial_endpoint_complex data
  rcases EndpointComplex.endpoints_not_both_zero data.cusp degree upper lower nontrivialClass with upperNonzero | lowerNonzero
  · exact ⟨upper, upperNonzero, upperRotation, positive_endpoint_lowest data upper upperRotation,
      level, openness, compactness, upperFixed⟩
  · let vector := smoothTranslate data.cusp reflection lower
    have nonzero : vector ≠ 0 := by
      intro vanishing
      apply lowerNonzero
      apply (reflection_involutive data.cusp).injective
      exact vanishing.trans (map_zero _).symm
    have eigen : rotationOperator data.cusp vector = (Complex.I * (degree + 3 : ℤ)) • vector := by
      have equality := reflection_eigen data.cusp lower (-(degree + 3))
        (by simpa only [Int.cast_neg] using lowerRotation)
      simpa only [neg_neg] using equality
    exact ⟨vector, nonzero, eigen, positive_endpoint_lowest data vector eigen,
      level, openness, compactness, fixedSubspace_real_stable data.cusp level reflection lower.val lowerFixed⟩

theorem exists_lowest_weight {degree : ℕ} (data : InducingData degree) :
    ∃ vector : data.cusp.smooth, vector ≠ 0 ∧
      rotationOperator data.cusp vector = (Complex.I * (degree + 3 : ℤ)) • vector ∧
      lowering data.cusp vector = 0 := by
  obtain ⟨vector, nonzero, eigen, lowest, _⟩ := exists_lowest_weight_fixed data
  exact ⟨vector, nonzero, eigen, lowest⟩

theorem exists_highest_weight_fixed {degree : ℕ} (data : InducingData degree) :
    ∃ vector : data.cusp.smooth, vector ≠ 0 ∧
      rotationOperator data.cusp vector = (Complex.I * (-(degree + 3 : ℤ))) • vector ∧
      raising data.cusp vector = 0 ∧
      ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ vector.val ∈ fixedSubspace data.cusp level := by
  obtain ⟨lowest, nonzero, eigen, _, level, openness, compactness, fixed⟩ := exists_lowest_weight_fixed data
  let vector := smoothTranslate data.cusp reflection lowest
  have vectorNonzero : vector ≠ 0 := by
    intro vanishing
    apply nonzero
    apply (reflection_involutive data.cusp).injective
    exact vanishing.trans (map_zero _).symm
  have vectorEigen : rotationOperator data.cusp vector = (Complex.I * (-(degree + 3 : ℤ))) • vector := by
    simpa only [Int.cast_neg] using reflection_eigen data.cusp lowest (degree + 3) eigen
  exact ⟨vector, vectorNonzero, vectorEigen, negative_endpoint_highest data vector vectorEigen,
    level, openness, compactness, fixedSubspace_real_stable data.cusp level reflection lowest.val fixed⟩

theorem hasSum_of_endpoint_finiteDimensional {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    [FiniteDimensional ℂ (FiniteRotationTypes.fixedMode data.cusp finiteCongruence (degree + 3))]
    (basePoint : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (ScalarSeries.literalSum sectionFamily parameter basePoint) := by
  obtain ⟨vector, nonzero, eigen, lowest⟩ := exists_lowest_weight data
  exact hasSum_of_lowest_weight flatSection (degree + 3) (by omega) vector nonzero eigen lowest
    basePoint parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalCasimir
