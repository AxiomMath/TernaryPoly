module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Intertwining
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CasimirIrreducibility

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RaisingChain TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointIntertwining

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointCasimir

theorem upper_composition (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth) (value : ℂ)
    (rotationEigen : rotationOperator data vector = (Complex.I * (degree + 3 : ℤ)) • vector)
    (casimirEigen : casimir data vector = value • vector) :
    raising data (lowering data vector) = (value - (degree + 3 : ℂ) * (degree + 1)) • vector := by
  have equality := raising_lowering_of_eigen data vector (degree + 3) value rotationEigen casimirEigen
  have coefficient : value - ((degree + 3 : ℤ) : ℂ) * (((degree + 3 : ℤ) : ℂ) - 2) =
      value - (degree + 3 : ℂ) * (degree + 1) := by push_cast; ring
  rw [coefficient] at equality
  exact equality

theorem lower_composition (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth) (value : ℂ)
    (rotationEigen : rotationOperator data vector = (Complex.I * (-(degree + 3 : ℤ))) • vector)
    (casimirEigen : casimir data vector = value • vector) :
    lowering data (raising data vector) = (value - (degree + 3 : ℂ) * (degree + 1)) • vector := by
  have equality := lowering_raising_of_eigen data vector (-(degree + 3)) value
    (by simpa only [Int.cast_neg] using rotationEigen) casimirEigen
  have coefficient : value - ((-(degree + 3 : ℤ)) : ℂ) * (((-(degree + 3 : ℤ)) : ℂ) + 2) =
      value - (degree + 3 : ℂ) * (degree + 1) := by push_cast; ring
  simp only [Int.cast_neg] at equality
  rw [coefficient] at equality
  exact equality

/-- Away from the cohomological Casimir value the endpoint pair has an explicit analytic primitive. -/
theorem exact_of_other_casimir (data : CuspidalRepresentation) (degree : ℕ) (upper lower : data.smooth)
    (value : ℂ) (different : value ≠ (degree + 3 : ℂ) * (degree + 1))
    (upperRotation : rotationOperator data upper = (Complex.I * (degree + 3 : ℤ)) • upper)
    (lowerRotation : rotationOperator data lower = (Complex.I * (-(degree + 3 : ℤ))) • lower)
    (upperCasimir : casimir data upper = value • upper)
    (lowerCasimir : casimir data lower = value • lower)
    (equation : lowering data upper = raising data (chain data lower (degree + 1))) :
    ∃ vector : data.smooth,
      rotationOperator data vector = (Complex.I * (-(degree + 1 : ℤ))) • vector ∧
        upper = raising data (chain data vector (degree + 1)) ∧ lower = lowering data vector := by
  let scalar : ℂ := value - (degree + 3 : ℂ) * (degree + 1)
  have nonzero : scalar ≠ 0 := sub_ne_zero.mpr different
  refine ⟨scalar⁻¹ • raising data lower, ?_, ?_, ?_⟩
  · have eigen := raising_eigen data lower (-(degree + 3)) (by simpa only [Int.cast_neg] using lowerRotation)
    have indexEquality : -(degree + 3 : ℤ) + 2 = -(degree + 1 : ℤ) := by omega
    rw [map_smul, eigen, indexEquality]
    simpa only [Int.cast_neg] using smul_comm scalar⁻¹ (Complex.I * ((-(degree + 1 : ℤ)) : ℂ)) (raising data lower)
  · rw [chain_smul, map_smul, chain_raising, ← equation,
      upper_composition data degree upper value upperRotation upperCasimir]
    change upper = scalar⁻¹ • scalar • upper
    rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul]
  · rw [map_smul, lower_composition data degree lower value lowerRotation lowerCasimir]
    change lower = scalar⁻¹ • scalar • lower
    rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul]

theorem forced_value {degree : ℕ} (data : InducingData degree) (value : ℂ)
    (scalar : ∀ vector : data.cusp.smooth, casimir data.cusp vector = value • vector) :
    value = (degree + 3 : ℂ) * (degree + 1) := by
  by_contra different
  obtain ⟨upper, lower, _, upperRotation, lowerRotation, equation, nontrivialClass⟩ :=
    EndpointComplex.exists_nontrivial_endpoint_complex data
  exact nontrivialClass (exact_of_other_casimir data.cusp degree upper lower value different
    upperRotation lowerRotation (scalar upper) (scalar lower) equation)

theorem upper_killed (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth)
    (rotationEigen : rotationOperator data vector = (Complex.I * (degree + 3 : ℤ)) • vector)
    (casimirEigen : casimir data vector = ((degree + 3 : ℂ) * (degree + 1)) • vector) :
    lowering data vector = 0 := by
  have composition := upper_composition data degree vector _ rotationEigen casimirEigen
  rw [sub_self, zero_smul] at composition
  have identity := LieNorms.raising_inner data vector (lowering data vector)
  rw [composition] at identity
  change inner ℂ vector.val 0 + inner ℂ (lowering data vector).val (lowering data vector).val = 0 at identity
  rw [inner_zero_right, zero_add, inner_self_eq_zero] at identity
  exact Subtype.ext identity

theorem lower_killed (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth)
    (rotationEigen : rotationOperator data vector = (Complex.I * (-(degree + 3 : ℤ))) • vector)
    (casimirEigen : casimir data vector = ((degree + 3 : ℂ) * (degree + 1)) • vector) :
    raising data vector = 0 := by
  have composition := lower_composition data degree vector _ rotationEigen casimirEigen
  rw [sub_self, zero_smul] at composition
  have identity := LieNorms.lowering_inner data vector (raising data vector)
  rw [composition] at identity
  change inner ℂ vector.val 0 + inner ℂ (raising data vector).val (raising data vector).val = 0 at identity
  rw [inner_zero_right, zero_add, inner_self_eq_zero] at identity
  exact Subtype.ext identity

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointCasimir
