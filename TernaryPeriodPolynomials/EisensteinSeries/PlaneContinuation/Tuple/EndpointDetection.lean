module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.Ladder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleLadder

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleEndpointDetection

theorem lowering_coefficient_nonzero (base index : ℤ) (baseBound : 3 ≤ base) (above : base < index) :
    (base : ℂ) * (base - 2) - (index : ℂ) * (index - 2) ≠ 0 := by
  intro vanishing
  have realEquality : (base : ℝ) * (base - 2) = (index : ℝ) * (index - 2) := by
    exact_mod_cast (sub_eq_zero.mp vanishing)
  have baseReal : (3 : ℝ) ≤ base := by exact_mod_cast baseBound
  have aboveReal : (base : ℝ) < index := by exact_mod_cast above
  nlinarith [mul_pos (sub_pos.mpr aboveReal) (show 0 < (index : ℝ) + base - 2 by linarith)]

theorem raising_coefficient_nonzero (base index : ℤ) (baseBound : 3 ≤ base) (below : index < -base) :
    (base : ℂ) * (base - 2) - (index : ℂ) * (index + 2) ≠ 0 := by
  intro vanishing
  have realEquality : (base : ℝ) * (base - 2) = (index : ℝ) * (index + 2) := by
    exact_mod_cast (sub_eq_zero.mp vanishing)
  have baseReal : (3 : ℝ) ≤ base := by exact_mod_cast baseBound
  have belowReal : (index : ℝ) < -base := by exact_mod_cast below
  nlinarith [mul_pos (show 0 < -(index : ℝ) - base by linarith)
    (show 0 < -(index : ℝ) + base - 2 by linarith)]

theorem zero_of_endpoints {degree : ℕ} (data : InducingData degree) (base : ℤ) (baseBound : 3 ≤ base)
    (casimir : ∀ vector : data.cusp.smooth, LieCasimir.casimir data.cusp vector = ((base : ℂ) * (base - 2)) • vector)
    (family : ∀ index : ℤ, Module.End ℂ (admissible data index))
    (raising : ∀ index value, admissibleRaising data index (family index value) =
      family (index + 2) (admissibleRaising data index value))
    (lowering : ∀ index value, admissibleLowering data index (family index value) =
      family (index - 2) (admissibleLowering data index value))
    (positiveEndpoint : family base = 0) (negativeEndpoint : family (-base) = 0) :
    ∀ index : ℤ, family index = 0 := by
  have inductionClaim : ∀ size : ℕ, ∀ index : ℤ, index.natAbs = size → family index = 0 := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
      intro index sizeEquality
      by_cases small : |index| < base
      · let _ : Subsingleton (fixedMode data.cusp finiteCongruence index) := by
          rw [LadderAdmissibility.fixedMode_eq_bot_of_small_weight data.cusp finiteCongruence base index baseBound small casimir]
          infer_instance
        exact Subsingleton.elim _ _
      by_cases endpoint : index = base
      · exact endpoint ▸ positiveEndpoint
      by_cases negative : index = -base
      · exact negative ▸ negativeEndpoint
      by_cases positive : 0 ≤ index
      · rw [abs_of_nonneg positive] at small
        have above : base < index := by omega
        have nextSmaller : (index - 2).natAbs < size := by
          have current := Int.natAbs_of_nonneg positive
          have next := Int.natAbs_of_nonneg (show 0 ≤ index - 2 by omega)
          omega
        have nextZero := inductionHypothesis (index - 2).natAbs nextSmaller (index - 2) rfl
        apply LinearMap.ext
        intro value
        apply admissibleLowering_injective data index ((base : ℂ) * (base - 2)) casimir
          (lowering_coefficient_nonzero base index baseBound above)
        rw [lowering, nextZero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
      · rw [abs_of_neg (show index < 0 by omega)] at small
        have below : index < -base := by omega
        have nextSmaller : (index + 2).natAbs < size := by
          have current := Int.natCast_natAbs index
          have next := Int.natCast_natAbs (index + 2)
          rw [abs_of_nonpos (show index ≤ 0 by omega)] at current
          rw [abs_of_nonpos (show index + 2 ≤ 0 by omega)] at next
          omega
        have nextZero := inductionHypothesis (index + 2).natAbs nextSmaller (index + 2) rfl
        apply LinearMap.ext
        intro value
        apply admissibleRaising_injective data index ((base : ℂ) * (base - 2)) casimir
          (raising_coefficient_nonzero base index baseBound below)
        rw [raising, nextZero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  intro index
  exact inductionClaim index.natAbs index rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleEndpointDetection
