module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CasimirIrreducibility

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirNorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LadderAdmissibility

noncomputable def raisingMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (index : ℤ) :
    fixedMode data level index →ₗ[ℂ] fixedMode data level (index + 2) :=
  ((raising data).comp (fixedMode data level index).subtype).codRestrict
    (fixedMode data level (index + 2)) (fun vector => raising_mem_fixedMode data level vector.val index vector.property)

noncomputable def loweringMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (index : ℤ) :
    fixedMode data level index →ₗ[ℂ] fixedMode data level (index - 2) :=
  ((lowering data).comp (fixedMode data level index).subtype).codRestrict
    (fixedMode data level (index - 2)) (fun vector => lowering_mem_fixedMode data level vector.val index vector.property)

theorem raisingMap_injective (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (index : ℤ) (value : ℂ) (scalar : ∀ vector : data.smooth, casimir data vector = value • vector)
    (nonzero : value - (index : ℂ) * (index + 2) ≠ 0) :
    Function.Injective (raisingMap data level index) := by
  intro first second equality
  have equalRaised : raising data first.val = raising data second.val := congrArg Subtype.val equality
  have firstEigen := (rotation_eigen_iff data first.val index).mpr
    ((mem_fixedMode_iff data level index first.val).mp first.property).2
  have secondEigen := (rotation_eigen_iff data second.val index).mpr
    ((mem_fixedMode_iff data level index second.val).mp second.property).2
  have equalScaled := congrArg (lowering data) equalRaised
  rw [lowering_raising_of_eigen data first.val index value firstEigen (scalar first.val),
    lowering_raising_of_eigen data second.val index value secondEigen (scalar second.val)] at equalScaled
  exact Subtype.ext ((smul_right_inj nonzero).mp equalScaled)

theorem loweringMap_injective (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (index : ℤ) (value : ℂ) (scalar : ∀ vector : data.smooth, casimir data vector = value • vector)
    (nonzero : value - (index : ℂ) * (index - 2) ≠ 0) :
    Function.Injective (loweringMap data level index) := by
  intro first second equality
  have equalLowered : lowering data first.val = lowering data second.val := congrArg Subtype.val equality
  have firstEigen := (rotation_eigen_iff data first.val index).mpr
    ((mem_fixedMode_iff data level index first.val).mp first.property).2
  have secondEigen := (rotation_eigen_iff data second.val index).mpr
    ((mem_fixedMode_iff data level index second.val).mp second.property).2
  have equalScaled := congrArg (raising data) equalLowered
  rw [raising_lowering_of_eigen data first.val index value firstEigen (scalar first.val),
    raising_lowering_of_eigen data second.val index value secondEigen (scalar second.val)] at equalScaled
  exact Subtype.ext ((smul_right_inj nonzero).mp equalScaled)

theorem finiteDimensional_of_raising (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (index : ℤ) (value : ℂ) (scalar : ∀ vector : data.smooth, casimir data vector = value • vector)
    (nonzero : value - (index : ℂ) * (index + 2) ≠ 0)
    [FiniteDimensional ℂ (fixedMode data level (index + 2))] :
    FiniteDimensional ℂ (fixedMode data level index) :=
  FiniteDimensional.of_injective (raisingMap data level index)
    (raisingMap_injective data level index value scalar nonzero)

theorem finiteDimensional_of_lowering (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (index : ℤ) (value : ℂ) (scalar : ∀ vector : data.smooth, casimir data vector = value • vector)
    (nonzero : value - (index : ℂ) * (index - 2) ≠ 0)
    [FiniteDimensional ℂ (fixedMode data level (index - 2))] :
    FiniteDimensional ℂ (fixedMode data level index) :=
  FiniteDimensional.of_injective (loweringMap data level index)
    (loweringMap_injective data level index value scalar nonzero)

theorem fixedMode_eq_bot_of_small_weight (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (base index : ℤ) (baseBound : 3 ≤ base) (smallWeight : |index| < base)
    (scalar : ∀ vector : data.smooth, casimir data vector = ((base : ℂ) * (base - 2)) • vector) :
    fixedMode data level index = ⊥ := by
  apply eq_bot_iff.mpr
  intro vector membership
  change vector = 0
  by_contra nonzero
  have rotationEigen := (rotation_eigen_iff data vector index).mpr
    ((mem_fixedMode_iff data level index vector).mp membership).2
  have scalarReal : casimir data vector = (((base : ℝ) * (base - 2) : ℝ) : ℂ) • vector := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat] using scalar vector
  have raisingBound := raising_coefficient_nonneg data vector nonzero index ((base : ℝ) * (base - 2)) rotationEigen scalarReal
  have loweringBound := lowering_coefficient_nonneg data vector nonzero index ((base : ℝ) * (base - 2)) rotationEigen scalarReal
  have realBase : (3 : ℝ) ≤ base := by exact_mod_cast baseBound
  obtain ⟨lowerSmall, upperSmall⟩ := abs_lt.mp smallWeight
  have positiveSmall : (index : ℝ) ≤ base - 1 := by
    have : index ≤ base - 1 := by omega
    exact_mod_cast this
  have negativeSmall : -(base : ℝ) + 1 ≤ index := by
    have : -base + 1 ≤ index := by omega
    exact_mod_cast this
  by_cases positive : (0 : ℝ) ≤ index
  · have productNonnegative : 0 ≤ (index : ℝ) * (base - 1 - index) :=
      mul_nonneg positive (by linarith)
    nlinarith
  · have productNonnegative : 0 ≤ -(index : ℝ) * (base - 1 + index) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- A scalar discrete-series Casimir reduces every fixed-level rotation type to its two endpoint types. -/
theorem finite_types_of_endpoints (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (base : ℤ) (baseBound : 3 ≤ base)
    (scalar : ∀ vector : data.smooth, casimir data vector = ((base : ℂ) * (base - 2)) • vector)
    [FiniteDimensional ℂ (fixedMode data level base)]
    [FiniteDimensional ℂ (fixedMode data level (-base))] :
    ∀ index : ℤ, FiniteDimensional ℂ (fixedMode data level index) := by
  have inductionClaim : ∀ size : ℕ, ∀ index : ℤ, index.natAbs = size →
      FiniteDimensional ℂ (fixedMode data level index) := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
      intro index sizeEquality
      by_cases small : |index| < base
      · rw [fixedMode_eq_bot_of_small_weight data level base index baseBound small scalar]
        infer_instance
      by_cases positiveEndpoint : index = base
      · subst index
        infer_instance
      by_cases negativeEndpoint : index = -base
      · subst index
        infer_instance
      by_cases positive : 0 ≤ index
      · rw [abs_of_nonneg positive] at small
        have above : base < index := by omega
        have nextSmaller : (index - 2).natAbs < size := by
          have current := Int.natAbs_of_nonneg positive
          have next := Int.natAbs_of_nonneg (show 0 ≤ index - 2 by omega)
          omega
        let _ : FiniteDimensional ℂ (fixedMode data level (index - 2)) :=
          inductionHypothesis (index - 2).natAbs nextSmaller (index - 2) rfl
        apply finiteDimensional_of_lowering data level index ((base : ℂ) * (base - 2)) scalar
        intro vanishing
        have realEquality : (base : ℝ) * (base - 2) = (index : ℝ) * (index - 2) := by
          exact_mod_cast (sub_eq_zero.mp vanishing)
        have baseReal : (3 : ℝ) ≤ base := by exact_mod_cast baseBound
        have aboveReal : (base : ℝ) < index := by exact_mod_cast above
        nlinarith [mul_pos (sub_pos.mpr aboveReal) (show 0 < (index : ℝ) + base - 2 by linarith)]
      · rw [abs_of_neg (show index < 0 by omega)] at small
        have below : index < -base := by omega
        have nextSmaller : (index + 2).natAbs < size := by
          have current := Int.natCast_natAbs index
          have next := Int.natCast_natAbs (index + 2)
          rw [abs_of_nonpos (show index ≤ 0 by omega)] at current
          rw [abs_of_nonpos (show index + 2 ≤ 0 by omega)] at next
          omega
        let _ : FiniteDimensional ℂ (fixedMode data level (index + 2)) :=
          inductionHypothesis (index + 2).natAbs nextSmaller (index + 2) rfl
        apply finiteDimensional_of_raising data level index ((base : ℂ) * (base - 2)) scalar
        intro vanishing
        have realEquality : (base : ℝ) * (base - 2) = (index : ℝ) * (index + 2) := by
          exact_mod_cast (sub_eq_zero.mp vanishing)
        have baseReal : (3 : ℝ) ≤ base := by exact_mod_cast baseBound
        have belowReal : (index : ℝ) < -base := by exact_mod_cast below
        nlinarith [mul_pos (show 0 < -(index : ℝ) - base by linarith)
          (show 0 < -(index : ℝ) + base - 2 by linarith)]
  intro index
  exact inductionClaim index.natAbs index rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LadderAdmissibility
