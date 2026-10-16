module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralFlagFrames
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OrbitDetection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem integralFrame_column_in_plane (frame : IntegralGL3) (index : Fin 2) :
    IntegralVectorInFlag .plane (QuotientGroup.mk (integralRational frame))
      (fun row => frame.val row index.castSucc) := by
  refine ⟨integralRational frame, rfl, Pi.single index.castSucc 1, ?_, ?_⟩
  · fin_cases index <;> rfl
  · funext row
    simp [integralRational, GeneralLinearGroup.map_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem zmodThree_exists_integer_unit (value : ZMod 3) (nonzero : value ≠ 0) :
    ∃ unit : ℤˣ, value * (unit.val : ZMod 3) = 1 := by
  fin_cases value
  · exact (nonzero rfl).elim
  · exact ⟨1, by decide⟩
  · exact ⟨-1, by decide⟩

/-- Every bad rational plane is represented by an element of the actual arithmetic level. -/
theorem badPlane_exists_arithmetic_frame (flag : Flags .plane) (bad : ¬ GoodFlag .plane flag) :
    ∃ frame : arithmeticLevel, QuotientGroup.mk (rationalInclusion frame) = flag := by
  induction flag using Quotient.inductionOn with
  | h representative =>
    obtain ⟨frame, same_flag⟩ := rationalPlane_exists_integral_frame representative
    have columns_zero (index : Fin 2) : (frame.val 2 index.castSucc : ZMod 3) = 0 := by
      by_contra nonzero
      apply bad
      change GoodFlag .plane (QuotientGroup.mk representative)
      rw [← same_flag]
      exact ⟨_, integralFrame_column_in_plane frame index, nonzero⟩
    have last_nonzero : (frame.val 2 2 : ZMod 3) ≠ 0 := by
      intro zero
      have diagonal := congrArg (fun value : IntegralGL3 => (value.val 2 2 : ZMod 3))
        (mul_inv_cancel frame)
      simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
        Int.cast_add, Int.cast_mul, GeneralLinearGroup.coe_one, Matrix.one_apply_eq] at diagonal
      have first := columns_zero 0
      have second := columns_zero 1
      norm_num at first second
      rw [first, second, zero] at diagonal
      norm_num at diagonal
    obtain ⟨unit, unit_eq⟩ := zmodThree_exists_integer_unit (frame.val 2 2) last_nonzero
    let adjusted := frame * planeLevi 1 unit
    have adjusted_level : adjusted ∈ arithmeticLevel := by
      change lastRow ᵥ* (reductionThree adjusted).val = lastRow
      funext column
      have first := columns_zero 0
      have second := columns_zero 1
      norm_num at first second
      fin_cases column <;>
        simp [adjusted, reductionThree,
          planeLevi, planeBlock, lastRow, Matrix.vecMul, dotProduct, Matrix.mul_apply,
          Fin.sum_univ_three, first, second, unit_eq]
    refine ⟨⟨adjusted, adjusted_level⟩, ?_⟩
    change QuotientGroup.mk (integralRational (frame * planeLevi 1 unit)) = _
    rw [map_mul, QuotientGroup.mk_mul_of_mem]
    · exact same_flag
    · change (integralRational (planeLevi 1 unit)).val 2 0 = 0 ∧
        (integralRational (planeLevi 1 unit)).val 2 1 = 0
      simp [integralRational, GeneralLinearGroup.map_apply, planeLevi, planeBlock]

/-- The bad-plane cusps form one orbit under the specified congruence subgroup. -/
theorem badPlane_exists_transporter (flag : Flags .plane) (bad : ¬ GoodFlag .plane flag) :
    ∃ element : rationalLevel, element.val • (QuotientGroup.mk (1 : RationalGL3)) = flag := by
  obtain ⟨frame, equality⟩ := badPlane_exists_arithmetic_frame flag bad
  refine ⟨⟨rationalInclusion frame, ⟨frame, rfl⟩⟩, ?_⟩
  change QuotientGroup.mk (rationalInclusion frame * 1) = flag
  simpa only [mul_one] using equality

/-- Vanishing at the identity plane detects a class already supported on bad planes. -/
theorem badPlaneRepresentative_eq_zero_of_identityRestriction {degree : ℕ}
    (data : InducingData degree) (coordinate : boundarySummand data .plane)
    (supported : BadPlaneRepresentative data coordinate)
    (identity_zero : flagRestriction data.chi .plane (QuotientGroup.mk (1 : RationalGL3))
      coordinate.val = 0) : coordinate = 0 := by
  apply badPlaneRepresentative_eq_zero_of_badRestrictions data coordinate supported
  intro flag bad
  obtain ⟨element, transported⟩ := badPlane_exists_transporter flag bad
  rw [← transported]
  exact flagRestriction_smul_zero data.chi .plane (QuotientGroup.mk (1 : RationalGL3))
    element coordinate.val identity_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
