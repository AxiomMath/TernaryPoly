module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def standardBadLine : Flags .line := QuotientGroup.mk (1 : RationalGL3)

theorem integralVectorInFlag_standardBadLine (vector : Fin 3 → ℤ) :
    IntegralVectorInFlag .line standardBadLine vector ↔
      vector 1 = 0 ∧ vector 2 = 0 := by
  constructor
  · rintro ⟨representative, represented, coordinates, support, inFlag⟩
    have parabolic : representative ∈ lineParabolic ℚ := by
      have equality : (QuotientGroup.mk (1 : RationalGL3) : Flags .line) =
          QuotientGroup.mk representative := represented.symm
      have membership := QuotientGroup.eq.mp equality
      simpa only [inv_one, one_mul, GeneralEisenstein.parabolic] using membership
    have entries : representative.val 1 0 = 0 ∧ representative.val 2 0 = 0 := parabolic
    have first := congrFun inFlag 1
    have second := congrFun inFlag 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, support.1, support.2,
      entries.1, entries.2, mul_zero, zero_mul, add_zero] at first second
    exact ⟨Int.cast_eq_zero.mp first.symm, Int.cast_eq_zero.mp second.symm⟩
  · rintro ⟨first, second⟩
    refine ⟨1, rfl, fun index => (vector index : ℚ), ?_, ?_⟩
    · exact ⟨by simp only [first, Int.cast_zero], by simp only [second, Int.cast_zero]⟩
    · exact Matrix.one_mulVec _

theorem standardBadLine_not_good : ¬ GoodFlag .line standardBadLine := by
  rintro ⟨vector, integral, nonzero⟩
  have zeroCoordinate := (integralVectorInFlag_standardBadLine vector).mp integral
  exact nonzero (by rw [zeroCoordinate.2]; rfl)

theorem fixedPointLevel_standardBadLine :
    fixedPointLevel rationalLevel standardBadLine =
      rationalLevel ⊓ lineParabolic ℚ := by
  exact congrArg (fun subgroup => rationalLevel ⊓ subgroup)
    (MulAction.stabilizer_quotient (lineParabolic ℚ))

def integralLineLevi (unit : ℤˣ) (binary : GeneralLinearGroup (Fin 2) ℤ)
    (binaryLevel : ∀ column : Fin 2,
      (binary.val 1 column : ZMod 3) = if column = 1 then 1 else 0) : arithmeticLevel :=
  ⟨lineLevi unit binary, by
    change lastRow ᵥ* (reductionThree (lineLevi unit binary)).val = lastRow
    funext column
    simp only [lastRow, single_vecMul, one_smul]
    change ((lineLevi unit binary).val 2 column : ZMod 3) = _
    rw [lineLevi_val]
    fin_cases column
    · rfl
    · change (binary.val 1 0 : ZMod 3) = 0
      simpa using binaryLevel 0
    · change (binary.val 1 1 : ZMod 3) = 1
      simpa using binaryLevel 1⟩

theorem integralLineLevi_rational_mem (unit : ℤˣ)
    (binary : GeneralLinearGroup (Fin 2) ℤ)
    (binaryLevel : ∀ column : Fin 2,
      (binary.val 1 column : ZMod 3) = if column = 1 then 1 else 0) :
    rationalInclusion (integralLineLevi unit binary binaryLevel) ∈
      fixedPointLevel rationalLevel standardBadLine := by
  rw [fixedPointLevel_standardBadLine]
  refine ⟨⟨integralLineLevi unit binary binaryLevel, rfl⟩, ?_⟩
  exact inLine_map (Int.castRingHom ℚ) (lineLevi unit binary)
    (lineLevi_mem unit binary)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
