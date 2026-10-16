module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.IntegralReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.OrbitInner

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem rationalVector_clear_denominators (vector : Fin 3 → ℚ) :
    ∃ denominator : ℚ, denominator ≠ 0 ∧ ∃ integral : Fin 3 → ℤ,
      ∀ index, denominator * vector index = (integral index : ℚ) := by
  let common : ℕ := (vector 0).den * (vector 1).den * (vector 2).den
  have commonNonzero : common ≠ 0 :=
    mul_ne_zero (mul_ne_zero (vector 0).den_ne_zero (vector 1).den_ne_zero)
      (vector 2).den_ne_zero
  let integral : Fin 3 → ℤ :=
    ![(vector 0).num * (vector 1).den * (vector 2).den,
      (vector 0).den * (vector 1).num * (vector 2).den,
      (vector 0).den * (vector 1).den * (vector 2).num]
  refine ⟨common, by exact_mod_cast commonNonzero, integral, ?_⟩
  intro index
  fin_cases index
  · dsimp [common, integral]
    push_cast
    linear_combination ((vector 1).den : ℚ) * ((vector 2).den : ℚ) *
      Rat.den_mul_eq_num (vector 0)
  · dsimp [common, integral]
    push_cast
    linear_combination ((vector 0).den : ℚ) * ((vector 2).den : ℚ) *
      Rat.den_mul_eq_num (vector 1)
  · dsimp [common, integral]
    push_cast
    linear_combination ((vector 0).den : ℚ) * ((vector 1).den : ℚ) *
      Rat.den_mul_eq_num (vector 2)

theorem rationalLine_has_integral_representative (flag : Flags .line) :
    ∃ integral : IntegralGL3, QuotientGroup.mk (integralRational integral) = flag := by
  refine Quotient.inductionOn' flag ?_
  intro representative
  obtain ⟨denominator, _nonzero, vector, coordinates⟩ :=
    rationalVector_clear_denominators (fun row => representative.val row 0)
  let reduction := integralVectorReduction vector
  refine ⟨reduction⁻¹, QuotientGroup.eq.mpr ?_⟩
  change (integralRational (reduction⁻¹))⁻¹ * representative ∈ lineParabolic ℚ
  rw [map_inv, inv_inv]
  have reduced := integralVectorReduction_mulVec vector
  have mapped : (integralRational reduction).val *ᵥ (fun index => (vector index : ℚ)) =
      fun index => ((reduction.val *ᵥ vector) index : ℚ) := by
    ext index
    exact ((Int.castRingHom ℚ).map_mulVec reduction.val vector index).symm
  have column (row : Fin 3) :
      denominator * ((integralRational reduction).val * representative.val) row 0 =
        ((integralRational reduction).val *ᵥ (fun index => (vector index : ℚ))) row := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _membership
    rw [← coordinates index]
    ring
  constructor
  · have zeroCoordinate := congrFun reduced 1
    change (reduction.val *ᵥ vector) 1 = 0 at zeroCoordinate
    have mappedZero : ((integralRational reduction).val *ᵥ
        (fun index => (vector index : ℚ))) 1 = 0 :=
      (congrFun mapped 1).trans (congrArg (Int.castRingHom ℚ) zeroCoordinate)
    have zeroColumn := (column 1).trans mappedZero
    exact (mul_eq_zero.mp zeroColumn).resolve_left _nonzero
  · have zeroCoordinate := congrFun reduced 2
    change (reduction.val *ᵥ vector) 2 = 0 at zeroCoordinate
    have mappedZero : ((integralRational reduction).val *ᵥ
        (fun index => (vector index : ℚ))) 2 = 0 :=
      (congrFun mapped 2).trans (congrArg (Int.castRingHom ℚ) zeroCoordinate)
    have zeroColumn := (column 2).trans mappedZero
    exact (mul_eq_zero.mp zeroColumn).resolve_left _nonzero

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
