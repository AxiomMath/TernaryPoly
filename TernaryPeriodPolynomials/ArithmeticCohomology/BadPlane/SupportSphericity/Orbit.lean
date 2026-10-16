module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers

theorem integer_pair_reduction (first second : ℤ) :
    ∃ transform : GeneralLinearGroup (Fin 2) ℤ,
      (![first, second] ᵥ* transform.val) 0 = 0 := by
  by_cases both_zero : first = 0 ∧ second = 0
  · refine ⟨1, ?_⟩
    simp [both_zero.1, both_zero.2]
  let divisor : ℤ := Int.gcd first second
  have divisor_ne : divisor ≠ 0 := by
    change (Int.gcd first second : ℤ) ≠ 0
    exact_mod_cast mt Int.gcd_eq_zero_iff.mp both_zero
  have first_div : first / divisor * divisor = first :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left first second)
  have second_div : second / divisor * divisor = second :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
  have bezout : first / divisor * Int.gcdA first second +
      second / divisor * Int.gcdB first second = 1 := by
    apply mul_right_cancel₀ divisor_ne
    calc
      (first / divisor * Int.gcdA first second +
          second / divisor * Int.gcdB first second) * divisor =
          first * Int.gcdA first second + second * Int.gcdB first second := by
        calc
          _ = (first / divisor * divisor) * Int.gcdA first second +
              (second / divisor * divisor) * Int.gcdB first second := by ring
          _ = _ := by rw [first_div, second_div]
      _ = 1 * divisor := by simpa [divisor] using (Int.gcd_eq_gcd_ab first second).symm
  let transform : GeneralLinearGroup (Fin 2) ℤ :=
    ⟨!![second / divisor, Int.gcdA first second;
        -(first / divisor), Int.gcdB first second],
      !![Int.gcdB first second, -Int.gcdA first second;
        first / divisor, second / divisor], by
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [bezout], by
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [bezout]⟩
  refine ⟨transform, ?_⟩
  dsimp [transform, Matrix.vecMul, dotProduct]
  simp only [Fin.sum_univ_two]
  change first * (second / divisor) + second * (-(first / divisor)) = 0
  apply mul_right_cancel₀ divisor_ne
  calc
    (first * (second / divisor) + second * (-(first / divisor))) * divisor =
        first * (second / divisor * divisor) - second * (first / divisor * divisor) := by ring
    _ = 0 * divisor := by rw [first_div, second_div]; ring

theorem integer_row_reduction (vector : Fin 3 → ℤ) :
    ∃ transform : IntegralGL3,
      (vector ᵥ* transform.val) 0 = 0 ∧ (vector ᵥ* transform.val) 1 = 0 := by
  obtain ⟨first, first_zero⟩ := integer_pair_reduction (vector 0) (vector 1)
  let firstTransform : IntegralGL3 := planeLevi first 1
  let intermediate := vector ᵥ* firstTransform.val
  have intermediate_zero : intermediate 0 = 0 := by
    simpa [intermediate, firstTransform, planeLevi, planeBlock,
      Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      vecHead, vecTail] using first_zero
  obtain ⟨second, second_zero⟩ := integer_pair_reduction (intermediate 1) (intermediate 2)
  refine ⟨firstTransform * lineLevi 1 second, ?_, ?_⟩
  · rw [GeneralLinearGroup.coe_mul, ← vecMul_vecMul]
    change (intermediate ᵥ* (lineLevi 1 second).val) 0 = 0
    simp [lineLevi_val, Matrix.vecMul, dotProduct, Fin.sum_univ_three, intermediate_zero]
  · rw [GeneralLinearGroup.coe_mul, ← vecMul_vecMul]
    change (intermediate ᵥ* (lineLevi 1 second).val) 1 = 0
    simpa [lineLevi_val, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two] using second_zero

theorem rational_row_reduction (vector : Fin 3 → ℚ) :
    ∃ transform : IntegralGL3,
      (vector ᵥ* (integralRational transform).val) 0 = 0 ∧
      (vector ᵥ* (integralRational transform).val) 1 = 0 := by
  let denominator : ℕ := (vector 0).den * (vector 1).den * (vector 2).den
  let integerVector : Fin 3 → ℤ :=
    ![(vector 0).num * (vector 1).den * (vector 2).den,
      (vector 1).num * (vector 0).den * (vector 2).den,
      (vector 2).num * (vector 0).den * (vector 1).den]
  have denominator_ne : (denominator : ℚ) ≠ 0 := by
    simp [denominator]
  have integral_vector (index : Fin 3) :
      (integerVector index : ℚ) = vector index * denominator := by
    fin_cases index <;> dsimp [integerVector, denominator] <;> push_cast
    · rw [← Rat.mul_den_eq_num]; ring
    · rw [← Rat.mul_den_eq_num]; ring
    · rw [← Rat.mul_den_eq_num]; ring
  obtain ⟨transform, first_zero, second_zero⟩ := integer_row_reduction integerVector
  have transfer (index : Fin 3) (zero : (integerVector ᵥ* transform.val) index = 0) :
      (vector ᵥ* (integralRational transform).val) index = 0 := by
    have cast_zero := congrArg (Int.cast : ℤ → ℚ) zero
    simp only [Matrix.vecMul, dotProduct, Int.cast_sum, Int.cast_mul, Int.cast_zero,
      integral_vector] at cast_zero
    apply mul_right_cancel₀ denominator_ne
    calc
      (vector ᵥ* (integralRational transform).val) index * (denominator : ℚ) =
          ∑ row, (vector row * (denominator : ℚ)) * (transform.val row index : ℚ) := by
        simp only [Matrix.vecMul, dotProduct, integralRational,
          GeneralLinearGroup.map_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro row _
        change vector row * (transform.val row index : ℚ) * denominator = _
        ring
      _ = 0 * denominator := by simpa using cast_zero
  exact ⟨transform, transfer 0 first_zero, transfer 1 second_zero⟩

theorem rational_plane_integral_representative (flag : RationalGL3) :
    ∃ transform : IntegralGL3,
      flag⁻¹ * integralRational transform ∈ planeParabolic ℚ := by
  obtain ⟨transform, first_zero, second_zero⟩ :=
    rational_row_reduction (fun column => flag⁻¹.val 2 column)
  refine ⟨transform, ?_, ?_⟩
  · simpa [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.vecMul, dotProduct]
      using first_zero
  · simpa [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.vecMul, dotProduct]
      using second_zero

theorem bad_plane_integral_columns (flag : RationalGL3)
    (bad : ¬ GoodFlag .plane (QuotientGroup.mk flag)) (transform : IntegralGL3)
    (same_flag : flag⁻¹ * integralRational transform ∈ planeParabolic ℚ) :
    (transform.val 2 0 : ZMod 3) = 0 ∧ (transform.val 2 1 : ZMod 3) = 0 := by
  have column_zero (column : Fin 3) (not_last : column ≠ 2) :
      (transform.val 2 column : ZMod 3) = 0 := by
    by_contra nonzero
    apply bad
    refine ⟨fun row => transform.val row column, ?_, nonzero⟩
    refine ⟨integralRational transform, QuotientGroup.eq.mpr same_flag |>.symm,
      Pi.single column 1, ?_, ?_⟩
    · simp [not_last.symm]
    · ext row
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
      rfl
  exact ⟨column_zero 0 (by decide), column_zero 1 (by decide)⟩

theorem bad_plane_arithmetic_representative (flag : RationalGL3)
    (bad : ¬ GoodFlag .plane (QuotientGroup.mk flag)) :
    ∃ transform : arithmeticLevel,
      flag⁻¹ * rationalInclusion transform ∈ planeParabolic ℚ := by
  obtain ⟨integral, same_flag⟩ := rational_plane_integral_representative flag
  obtain ⟨first_zero, second_zero⟩ := bad_plane_integral_columns flag bad integral same_flag
  have last_ne : (integral.val 2 2 : ZMod 3) ≠ 0 := by
    intro zero
    have inverse := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) (ZMod 3) => matrix 2 2)
      (reductionThree integral).val_inv
    change (∑ column, (integral.val 2 column : ZMod 3) *
      (reductionThree integral).inv column 2) = 1 at inverse
    simp [Fin.sum_univ_three, first_zero, second_zero, zero] at inverse
  have last_sign : (integral.val 2 2 : ZMod 3) = 1 ∨
      (integral.val 2 2 : ZMod 3) = -1 := by
    have signs : ∀ value : ZMod 3, value ≠ 0 → value = 1 ∨ value = -1 := by decide
    exact signs _ last_ne
  rcases last_sign with positive | negative
  · refine ⟨⟨integral, ?_⟩, same_flag⟩
    change lastRow ᵥ* (reductionThree integral).val = lastRow
    ext column
    fin_cases column <;>
      simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
        reductionThree, GeneralLinearGroup.map_apply, first_zero, second_zero, positive]
  · let correction : IntegralGL3 := planeLevi 1 (-1)
    have corrected_level : integral * correction ∈ arithmeticLevel := by
      change lastRow ᵥ* (reductionThree (integral * correction)).val = lastRow
      ext column
      fin_cases column <;>
        simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
          reductionThree,
          Matrix.mul_apply, correction, planeLevi, planeBlock,
          first_zero, second_zero, negative]
    refine ⟨⟨integral * correction, corrected_level⟩, ?_⟩
    change flag⁻¹ * integralRational (integral * correction) ∈ planeParabolic ℚ
    rw [map_mul, ← mul_assoc]
    apply (planeParabolic ℚ).mul_mem same_flag
    change InPlaneParabolic (integralRational correction)
    exact ⟨rfl, rfl⟩

end TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers
