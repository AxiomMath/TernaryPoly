module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers

noncomputable section

theorem map_mulVec_eq {Ring Source : Type} [CommRing Ring] [CommRing Source]
    (hom : Ring →+* Source) (matrix : Matrix (Fin 3) (Fin 3) Ring) (vector : Fin 3 → Ring) :
    (fun index => hom ((matrix *ᵥ vector) index)) =
      matrix.map hom *ᵥ (fun index => hom (vector index)) := by
  funext index
  exact hom.map_mulVec matrix vector index

def localThree {size : ℕ} : GeneralLinearGroup (Fin size) Adeles →*
    GeneralLinearGroup (Fin size) ℚ_[3] :=
  GeneralLinearGroup.map
    (threeCompletionEquiv.toRingHom.comp
      ((finiteEvaluation placeThree).comp (RingHom.snd ℝ FiniteAdeles)))

def LocalGood (matrix : GeneralLinearGroup (Fin 3) ℚ_[3]) : Prop :=
  ∃ vector : Fin 3 → ℤ_[3],
    (matrix.val *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0 ∧
      PadicInt.toZMod (vector 2) ≠ 0

def AdelicGood (matrix : AdelicGL) : Prop := LocalGood (localThree matrix)

theorem reduction_nonzero_iff_unit (value : ℤ_[3]) :
    PadicInt.toZMod value ≠ 0 ↔ IsUnit value := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod]
  rfl

theorem local_good_parabolic {parabolic_matrix matrix : GeneralLinearGroup (Fin 3) ℚ_[3]}
    (parabolic_membership : InPlaneParabolic parabolic_matrix) :
    LocalGood (parabolic_matrix * matrix) ↔ LocalGood matrix := by
  have corner_ne_zero : parabolic_matrix.val 2 2 ≠ 0 := by
    have identity := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℚ_[3] => value 2 2)
      parabolic_matrix.mul_inv
    have corner_identity : parabolic_matrix.val 2 2 * parabolic_matrix.inv 2 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three, parabolic_membership.1,
        parabolic_membership.2] using identity
    exact left_ne_zero_of_mul_eq_one corner_identity
  have kernel (vector : Fin 3 → ℤ_[3]) :
      ((parabolic_matrix * matrix).val *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0 ↔
        (matrix.val *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0 := by
    rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      parabolic_membership.1, parabolic_membership.2, corner_ne_zero]
  constructor
  · rintro ⟨vector, kernel_zero, last_nonzero⟩
    exact ⟨vector, (kernel vector).mp kernel_zero, last_nonzero⟩
  · rintro ⟨vector, kernel_zero, last_nonzero⟩
    exact ⟨vector, (kernel vector).mpr kernel_zero, last_nonzero⟩

theorem local_good_integral {compact : GeneralLinearGroup (Fin 3) ℤ_[3]}
    (compact_row : lastRow ᵥ* (GeneralLinearGroup.map PadicInt.toZMod compact).val = lastRow)
    (matrix : GeneralLinearGroup (Fin 3) ℚ_[3]) :
    LocalGood (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) ↔ LocalGood matrix := by
  have row_entry (index : Fin 3) : PadicInt.toZMod (compact.val 2 index) = lastRow index := by
    have entry := congrFun compact_row index
    simpa [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry
  have last_coordinate (vector : Fin 3 → ℤ_[3]) :
      PadicInt.toZMod ((compact.val *ᵥ vector) 2) = PadicInt.toZMod (vector 2) := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, row_entry]
    simp [lastRow, Fin.sum_univ_three]
  have forward : LocalGood (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) →
      LocalGood matrix := by
    rintro ⟨vector, kernel_zero, last_nonzero⟩
    refine ⟨compact.val *ᵥ vector, ?_, ?_⟩
    · change (matrix.val *ᵥ (fun index => PadicInt.Coe.ringHom ((compact.val *ᵥ vector) index))) 2 = 0
      rw [map_mulVec_eq]
      change (matrix.val *ᵥ (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
        (fun index => (vector index : ℚ_[3]))) 2 = 0
      rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul]
      exact kernel_zero
    · rw [last_coordinate]
      exact last_nonzero
  have inverse_row : lastRow ᵥ* (GeneralLinearGroup.map PadicInt.toZMod compact⁻¹).val = lastRow := by
    have inverse_membership := rowStabilizer.inv_mem compact_row
    change lastRow ᵥ* (((GeneralLinearGroup.map PadicInt.toZMod) compact)⁻¹).val = lastRow at inverse_membership
    simpa only [map_inv] using inverse_membership
  constructor
  · exact forward
  · intro matrix_good
    obtain ⟨vector, kernel_zero, last_nonzero⟩ := matrix_good
    refine ⟨compact.inv *ᵥ vector, ?_, ?_⟩
    · have vector_identity : (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
          (fun index => ((compact.inv *ᵥ vector) index : ℚ_[3])) =
          fun index => (vector index : ℚ_[3]) := by
        change (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
          (fun index => PadicInt.Coe.ringHom (((compact⁻¹).val *ᵥ vector) index)) = _
        rw [map_mulVec_eq]
        change (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
          (GeneralLinearGroup.map PadicInt.Coe.ringHom compact⁻¹).val *ᵥ
          (fun index => (vector index : ℚ_[3])) = _
        rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, ← map_mul,
          mul_inv_cancel, map_one, GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, vector_identity]
      exact kernel_zero
    · have inverse_entry (index : Fin 3) :
          PadicInt.toZMod (compact.inv 2 index) = lastRow index := by
        change lastRow ᵥ* (compact.inv.map PadicInt.toZMod) = lastRow at inverse_row
        have entry := congrFun inverse_row index
        simpa [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, inverse_entry]
      simpa [lastRow, Fin.sum_univ_three] using last_nonzero

theorem local_three_infinity {size : ℕ} (matrix : GeneralLinearGroup (Fin size) ℝ) :
    localThree (atInfinity matrix) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  simp only [localThree, GeneralLinearGroup.map_apply, RingHom.comp_apply,
    RingHom.coe_snd, atInfinity, combineGL, pairMatrix, GeneralLinearGroup.coe_one,
    Matrix.one_apply, apply_ite]
  split_ifs <;> simp

theorem local_three_rational {size : ℕ} (matrix : GeneralLinearGroup (Fin size) ℚ) :
    localThree (GeneralLinearGroup.map rationalAdele matrix) =
      GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) matrix := by
  apply GeneralLinearGroup.ext
  intro row column
  simp only [localThree, GeneralLinearGroup.map_apply, RingHom.comp_apply]
  exact threeCompletion_rational (matrix.val row column)

theorem adelic_good_infinity (base : AdelicGL) (translate : RealGL3) :
    AdelicGood (base * atInfinity translate) ↔ AdelicGood base := by
  simp only [AdelicGood, map_mul, local_three_infinity, mul_one]

theorem adelic_good_left_parabolic {parabolic_matrix base : AdelicGL}
    (membership : InPlaneParabolic parabolic_matrix) :
    AdelicGood (parabolic_matrix * base) ↔ AdelicGood base := by
  simp only [AdelicGood, map_mul]
  apply local_good_parabolic
  constructor
  · simp only [localThree, GeneralLinearGroup.map_apply, membership.1, map_zero]
  · simp only [localThree, GeneralLinearGroup.map_apply, membership.2, map_zero]

theorem adelic_good_binary (binary : BinaryAdelicGL) (base : AdelicGL) :
    AdelicGood (binaryLevi .plane binary * base) ↔ AdelicGood base :=
  adelic_good_left_parabolic (planeLevi_mem binary 1)

theorem local_good_rational_iff (frame : RationalGL3) :
    LocalGood (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) frame⁻¹) ↔
      ∃ vector : Fin 3 → ℤ,
        (frame.inv *ᵥ (fun index => (vector index : ℚ))) 2 = 0 ∧ (vector 2 : ZMod 3) ≠ 0 := by
  constructor
  · rintro ⟨vector, kernel_zero, last_nonzero⟩
    change (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ
      (fun index => (vector index : ℚ_[3]))) 2 = 0 at kernel_zero
    have last_norm : ‖(vector 2 : ℚ_[3])‖ = 1 :=
      PadicInt.isUnit_iff.mp ((reduction_nonzero_iff_unit _).mp last_nonzero)
    let first : ℚ := frame.inv 2 0
    let second : ℚ := frame.inv 2 1
    let last : ℚ := frame.inv 2 2
    have equation : (first : ℚ_[3]) * vector 0 + (second : ℚ_[3]) * vector 1 =
        -(last : ℚ_[3]) * vector 2 := by
      have rational_cast (value : ℚ) : (algebraMap ℚ ℚ_[3]) value = (value : ℚ_[3]) :=
        map_ratCast (algebraMap ℚ ℚ_[3]) value
      have expanded : (first : ℚ_[3]) * vector 0 + (second : ℚ_[3]) * vector 1 +
          (last : ℚ_[3]) * vector 2 = 0 := by
        simpa only [first, second, last, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          Matrix.map_apply, rational_cast] using kernel_zero
      linear_combination expanded
    have bound : ‖(last : ℚ_[3])‖ ≤ max ‖(first : ℚ_[3])‖ ‖(second : ℚ_[3])‖ := by
      calc
        ‖(last : ℚ_[3])‖ = ‖-(last : ℚ_[3]) * vector 2‖ := by
          rw [norm_mul, norm_neg, last_norm, mul_one]
        _ = ‖(first : ℚ_[3]) * vector 0 + (second : ℚ_[3]) * vector 1‖ :=
          congrArg norm equation.symm
        _ ≤ max ‖(first : ℚ_[3]) * vector 0‖ ‖(second : ℚ_[3]) * vector 1‖ :=
          Padic.nonarchimedean _ _
        _ ≤ max ‖(first : ℚ_[3])‖ ‖(second : ℚ_[3])‖ := by
          apply max_le_max
          all_goals rw [norm_mul]
          · exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
          · exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
    have construction (coefficient : ℚ) (coefficient_ne_zero : coefficient ≠ 0)
        (coefficient_bound : ‖(last : ℚ_[3])‖ ≤ ‖(coefficient : ℚ_[3])‖) :
        ∃ numerator : ℤ, ∃ denominator : ℕ,
          (denominator : ZMod 3) ≠ 0 ∧
            coefficient * numerator + last * denominator = 0 := by
      let ratio : ℚ := -last / coefficient
      have coefficient_cast_ne_zero : (coefficient : ℚ_[3]) ≠ 0 := by exact_mod_cast coefficient_ne_zero
      have ratio_integral : ‖(ratio : ℚ_[3])‖ ≤ 1 := by
        simp only [ratio, Rat.cast_div, Rat.cast_neg, norm_div, norm_neg]
        exact (div_le_one (norm_pos_iff.mpr coefficient_cast_ne_zero)).mpr coefficient_bound
      have denominator_not_divisible : ¬3 ∣ ratio.den :=
        Rat.padicValuation_le_one_iff.mp
          ((Padic.norm_rat_le_one_iff_padicValuation_le_one 3).mp ratio_integral)
      refine ⟨ratio.num, ratio.den, ?_, ?_⟩
      · intro denominator_zero
        exact denominator_not_divisible
          ((ZMod.natCast_eq_zero_iff _ _).mp denominator_zero)
      · have ratio_identity := Rat.mul_den_eq_num ratio
        have ratio_equation : ratio * coefficient = -last := by
          dsimp [ratio]
          field_simp
        linear_combination -coefficient * ratio_identity + (ratio.den : ℚ) * ratio_equation
    by_cases first_zero : first = 0
    · have second_ne_zero : second ≠ 0 := by
        intro second_zero
        have last_zero : last = 0 := by
          have cast_zero : (last : ℚ_[3]) = 0 := by
            apply norm_eq_zero.mp
            apply le_antisymm _ (norm_nonneg _)
            simpa only [first_zero, second_zero, Rat.cast_zero, norm_zero, max_self] using bound
          exact_mod_cast cast_zero
        have identity := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℚ => value 2 2) frame.inv_mul
        change (frame.inv * frame.val) 2 2 = 1 at identity
        simp only [Matrix.mul_apply, Fin.sum_univ_three] at identity
        change first * frame.val 0 2 + second * frame.val 1 2 + last * frame.val 2 2 = 1 at identity
        simp only [first_zero, second_zero, last_zero, zero_mul, add_zero, zero_ne_one] at identity
      obtain ⟨numerator, denominator, denominator_nonzero, identity⟩ :=
        construction second second_ne_zero (by
          simpa only [first_zero, Rat.cast_zero, norm_zero, max_eq_right (norm_nonneg _)] using bound)
      refine ⟨![0, numerator, denominator], ?_, denominator_nonzero⟩
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first_zero,
        first, second, last] using identity
    · by_cases maximum : ‖(second : ℚ_[3])‖ ≤ ‖(first : ℚ_[3])‖
      · obtain ⟨numerator, denominator, denominator_nonzero, identity⟩ :=
          construction first first_zero (by simpa only [max_eq_left maximum] using bound)
        refine ⟨![numerator, 0, denominator], ?_, denominator_nonzero⟩
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first, second, last] using identity
      · have second_ne_zero : second ≠ 0 := by
          intro second_zero
          exact maximum (by simpa only [second_zero, Rat.cast_zero, norm_zero] using norm_nonneg (first : ℚ_[3]))
        obtain ⟨numerator, denominator, denominator_nonzero, identity⟩ :=
          construction second second_ne_zero
            (by simpa only [max_eq_right (le_of_lt (lt_of_not_ge maximum))] using bound)
        refine ⟨![0, numerator, denominator], ?_, denominator_nonzero⟩
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first, second, last] using identity
  · rintro ⟨vector, kernel_zero, last_nonzero⟩
    refine ⟨fun index => (vector index : ℤ_[3]), ?_, ?_⟩
    · change (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ
        (fun index => ((vector index : ℤ_[3]) : ℚ_[3]))) 2 = 0
      have cast_integer (value : ℤ) :
          (algebraMap ℚ ℚ_[3]) (value : ℚ) = ((value : ℤ_[3]) : ℚ_[3]) := by
        simp
      simpa only [RingHom.map_mulVec, Function.comp_def, cast_integer, map_zero]
        using congrArg (algebraMap ℚ ℚ_[3]) kernel_zero
    · simpa only [map_intCast] using last_nonzero

theorem good_flag_kernel_iff (frame : RationalGL3) :
    GoodFlag .plane (QuotientGroup.mk frame) ↔
      ∃ vector : Fin 3 → ℤ,
        (frame.inv *ᵥ (fun index => (vector index : ℚ))) 2 = 0 ∧ (vector 2 : ZMod 3) ≠ 0 := by
  constructor
  · rintro ⟨vector, ⟨other_frame, flag_equality, coordinates, coordinates_last, vector_equality⟩,
      last_nonzero⟩
    refine ⟨vector, ?_, last_nonzero⟩
    have relative_membership : frame⁻¹ * other_frame ∈ parabolic .plane :=
      QuotientGroup.eq.mp flag_equality.symm
    have first_zero : (frame.inv * other_frame.val) 2 0 = 0 := relative_membership.1
    have second_zero : (frame.inv * other_frame.val) 2 1 = 0 := relative_membership.2
    change ((frame⁻¹).val *ᵥ (fun index => (vector index : ℚ))) 2 = 0
    rw [← vector_equality, Matrix.mulVec_mulVec]
    change ((frame.inv * other_frame.val) *ᵥ coordinates) 2 = 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      first_zero, second_zero, zero_mul, zero_add, coordinates_last, mul_zero]
  · rintro ⟨vector, kernel_zero, last_nonzero⟩
    refine ⟨vector, ⟨frame, rfl, frame.inv *ᵥ (fun index => (vector index : ℚ)), kernel_zero, ?_⟩,
      last_nonzero⟩
    change frame.val *ᵥ (frame⁻¹).val *ᵥ (fun index => (vector index : ℚ)) = _
    rw [Matrix.mulVec_mulVec, frame.mul_inv, Matrix.one_mulVec]

theorem adelic_good_rational (frame : RationalGL3) :
    AdelicGood (rationalGroup frame⁻¹) ↔ GoodFlag .plane (QuotientGroup.mk frame) := by
  change LocalGood (localThree (GeneralLinearGroup.map rationalAdele frame⁻¹)) ↔ _
  rw [local_three_rational, local_good_rational_iff, good_flag_kernel_iff]

end

end TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers
