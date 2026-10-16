module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.BoundarySupport

@[expose] public section


/-!
# Cutting a line source by the goodness of its flag

The goodness of a rational line flag is a condition at the place three that is invariant under the
line parabolic on the left and the level subgroup on the right.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers
open TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits

namespace TernaryPeriodPolynomials.Separation

/-- The three-adic line goodness of a matrix. -/
def LocalGoodLine (matrix : GeneralLinearGroup (Fin 3) ℚ_[3]) : Prop :=
  ∃ vector : Fin 3 → ℤ_[3],
    (matrix.val *ᵥ (fun index => (vector index : ℚ_[3]))) 1 = 0 ∧
    (matrix.val *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0 ∧
      PadicInt.toZMod (vector 2) ≠ 0

/-- The adelic line goodness. -/
def AdelicGoodLine (matrix : AdelicGL) : Prop := LocalGoodLine (localThree matrix)

theorem inLine_mulVec_zero {R : Type*} [CommRing R] {p : GL3 R} (hp : InLineParabolic p)
    {y : Fin 3 → R} (h1 : y 1 = 0) (h2 : y 2 = 0) :
    (p.val *ᵥ y) 1 = 0 ∧ (p.val *ᵥ y) 2 = 0 := by
  constructor <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp.1, hp.2, h1, h2]

theorem inLine_mulVec_zero_iff {R : Type*} [CommRing R] {p : GL3 R} (hp : InLineParabolic p)
    (y : Fin 3 → R) :
    ((p.val *ᵥ y) 1 = 0 ∧ (p.val *ᵥ y) 2 = 0) ↔ (y 1 = 0 ∧ y 2 = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    have := inLine_mulVec_zero (inLine_inv hp) h1 h2
    rwa [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
      GeneralLinearGroup.coe_one, Matrix.one_mulVec] at this
  · rintro ⟨h1, h2⟩
    exact inLine_mulVec_zero hp h1 h2

theorem local_good_line_parabolic {p matrix : GeneralLinearGroup (Fin 3) ℚ_[3]}
    (hp : InLineParabolic p) : LocalGoodLine (p * matrix) ↔ LocalGoodLine matrix := by
  have kernel (vector : Fin 3 → ℤ_[3]) :
      (((p * matrix).val *ᵥ (fun index => (vector index : ℚ_[3]))) 1 = 0 ∧
        ((p * matrix).val *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0) ↔
      ((matrix.val *ᵥ (fun index => (vector index : ℚ_[3]))) 1 = 0 ∧
        (matrix.val *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0) := by
    rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    exact inLine_mulVec_zero_iff hp _
  constructor
  · rintro ⟨vector, h1, h2, h3⟩
    exact ⟨vector, ((kernel vector).mp ⟨h1, h2⟩).1, ((kernel vector).mp ⟨h1, h2⟩).2, h3⟩
  · rintro ⟨vector, h1, h2, h3⟩
    exact ⟨vector, ((kernel vector).mpr ⟨h1, h2⟩).1, ((kernel vector).mpr ⟨h1, h2⟩).2, h3⟩

theorem local_good_line_integral {compact : GeneralLinearGroup (Fin 3) ℤ_[3]}
    (compact_row : lastRow ᵥ* (GeneralLinearGroup.map PadicInt.toZMod compact).val = lastRow)
    (matrix : GeneralLinearGroup (Fin 3) ℚ_[3]) :
    LocalGoodLine (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) ↔
      LocalGoodLine matrix := by
  have row_entry (index : Fin 3) : PadicInt.toZMod (compact.val 2 index) = lastRow index := by
    have entry := congrFun compact_row index
    simpa [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry
  have last_coordinate (vector : Fin 3 → ℤ_[3]) :
      PadicInt.toZMod ((compact.val *ᵥ vector) 2) = PadicInt.toZMod (vector 2) := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, row_entry]
    simp [lastRow, Fin.sum_univ_three]
  have image (vector : Fin 3 → ℤ_[3]) :
      (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
          (fun index => (vector index : ℚ_[3])) =
        fun index => ((compact.val *ᵥ vector) index : ℚ_[3]) := by
    change (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
      (fun index => PadicInt.Coe.ringHom (vector index)) =
        fun index => PadicInt.Coe.ringHom ((compact.val *ᵥ vector) index)
    exact (map_mulVec_eq PadicInt.Coe.ringHom compact.val vector).symm
  have forward : LocalGoodLine (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) →
      LocalGoodLine matrix := by
    rintro ⟨vector, h1, h2, h3⟩
    rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, image] at h1 h2
    exact ⟨compact.val *ᵥ vector, h1, h2, by rw [last_coordinate]; exact h3⟩
  have inverse_row : lastRow ᵥ* (GeneralLinearGroup.map PadicInt.toZMod compact⁻¹).val = lastRow := by
    have inverse_membership := rowStabilizer.inv_mem compact_row
    change lastRow ᵥ* (((GeneralLinearGroup.map PadicInt.toZMod) compact)⁻¹).val = lastRow
      at inverse_membership
    simpa only [map_inv] using inverse_membership
  refine ⟨forward, ?_⟩
  rintro ⟨vector, h1, h2, h3⟩
  have inverse_entry (index : Fin 3) :
      PadicInt.toZMod (compact.inv 2 index) = lastRow index := by
    change lastRow ᵥ* (compact.inv.map PadicInt.toZMod) = lastRow at inverse_row
    have entry := congrFun inverse_row index
    simpa [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry
  have vector_identity : (GeneralLinearGroup.map PadicInt.Coe.ringHom compact).val *ᵥ
      (fun index => ((compact.inv *ᵥ vector) index : ℚ_[3])) =
      fun index => (vector index : ℚ_[3]) := by
    rw [image, Matrix.mulVec_mulVec, compact.val_inv, Matrix.one_mulVec]
  refine ⟨compact.inv *ᵥ vector, ?_, ?_, ?_⟩
  · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, vector_identity]
    exact h1
  · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, vector_identity]
    exact h2
  · simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, inverse_entry]
    simpa [lastRow, Fin.sum_univ_three] using h3

attribute [local instance] Classical.propDecidable

theorem local_good_line_rational_iff (frame : RationalGL3) :
    LocalGoodLine (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) frame⁻¹) ↔
      ∃ vector : Fin 3 → ℤ,
        (frame.inv *ᵥ (fun index => (vector index : ℚ))) 1 = 0 ∧
        (frame.inv *ᵥ (fun index => (vector index : ℚ))) 2 = 0 ∧ (vector 2 : ZMod 3) ≠ 0 := by
  constructor
  · rintro ⟨vector, kernel_one, kernel_two, last_nonzero⟩
    change (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun index => (vector index : ℚ_[3]))) 1 = 0
      at kernel_one
    change (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun index => (vector index : ℚ_[3]))) 2 = 0
      at kernel_two
    have rational_cast (value : ℚ) : (algebraMap ℚ ℚ_[3]) value = (value : ℚ_[3]) :=
      map_ratCast (algebraMap ℚ ℚ_[3]) value
    have product : frame.val.map (algebraMap ℚ ℚ_[3]) * frame.inv.map (algebraMap ℚ ℚ_[3]) = 1 := by
      rw [← Matrix.map_mul, frame.val_inv]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have recover : (fun index => (vector index : ℚ_[3])) =
        frame.val.map (algebraMap ℚ ℚ_[3]) *ᵥ
          (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun index => (vector index : ℚ_[3]))) := by
      rw [Matrix.mulVec_mulVec, product, Matrix.one_mulVec]
    generalize (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun index => (vector index : ℚ_[3]))) = y
      at kernel_one kernel_two recover
    have entry (index : Fin 3) :
        (vector index : ℚ_[3]) = ((frame.val index 0 : ℚ) : ℚ_[3]) * y 0 := by
      have equation := congrFun recover index
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.map_apply, rational_cast,
        kernel_one, kernel_two, mul_zero, add_zero] at equation
      exact equation
    have last_norm : ‖(vector 2 : ℚ_[3])‖ = 1 :=
      PadicInt.isUnit_iff.mp ((reduction_nonzero_iff_unit _).mp last_nonzero)
    have last_ne_zero : (vector 2 : ℚ_[3]) ≠ 0 := by
      intro zero
      rw [zero, norm_zero] at last_norm
      exact zero_ne_one last_norm
    have corner_ne_zero : (frame.val 2 0 : ℚ) ≠ 0 := by
      intro zero
      apply last_ne_zero
      rw [entry 2, zero, Rat.cast_zero, zero_mul]
    have scale_ne_zero : y 0 ≠ 0 := by
      intro zero
      apply last_ne_zero
      rw [entry 2, zero, mul_zero]
    have ratio_bound (index : Fin 3) :
        ‖((frame.val index 0 / frame.val 2 0 : ℚ) : ℚ_[3])‖ ≤ 1 := by
      have quotient : ((frame.val index 0 / frame.val 2 0 : ℚ) : ℚ_[3]) =
          (vector index : ℚ_[3]) / (vector 2 : ℚ_[3]) := by
        rw [Rat.cast_div, entry index, entry 2]
        exact (mul_div_mul_right _ _ scale_ne_zero).symm
      rw [quotient, norm_div, last_norm, div_one]
      exact PadicInt.norm_le_one _
    have denominator_free (value : ℚ) (bound : ‖(value : ℚ_[3])‖ ≤ 1) : ¬3 ∣ value.den :=
      Rat.padicValuation_le_one_iff.mp
        ((Padic.norm_rat_le_one_iff_padicValuation_le_one 3).mp bound)
    obtain ⟨first, first_def⟩ : ∃ ratio : ℚ, ratio = frame.val 0 0 / frame.val 2 0 := ⟨_, rfl⟩
    obtain ⟨second, second_def⟩ : ∃ ratio : ℚ, ratio = frame.val 1 0 / frame.val 2 0 := ⟨_, rfl⟩
    have first_bound : ‖(first : ℚ_[3])‖ ≤ 1 := by
      rw [first_def]
      exact ratio_bound 0
    have second_bound : ‖(second : ℚ_[3])‖ ≤ 1 := by
      rw [second_def]
      exact ratio_bound 1
    have first_free := denominator_free first first_bound
    have second_free := denominator_free second second_bound
    have first_eq : frame.val 0 0 = first * frame.val 2 0 := by
      rw [first_def]
      field_simp
    have second_eq : frame.val 1 0 = second * frame.val 2 0 := by
      rw [second_def]
      field_simp
    have first_num : (first.num : ℚ) = first * first.den := (Rat.mul_den_eq_num first).symm
    have second_num : (second.num : ℚ) = second * second.den := (Rat.mul_den_eq_num second).symm
    obtain ⟨factor, factor_def⟩ : ∃ factor : ℚ,
        factor = ((first.den : ℚ) * second.den) / frame.val 2 0 := ⟨_, rfl⟩
    have factor_eq : factor * frame.val 2 0 = (first.den : ℚ) * second.den := by
      rw [factor_def]
      field_simp
    have vector_cast : (fun index => ((![(second.den : ℤ) * first.num,
        (first.den : ℤ) * second.num, (first.den : ℤ) * second.den] index : ℤ) : ℚ)) =
        fun index => factor * frame.val index 0 := by
      funext index
      fin_cases index
      · change (((second.den : ℤ) * first.num : ℤ) : ℚ) = factor * frame.val 0 0
        push_cast
        rw [first_num]
        linear_combination (-factor) * first_eq + (-first) * factor_eq
      · change (((first.den : ℤ) * second.num : ℤ) : ℚ) = factor * frame.val 1 0
        push_cast
        rw [second_num]
        linear_combination (-factor) * second_eq + (-second) * factor_eq
      · change (((first.den : ℤ) * second.den : ℤ) : ℚ) = factor * frame.val 2 0
        push_cast
        exact factor_eq.symm
    have inverse_column (row : Fin 3) (zero : row ≠ 0) :
        frame.inv row 0 * frame.val 0 0 + frame.inv row 1 * frame.val 1 0 +
          frame.inv row 2 * frame.val 2 0 = 0 := by
      have identity := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℚ => value row 0)
        frame.inv_val
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, zero] using identity
    refine ⟨![(second.den : ℤ) * first.num, (first.den : ℤ) * second.num,
      (first.den : ℤ) * second.den], ?_, ?_, ?_⟩
    · rw [vector_cast]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination factor * inverse_column 1 (by decide)
    · rw [vector_cast]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination factor * inverse_column 2 (by decide)
    · intro vanishing
      have natural : (((first.den * second.den : ℕ)) : ZMod 3) = 0 := by
        simpa using vanishing
      have divisible : 3 ∣ first.den * second.den := (ZMod.natCast_eq_zero_iff _ _).mp natural
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp divisible with divisible | divisible
      · exact first_free divisible
      · exact second_free divisible
  · rintro ⟨vector, kernel_one, kernel_two, last_nonzero⟩
    have cast_integer (value : ℤ) :
        (algebraMap ℚ ℚ_[3]) (value : ℚ) = ((value : ℤ_[3]) : ℚ_[3]) := by
      simp
    have transfer (row : Fin 3)
        (kernel : (frame.inv *ᵥ (fun index => (vector index : ℚ))) row = 0) :
        (frame.inv.map (algebraMap ℚ ℚ_[3]) *ᵥ
          (fun index => ((vector index : ℤ_[3]) : ℚ_[3]))) row = 0 := by
      simpa only [RingHom.map_mulVec, Function.comp_def, cast_integer, map_zero]
        using congrArg (algebraMap ℚ ℚ_[3]) kernel
    refine ⟨fun index => (vector index : ℤ_[3]), transfer 1 kernel_one, transfer 2 kernel_two, ?_⟩
    simpa only [map_intCast] using last_nonzero

theorem good_flag_line_kernel_iff (frame : RationalGL3) :
    GoodFlag .line (QuotientGroup.mk frame) ↔
      ∃ vector : Fin 3 → ℤ,
        (frame.inv *ᵥ (fun index => (vector index : ℚ))) 1 = 0 ∧
        (frame.inv *ᵥ (fun index => (vector index : ℚ))) 2 = 0 ∧ (vector 2 : ZMod 3) ≠ 0 := by
  constructor
  · rintro ⟨vector, ⟨other_frame, flag_equality, coordinates, ⟨first_zero, second_zero⟩,
      vector_equality⟩, last_nonzero⟩
    have relative_membership : frame⁻¹ * other_frame ∈ parabolic .line :=
      QuotientGroup.eq.mp flag_equality.symm
    have row_one : (frame.inv * other_frame.val) 1 0 = 0 := relative_membership.1
    have row_two : (frame.inv * other_frame.val) 2 0 = 0 := relative_membership.2
    have transported : frame.inv *ᵥ (fun index => (vector index : ℚ)) =
        (frame.inv * other_frame.val) *ᵥ coordinates := by
      rw [← vector_equality, Matrix.mulVec_mulVec]
    refine ⟨vector, ?_, ?_, last_nonzero⟩
    · rw [transported]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, row_one, first_zero,
        second_zero, zero_mul, mul_zero, add_zero]
    · rw [transported]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, row_two, first_zero,
        second_zero, zero_mul, mul_zero, add_zero]
  · rintro ⟨vector, kernel_one, kernel_two, last_nonzero⟩
    refine ⟨vector, ⟨frame, rfl, frame.inv *ᵥ (fun index => (vector index : ℚ)),
      ⟨kernel_one, kernel_two⟩, ?_⟩, last_nonzero⟩
    change frame.val *ᵥ (frame⁻¹).val *ᵥ (fun index => (vector index : ℚ)) = _
    rw [Matrix.mulVec_mulVec, frame.mul_inv, Matrix.one_mulVec]

/-- Line goodness of a rational point is goodness of the corresponding line flag. -/
theorem adelic_good_line_rational (frame : RationalGL3) :
    AdelicGoodLine (rationalGroup frame⁻¹) ↔ GoodFlag .line (QuotientGroup.mk frame) := by
  change LocalGoodLine (localThree (GeneralLinearGroup.map rationalAdele frame⁻¹)) ↔ _
  rw [local_three_rational, local_good_line_rational_iff, good_flag_line_kernel_iff]

theorem adelic_good_line_infinity (base : AdelicGL) (translate : RealGL3) :
    AdelicGoodLine (base * atInfinity translate) ↔ AdelicGoodLine base := by
  simp only [AdelicGoodLine, map_mul, local_three_infinity, mul_one]

theorem adelic_good_line_left_parabolic {parabolic_matrix base : AdelicGL}
    (membership : InLineParabolic parabolic_matrix) :
    AdelicGoodLine (parabolic_matrix * base) ↔ AdelicGoodLine base := by
  simp only [AdelicGoodLine, map_mul]
  apply local_good_line_parabolic
  constructor
  · simp only [localThree, GeneralLinearGroup.map_apply, membership.1, map_zero]
  · simp only [localThree, GeneralLinearGroup.map_apply, membership.2, map_zero]

theorem adelic_good_line_finite (compact : finiteLevel) (base : AdelicGL) :
    AdelicGoodLine (base * atFinite compact.val) ↔ AdelicGoodLine base := by
  obtain ⟨integral, integral_membership, integral_equality⟩ := compact.property
  have row : lastRow ᵥ*
      (GeneralLinearGroup.map PadicInt.toZMod (GeneralLinearGroup.map integralThree integral)).val =
        lastRow := by
    rw [integral_three_reduction]
    exact integral_membership
  simp only [AdelicGoodLine, map_mul]
  rw [← integral_equality, local_three_integral]
  exact local_good_line_integral row (localThree base)

/-- The adelic condition keeping the points whose line goodness is `keep`. -/
def LineKeep (keep : Bool) (base : AdelicGL) : Prop :=
  AdelicGoodLine base ↔ keep = true

theorem lineKeep_infinity (keep : Bool) (base : AdelicGL) (translate : RealGL3) :
    LineKeep keep (base * atInfinity translate) ↔ LineKeep keep base := by
  simp only [LineKeep, adelic_good_line_infinity]

theorem lineKeep_finite (keep : Bool) (compact : finiteLevel) (base : AdelicGL) :
    LineKeep keep (base * atFinite compact.val) ↔ LineKeep keep base := by
  simp only [LineKeep, adelic_good_line_finite]

theorem lineKeep_parabolic (keep : Bool) {parabolic_matrix : AdelicGL}
    (membership : InLineParabolic parabolic_matrix) (base : AdelicGL) :
    LineKeep keep (parabolic_matrix * base) ↔ LineKeep keep base := by
  simp only [LineKeep, adelic_good_line_left_parabolic membership]

theorem lineLevi_in {R : Type*} [CommRing R] (scalar : Rˣ) (matrix : GeneralLinearGroup (Fin 2) R) :
    InLineParabolic (lineLevi scalar matrix) := lineLevi_mem scalar matrix

theorem lineKeep_binary (keep : Bool) (binary : BinaryAdelicGL) (base : AdelicGL) :
    LineKeep keep (binaryLevi .line binary * base) ↔ LineKeep keep base :=
  lineKeep_parabolic keep (lineLevi_in 1 binary) base

theorem good_flag_line_arithmetic (translate : arithmeticLevel) {flag : Flags .line}
    (flag_good : GoodFlag .line flag) :
    GoodFlag .line (rationalInclusion translate • flag) := by
  obtain ⟨vector, ⟨frame, frame_flag, coordinates, coordinates_last, vector_eq⟩,
    last_nonzero⟩ := flag_good
  refine ⟨translate.val.val *ᵥ vector,
    ⟨rationalInclusion translate * frame, ?_, coordinates, coordinates_last, ?_⟩, ?_⟩
  · rw [← frame_flag]
    rfl
  · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, vector_eq]
    change (translate.val.val.map (Int.castRingHom ℚ)) *ᵥ
      (fun index => (vector index : ℚ)) = _
    exact (map_mulVec_eq (Int.castRingHom ℚ) translate.val.val vector).symm
  · have row : lastRow ᵥ* (reductionThree translate.val).val = lastRow := translate.property
    have row_entry (index : Fin 3) :
        (translate.val.val 2 index : ZMod 3) = lastRow index := by
      have entry := congrFun row index
      simpa [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
        reductionThree, GeneralLinearGroup.map_apply] using entry
    simpa [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, row_entry,
      lastRow, Fin.sum_univ_three] using last_nonzero

theorem good_flag_line_level_forward (translate : rationalLevel) {flag : Flags .line}
    (flag_good : GoodFlag .line flag) : GoodFlag .line (translate.val • flag) := by
  obtain ⟨integral, integral_eq⟩ := translate.property
  rw [← integral_eq]
  exact good_flag_line_arithmetic integral flag_good

theorem good_flag_line_level (translate : rationalLevel) (flag : Flags .line) :
    GoodFlag .line (translate.val • flag) ↔ GoodFlag .line flag := by
  constructor
  · intro flag_good
    simpa only [Subgroup.coe_inv, inv_smul_smul] using
      good_flag_line_level_forward translate⁻¹ flag_good
  · exact good_flag_line_level_forward translate

/-- Keep the values of a line cochain at the flags of goodness `keep`, kill the others. -/
def lineFlagCut (keep : Bool) {degree : ℕ} {character : RankOneCharacter}
    (arity : ℕ) (cochain : MaximalCochains degree character .line arity) :
    MaximalCochains degree character .line arity :=
  ⟨fun coordinates flag =>
    if GoodFlag .line flag then
      if keep then cochain.val coordinates flag else 0
    else if keep then 0 else cochain.val coordinates flag, by
    intro translate coordinates
    funext flag
    change (if GoodFlag .line flag then
      if keep then cochain.val (fun index => translate.val * coordinates index) flag else 0
      else if keep then 0 else
        cochain.val (fun index => translate.val * coordinates index) flag) =
      rationalCoefficientComponent degree character translate.val
        (if GoodFlag .line (translate.val⁻¹ • flag) then
          if keep then cochain.val coordinates (translate.val⁻¹ • flag) else 0
          else if keep then 0 else cochain.val coordinates (translate.val⁻¹ • flag))
    have invariance := good_flag_line_level translate⁻¹ flag
    rw [Subgroup.coe_inv] at invariance
    rw [invariance]
    have equivariance := congrFun (cochain.property translate coordinates) flag
    change cochain.val (fun index => translate.val * coordinates index) flag =
      rationalCoefficientComponent degree character translate.val
        (cochain.val coordinates (translate.val⁻¹ • flag)) at equivariance
    split_ifs <;> simp only [map_zero, equivariance]⟩

/-- The two-cocycle cut by flag goodness. -/
def lineFlagCutCycle (keep : Bool) {degree : ℕ} {character : RankOneCharacter}
    (cycle : MaximalCycles degree character .line) : MaximalCycles degree character .line :=
  ⟨lineFlagCut keep 2 cycle.val, by
    have cycle_closed := cycle.property
    change differentialTwo rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line) cycle.val = 0
      at cycle_closed
    change differentialTwo rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line)
      (lineFlagCut keep 2 cycle.val) = 0
    funext coordinates flag
    have closed_value := congrFun (congrFun cycle_closed coordinates) flag
    cases keep <;> by_cases flag_good : GoodFlag .line flag
    · simp [lineFlagCut, differentialTwo, flag_good]
    · simpa [lineFlagCut, differentialTwo, flag_good] using closed_value
    · simpa [lineFlagCut, differentialTwo, flag_good] using closed_value
    · simp [lineFlagCut, differentialTwo, flag_good]⟩

/-- Keep the values at the adelic points whose line goodness is `keep`, kill the others. -/
def lineCut {Vector : Type} [Zero Vector] (keep : Bool) (family : AdelicGL → Vector)
    (base : AdelicGL) : Vector :=
  if LineKeep keep base then family base else 0

theorem line_cut_smooth_cusp_lift {degree arity : ℕ} {data : InducingData degree}
    {parameter : ℂ} {family : (Fin arity → RealGL3) → AdelicGL → ℂ} (keep : Bool)
    (family_lift : HasSmoothCuspLift data .line parameter family) :
    HasSmoothCuspLift data .line parameter
      (fun coordinates => lineCut keep (family coordinates)) := by
  intro base
  by_cases base_keep : LineKeep keep base
  · obtain ⟨vector, vector_smooth, evaluation⟩ := family_lift base
    refine ⟨vector, vector_smooth, ?_⟩
    intro coordinates binary
    simp only [lineCut, lineKeep_binary, lineKeep_infinity, ite_eq_left base_keep]
    exact evaluation coordinates binary
  · refine ⟨0, smooth_zero, ?_⟩
    intro coordinates binary
    simp only [Pi.zero_apply, map_zero, lineKeep_binary, lineCut, lineKeep_infinity,
      ite_eq_right base_keep, mul_zero]

theorem line_cut_induced {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    (keep : Bool) {family : AdelicGL → ℂ}
    (family_induced : IsInduced data .line parameter family) :
    IsInduced data .line parameter (lineCut keep family) := by
  obtain ⟨family_smooth, family_invariant, family_lift, family_radical,
    family_character, family_cusp⟩ := family_induced
  refine ⟨?_, ?_, line_cut_smooth_cusp_lift keep family_lift, ?_, ?_, ?_⟩
  · intro base
    simp only [lineCut, lineKeep_infinity]
    by_cases base_keep : LineKeep keep base
    · simpa only [ite_eq_left base_keep] using family_smooth base
    · simp only [ite_eq_right base_keep]
      exact smooth_zero
  · intro compact base
    simp only [lineCut, lineKeep_finite, family_invariant]
  · intro first second base
    have membership : InLineParabolic (lineUnipotent first second) := by
      simp [InLineParabolic, lineUnipotent, upperUnipotent]
    simp only [lineCut, lineKeep_parabolic keep membership, family_radical]
  · intro scalar base
    simp only [lineCut, lineKeep_parabolic keep (lineLevi_in scalar 1), family_character]
    split_ifs <;> simp
  · intro base
    by_cases base_keep : LineKeep keep base
    · simpa only [lineCut, lineKeep_parabolic keep (lineLevi_in _ _),
        ite_eq_left base_keep] using family_cusp base
    · simpa only [lineCut, lineKeep_parabolic keep (lineLevi_in _ _),
        ite_eq_right base_keep, mul_zero, Pi.zero_def] using
        (cuspFunctions data.cusp).zero_mem

/-- The source cocycle cut by the line goodness `keep` at the place three. -/
def lineSource {degree : ℕ} (keep : Bool) (source : SourceCochain degree) :
    SourceCochain degree :=
  fun coordinates => lineCut keep (source coordinates)

theorem line_source_cocycle {degree : ℕ} {data : InducingData degree} (keep : Bool)
    {source : SourceCochain degree} (source_closed : IsSourceCocycle data .line source) :
    IsSourceCocycle data .line (lineSource keep source) := by
  obtain ⟨source_induced, source_lift, source_equivariant, source_cycle⟩ := source_closed
  have coefficient (coordinates : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
      (fun base => ((lineSource keep source) coordinates base).val.coeff monomial) =
        lineCut keep (fun base => (source coordinates base).val.coeff monomial) := by
    funext base
    simp only [lineSource, lineCut]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coordinates monomial
    rw [coefficient]
    exact line_cut_induced keep (source_induced coordinates monomial)
  · intro monomial
    have family_equality :
        (fun coordinates base =>
          ((lineSource keep source) coordinates base).val.coeff monomial) =
          fun coordinates => lineCut keep
            (fun base => (source coordinates base).val.coeff monomial) := by
      funext coordinates
      exact coefficient coordinates monomial
    rw [family_equality]
    exact line_cut_smooth_cusp_lift keep (source_lift monomial)
  · intro translate coordinates base
    simp only [lineSource, lineCut, lineKeep_infinity]
    split_ifs <;> simp only [map_zero, source_equivariant]
  · intro coordinates base
    simp only [lineSource, lineCut]
    split_ifs
    · exact source_cycle coordinates base
    · simp

theorem line_source_evaluates {degree : ℕ} {data : InducingData degree} (keep : Bool)
    {source : SourceCochain degree} {cycle : MaximalCycles degree data.chi .line}
    (evaluation : Evaluates data .line source cycle) :
    Evaluates data .line (lineSource keep source) (lineFlagCutCycle keep cycle) := by
  intro coordinates frame
  change (if GoodFlag .line (QuotientGroup.mk frame) then
    (if keep then cycle.val.val coordinates (QuotientGroup.mk frame) else 0)
    else (if keep then 0 else cycle.val.val coordinates (QuotientGroup.mk frame))) =
    lineSource keep source
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (coordinates index))
      (rationalGroup frame⁻¹)
  rw [evaluation coordinates frame]
  simp only [lineSource, lineCut, LineKeep, adelic_good_line_rational]
  cases keep <;> by_cases flag_good : GoodFlag .line (QuotientGroup.mk frame) <;>
    simp [flag_good]

/-- Shapiro coordinates of a line class cut by goodness: unchanged at the kept cusp, zero at the
killed one. -/
theorem cuspRes_line_cut {n : ℕ} (D : InducingData n) (good : Bool)
    {c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line)}
    (hz : Evaluates D .line c z)
    (hz' : Evaluates D .line (lineSource good c) (lineFlagCutCycle good z)) :
    cuspRes n D.chi .line good
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
          (lineFlagCutCycle good z)) =
      cuspRes n D.chi .line good
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z) ∧
    cuspRes n D.chi .line (!good)
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
          (lineFlagCutCycle good z)) = 0 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (cuspFlag .line good)
    rw [cuspRes_classOf, cuspRes_classOf]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [← hq, fixedPointCycle_evaluates D .line hz' q x,
      fixedPointCycle_evaluates D .line hz q x]
    have keeps : LineKeep good (rationalGroup q⁻¹) := by
      unfold LineKeep
      rw [adelic_good_line_rational, hq, cuspFlag_good_iff]
    simp only [lineSource, lineCut, ite_eq_left keeps]
  · obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (cuspFlag .line (!good))
    refine cuspRes_classOf_eq_zero_of_vanish D .line (!good) hz' q hq (fun x => ?_)
    have drops : ¬LineKeep good (rationalGroup q⁻¹) := by
      unfold LineKeep
      rw [adelic_good_line_rational, hq, cuspFlag_good_iff]
      cases good <;> simp
    simp only [lineSource, lineCut, ite_eq_right drops]

/-- **Cutoff at the line cusps.** Every class of the line boundary summand has a summand class with
the same Shapiro coordinate at the cusp `good` and zero coordinate at the other cusp. -/
theorem exists_cutoff_line {n : ℕ} (D : InducingData n) (good : Bool)
    {a : StratumH2 n D.chi .line} (ha : a ∈ boundarySummand D .line) :
    ∃ a' ∈ boundarySummand D .line,
      cuspRes n D.chi .line good a' = cuspRes n D.chi .line good a ∧
        cuspRes n D.chi .line (!good) a' = 0 := by
  unfold boundarySummand at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hx
    have hz' := line_source_evaluates good hz
    exact ⟨_, classOf_mem_boundarySummand D .line (line_source_cocycle good hc) hz',
      cuspRes_line_cut D good hz hz'⟩
  | zero => exact ⟨0, zero_mem _, by simp, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨x', hx', keep_x, drop_x⟩ := ihx
    obtain ⟨y', hy', keep_y, drop_y⟩ := ihy
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, map_add, keep_x, keep_y],
      by rw [map_add, drop_x, drop_y, add_zero]⟩
  | smul r x hx ih =>
    obtain ⟨x', hx', keep_x, drop_x⟩ := ih
    exact ⟨r • x', Submodule.smul_mem _ r hx', by rw [map_smul, map_smul, keep_x],
      by rw [map_smul, drop_x, smul_zero]⟩

end TernaryPeriodPolynomials.Separation
