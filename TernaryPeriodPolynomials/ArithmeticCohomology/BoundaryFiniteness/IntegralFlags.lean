module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.IntegerRowReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags

noncomputable section

def rational : IntegralGL3 →* RationalGL3 := GeneralLinearGroup.map (Int.castRingHom ℚ)

theorem rational_row_reduction (row : Fin 3 → ℚ) :
    ∃ matrix : IntegralGL3, (row ᵥ* (rational matrix).val) 1 = 0 ∧
      (row ᵥ* (rational matrix).val) 2 = 0 := by
  let constantRows : Matrix (Fin 3) (Fin 3) ℚ := fun _ column => row column
  let integerRow : Fin 3 → ℤ := constantRows.num 0
  let denominator : ℚ := constantRows.den
  have denominator_nonzero : denominator ≠ 0 := Nat.cast_ne_zero.mpr constantRows.den_ne_zero
  have row_equality : denominator • row = fun index => (integerRow index : ℚ) := by
    funext index
    exact congrArg (fun matrix => matrix 0 index) (IntegralConjugation.clear_denominator constantRows)
  let matrix := IntegerRowReduction.reduceRow integerRow
  have vanishes (index : Fin 3) (different : index ≠ 0) : (integerRow ᵥ* matrix.val) index = 0 := by
    have equation := congrFun (IntegerRowReduction.reduceRow_spec integerRow) index
    fin_cases index
    · exact (different rfl).elim
    · exact equation
    · exact equation
  have rational_vanishes (index : Fin 3) (different : index ≠ 0) :
      (row ᵥ* (rational matrix).val) index = 0 := by
    apply (mul_eq_zero.mp (show denominator * _ = 0 from ?_)).resolve_left denominator_nonzero
    change (denominator • (row ᵥ* (rational matrix).val)) _ = 0
    rw [← Matrix.smul_vecMul, row_equality]
    have cast_equation := congrArg (Int.cast : ℤ → ℚ) (vanishes index different)
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three, rational] using cast_equation
  exact ⟨matrix, rational_vanishes 1 (by decide), rational_vanishes 2 (by decide)⟩

def transpose (matrix : IntegralGL3) : IntegralGL3 :=
  GeneralLinearGroup.mk'' matrix.val.transpose (by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det matrix.val).mp matrix.isUnit)

theorem integral_line_representative (matrix : RationalGL3) :
    ∃ representative : IntegralGL3,
      (QuotientGroup.mk (rational representative) : Flags .line) = QuotientGroup.mk matrix := by
  obtain ⟨reduction, first, second⟩ := rational_row_reduction (fun index => matrix.val index 0)
  refine ⟨(transpose reduction)⁻¹, QuotientGroup.eq.mpr ?_⟩
  rw [map_inv, inv_inv]
  change ((rational (transpose reduction)) * matrix).val 1 0 = 0 ∧
    ((rational (transpose reduction)) * matrix).val 2 0 = 0
  constructor
  · simpa [rational, transpose, Matrix.vecMul, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, mul_comm] using first
  · simpa [rational, transpose, Matrix.vecMul, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, mul_comm] using second

def swapFirstLast : IntegralGL3 :=
  ⟨!![0,0,1;0,1,0;1,0,0], !![0,0,1;0,1,0;1,0,0], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem integral_plane_representative (matrix : RationalGL3) :
    ∃ representative : IntegralGL3,
      (QuotientGroup.mk (rational representative) : Flags .plane) = QuotientGroup.mk matrix := by
  obtain ⟨reduction, first, second⟩ := rational_row_reduction (fun index => (matrix⁻¹).val 2 index)
  refine ⟨reduction * swapFirstLast, ?_⟩
  symm
  apply QuotientGroup.eq.mpr
  change (matrix⁻¹ * rational (reduction * swapFirstLast)).val 2 0 = 0 ∧
    (matrix⁻¹ * rational (reduction * swapFirstLast)).val 2 1 = 0
  rw [map_mul, ← mul_assoc]
  constructor
  · simpa [Matrix.mul_apply, Fin.sum_univ_three, rational, swapFirstLast, Matrix.vecMul, dotProduct] using second
  · simpa [Matrix.mul_apply, Fin.sum_univ_three, rational, swapFirstLast, Matrix.vecMul, dotProduct] using first

theorem integral_representative (side : Side) (flag : Flags side) :
    ∃ representative : IntegralGL3, QuotientGroup.mk (rational representative) = flag := by
  induction flag using Quotient.inductionOn with
  | _ matrix =>
    cases side
    · exact integral_plane_representative matrix
    · exact integral_line_representative matrix

end

end TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags
