module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.BadPlaneOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.GLStrongApproximation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem integerRow_exists_matrix (row : Fin 3 → ℤ) (pivot : Fin 3) (unit : IsUnit (row pivot)) :
    ∃ matrix : IntegralGL3, (fun column => matrix.val 2 column) = row := by
  have exists_matrix : ∃ matrix : Matrix (Fin 3) (Fin 3) ℤ,
      IsUnit matrix ∧ (fun column => matrix 2 column) = row := by
    fin_cases pivot
    · refine ⟨!![0,0,1;0,1,0;row 0,row 1,row 2], ?_, ?_⟩
      · apply (Matrix.isUnit_iff_isUnit_det _).mpr
        simpa [Matrix.det_fin_three] using unit.neg
      · funext column
        fin_cases column <;> rfl
    · refine ⟨!![1,0,0;0,0,1;row 0,row 1,row 2], ?_, ?_⟩
      · apply (Matrix.isUnit_iff_isUnit_det _).mpr
        simpa [Matrix.det_fin_three] using unit.neg
      · funext column
        fin_cases column <;> rfl
    · refine ⟨!![1,0,0;0,1,0;row 0,row 1,row 2], ?_, ?_⟩
      · apply (Matrix.isUnit_iff_isUnit_det _).mpr
        simpa [Matrix.det_fin_three] using unit
      · funext column
        fin_cases column <;> rfl
  obtain ⟨matrix, ⟨lift, lifted⟩, last_row⟩ := exists_matrix
  exact ⟨lift, by simpa only [lifted] using last_row⟩

theorem zmodThree_exists_centered_lift (value : ZMod 3) :
    ∃ integer : ℤ, (integer : ZMod 3) = value ∧ (value ≠ 0 → IsUnit integer) := by
  fin_cases value
  · exact ⟨0, rfl, fun nonzero => (nonzero rfl).elim⟩
  · exact ⟨1, rfl, fun _ => isUnit_one⟩
  · refine ⟨-1, ?_, fun _ => isUnit_one.neg⟩
    rw [Int.cast_neg, Int.cast_one]
    rfl

/-- Any nonzero residue row at three lifts to an actual unimodular integer row. -/
theorem zmodThreeRow_exists_integral_matrix (row : Fin 3 → ZMod 3) (nonzero : row ≠ 0) :
    ∃ matrix : IntegralGL3, ∀ column, (matrix.val 2 column : ZMod 3) = row column := by
  choose lift lifted unit using fun column => zmodThree_exists_centered_lift (row column)
  obtain ⟨pivot, pivot_nonzero⟩ : ∃ pivot, row pivot ≠ 0 := by
    by_contra none
    push Not at none
    exact nonzero (funext none)
  obtain ⟨matrix, equality⟩ := integerRow_exists_matrix lift pivot (unit pivot pivot_nonzero)
  exact ⟨matrix, fun column => (congrArg (fun value : ℤ => (value : ZMod 3))
    (congrFun equality column)).trans (lifted column)⟩

theorem lastRow_vecMul (matrix : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    lastRow ᵥ* matrix = fun column => matrix 2 column := by
  funext column
  simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

/-- The full integral compact group is an integer matrix times the specified level at three. -/
theorem integralGL_congruence_factorization (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    ∃ (integer : IntegralGL3) (compact : GeneralLinearGroup (Fin 3) IntegralAdeles),
      lastRow ᵥ* (GeneralLinearGroup.map integralReduction compact).val = lastRow ∧
      matrix = GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integer * compact := by
  let reduction := GeneralLinearGroup.map integralReduction matrix
  have row_ne : (fun column => (reduction⁻¹).val 2 column) ≠ 0 := by
    intro zero
    have diagonal := congrArg (fun value : GeneralLinearGroup (Fin 3) (ZMod 3) => value.val 2 2)
      (inv_mul_cancel reduction)
    change (∑ column, (reduction⁻¹).val 2 column * reduction.val column 2) = 1 at diagonal
    have entry_zero (column : Fin 3) : (reduction⁻¹).val 2 column = 0 := congrFun zero column
    simp only [entry_zero, zero_mul, Finset.sum_const_zero] at diagonal
    exact zero_ne_one diagonal
  obtain ⟨lift, lifted⟩ := zmodThreeRow_exists_integral_matrix
    (fun column => (reduction⁻¹).val 2 column) row_ne
  let mapped := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) lift
  let compact := mapped * matrix
  have last_row : lastRow ᵥ* (GeneralLinearGroup.map integralReduction mapped).val =
      lastRow ᵥ* (reduction⁻¹).val := by
    rw [lastRow_vecMul, lastRow_vecMul]
    funext column
    simpa [mapped, GeneralLinearGroup.map_apply] using lifted column
  have level : lastRow ᵥ* (GeneralLinearGroup.map integralReduction compact).val = lastRow := by
    change lastRow ᵥ* (GeneralLinearGroup.map integralReduction (mapped * matrix)).val = _
    rw [map_mul, GeneralLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, last_row,
      Matrix.vecMul_vecMul]
    change lastRow ᵥ* ((reduction⁻¹).val * reduction.val) = _
    rw [reduction.inv_mul, Matrix.vecMul_one]
  refine ⟨lift⁻¹, compact, level, ?_⟩
  rw [map_inv]
  change matrix = mapped⁻¹ * (mapped * matrix)
  rw [inv_mul_cancel_left]

theorem finiteGL_map_integer {dimension : ℕ} (integer : GeneralLinearGroup (Fin dimension) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integer) =
    GeneralLinearGroup.map integralEmbedding
      (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integer) := by
  apply Units.ext
  funext row column
  simp [GeneralLinearGroup.map_apply]

/-- Every finite adelic matrix is rational times the actual congruence level. -/
theorem finiteGL_rational_level_factorization (matrix : FiniteGL) :
    ∃ (rational : RationalGL3) (compact : finiteLevel),
      matrix = rationalFinite rational * compact.val := by
  obtain ⟨rational, integral, factorization⟩ := finiteGL_rational_integral_factorization matrix
  obtain ⟨integer, compact, level, compact_factorization⟩ := integralGL_congruence_factorization integral
  have membership : GeneralLinearGroup.map integralEmbedding compact ∈ finiteLevel :=
    ⟨compact, level, rfl⟩
  refine ⟨rational * GeneralLinearGroup.map (Int.castRingHom ℚ) integer,
    ⟨GeneralLinearGroup.map integralEmbedding compact, membership⟩, ?_⟩
  rw [factorization, compact_factorization, map_mul, map_mul, ← mul_assoc]
  change _ = (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integer)) * _
  rw [finiteGL_map_integer]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
