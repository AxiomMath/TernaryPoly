module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.UnipotentSubgroup
public import TernaryPeriodPolynomials.Building.BoundaryApartments.FiniteExtensionPrimitive

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix

abbrev UpperSigns := ℤˣ × ℤˣ

def integralUpperDiagonal (signs : UpperSigns) : IntegralGL3 :=
  ⟨!![(signs.1 : ℤ), 0, 0; 0, (signs.2 : ℤ), 0; 0, 0, 1],
   !![(signs.1⁻¹ : ℤˣ), 0, 0; 0, (signs.2⁻¹ : ℤˣ), 0; 0, 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def integralUpperDiagonalHom : UpperSigns →* IntegralGL3 where
  toFun := integralUpperDiagonal
  map_one' := by
    apply GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;> rfl
  map_mul' first second := by
    apply GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      simp [integralUpperDiagonal, Matrix.mul_apply, Fin.sum_univ_three]

def upperDiagonalHom : UpperSigns →* RationalGL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp integralUpperDiagonalHom

theorem upperDiagonal_entries (signs : UpperSigns) :
    (upperDiagonalHom signs).val =
      !![((signs.1 : ℤ) : ℚ), 0, 0; 0, ((signs.2 : ℤ) : ℚ), 0; 0, 0, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperDiagonalHom, integralUpperDiagonalHom, integralUpperDiagonal,
      GeneralLinearGroup.map_apply]

def upperBorelSubgroup : Subgroup RationalGL3 :=
  rationalLevel ⊓ (parabolic .plane ⊓ parabolic .line)

theorem upperDiagonal_mem (signs : UpperSigns) : upperDiagonalHom signs ∈ upperBorelSubgroup := by
  have arithmetic : integralUpperDiagonal signs ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree (integralUpperDiagonal signs)).val = lastRow
    ext index
    fin_cases index <;>
      simp [lastRow, reductionThree, integralUpperDiagonal, Matrix.single_vecMul]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨integralUpperDiagonal signs, arithmetic⟩, rfl⟩
  · constructor <;> change (upperDiagonalHom signs).val _ _ = 0 <;>
      rw [upperDiagonal_entries] <;> rfl
  · constructor <;> change (upperDiagonalHom signs).val _ _ = 0 <;>
      rw [upperDiagonal_entries] <;> rfl

theorem upperUnipotentSubgroup_le_borel : upperUnipotentSubgroup ≤ upperBorelSubgroup := by
  rintro matrix ⟨left, right, integer, rfl⟩
  refine ⟨(upperUnipotentElement left right integer).property, ?_, ?_⟩
  · constructor <;> change (upperUnipotentElement left right integer).val.val _ _ = 0 <;>
      rw [upperUnipotentElement_entries] <;> rfl
  · constructor <;> change (upperUnipotentElement left right integer).val.val _ _ = 0 <;>
      rw [upperUnipotentElement_entries] <;> rfl

theorem upperDiagonal_normalizes (signs : UpperSigns) (matrix : upperUnipotentSubgroup) :
    (upperDiagonalHom signs)⁻¹ * matrix.val * upperDiagonalHom signs ∈ upperUnipotentSubgroup := by
  obtain ⟨left, right, integer, matrix_eq⟩ := matrix.property
  refine ⟨(signs.1⁻¹ : ℤˣ) * left * (signs.2 : ℤ),
    (signs.1⁻¹ : ℤˣ) * right, (signs.2⁻¹ : ℤˣ) * integer, ?_⟩
  rw [← matrix_eq, ← map_inv]
  apply GeneralLinearGroup.ext
  intro row column
  simp only [GeneralLinearGroup.coe_mul, upperDiagonal_entries,
    upperUnipotentElement_entries]
  rcases Int.units_eq_one_or signs.1 with first | first <;>
    rcases Int.units_eq_one_or signs.2 with second | second <;>
    fin_cases row <;> fin_cases column <;>
    simp [first, second, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem upperBorel_decomposes (matrix : upperBorelSubgroup) :
    ∃ normal : upperUnipotentSubgroup, ∃ signs : UpperSigns,
      normal.val * upperDiagonalHom signs = matrix.val := by
  obtain ⟨integral, integral_eq⟩ := matrix.property.1
  have entry_zero (row column : Fin 3) (zero : matrix.val.val row column = 0) :
      integral.val.val row column = 0 := by
    rw [← integral_eq] at zero
    change (integral.val.val row column : ℚ) = 0 at zero
    exact_mod_cast zero
  have lower_first := entry_zero 1 0 matrix.property.2.2.1
  have lower_second := entry_zero 2 0 matrix.property.2.1.1
  have lower_third := entry_zero 2 1 matrix.property.2.1.2
  have inverse_plane := Adelic.inPlane_inv (g := integral.val) ⟨lower_second, lower_third⟩
  have inverse_line := Adelic.inLine_inv (g := integral.val) ⟨lower_first, lower_second⟩
  have inverse_first : (integral.val.val)⁻¹ 1 0 = 0 := by
    simpa only [GeneralLinearGroup.coe_inv] using inverse_line.1
  have inverse_second : (integral.val.val)⁻¹ 2 0 = 0 := by
    simpa only [GeneralLinearGroup.coe_inv] using inverse_line.2
  have inverse_third : (integral.val.val)⁻¹ 2 1 = 0 := by
    simpa only [GeneralLinearGroup.coe_inv] using inverse_plane.2
  have diagonal_inverse (index : Fin 3) :
      integral.val.val index index * integral.val.inv index index = 1 := by
    have identity := congrArg (fun entries : Matrix (Fin 3) (Fin 3) ℤ => entries index index)
      integral.val.mul_inv
    fin_cases index <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_three, lower_first, lower_second, lower_third,
        inverse_first, inverse_second, inverse_third] using identity
  let diagonal_unit (index : Fin 3) : ℤˣ :=
    ⟨integral.val.val index index, integral.val.inv index index, diagonal_inverse index,
      by simpa only [mul_comm] using diagonal_inverse index⟩
  have last_one : integral.val.val 2 2 = 1 := by
    rcases Int.units_eq_one_or (diagonal_unit 2) with positive | negative
    · exact congrArg Units.val positive
    · have last_negative : integral.val.val 2 2 = -1 := congrArg Units.val negative
      have residue := arithmetic_lastRow integral 2
      rw [last_negative] at residue
      change (-1 : ZMod 3) = 1 at residue
      exact ((by decide : (-1 : ZMod 3) ≠ 1) residue).elim
  let signs : UpperSigns := (diagonal_unit 0, diagonal_unit 1)
  let left := integral.val.val 0 1 * (signs.2⁻¹ : ℤˣ)
  let integer := integral.val.val 1 2
  let right := integral.val.val 0 2 - left * integer
  let normal : upperUnipotentSubgroup :=
    ⟨(upperUnipotentElement left right integer).val, ⟨left, right, integer, rfl⟩⟩
  refine ⟨normal, signs, ?_⟩
  have left_entry : left * (signs.2 : ℤ) = integral.val.val 0 1 := by
    dsimp only [left]
    rw [mul_assoc]
    have unit_inverse : ((signs.2⁻¹ : ℤˣ) : ℤ) * (signs.2 : ℤ) = 1 :=
      congrArg Units.val (inv_mul_cancel signs.2)
    rw [unit_inverse, mul_one]
  have rational_left : (left : ℚ) * ((signs.2 : ℤ) : ℚ) =
      (integral.val.val 0 1 : ℚ) := by exact_mod_cast left_entry
  have rational_right : (right : ℚ) + (left : ℚ) * (integer : ℚ) =
      (integral.val.val 0 2 : ℚ) := by
    dsimp only [right]
    push_cast
    ring
  rw [← integral_eq]
  apply GeneralLinearGroup.ext
  intro row column
  change ((upperUnipotentElement left right integer).val.val *
    (upperDiagonalHom signs).val) row column =
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integral.val).val row column
  rw [upperUnipotentElement_entries, upperDiagonal_entries]
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rational_left, rational_right,
      signs, diagonal_unit, integer, lower_first, lower_second, lower_third, last_one]

theorem upperBorel_exists_cochain {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ primitive : cochains upperBorelSubgroup
        (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne upperBorelSubgroup
        (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
          cocycle.val.val vertices := by
  let restricted : cocycles upperBorelSubgroup
      (rationalCoefficientComponent degree trivialCharacter) :=
    ⟨⟨cocycle.val.val, fun matrix vertices =>
      cocycle.val.property ⟨matrix.val, matrix.property.1⟩ vertices⟩, cocycle.property⟩
  obtain ⟨primitive, differential⟩ := upperUnipotent_exists_cochain degree_positive solution
    functional_property realizes
  obtain ⟨averaged, averaged_differential⟩ := finiteExtension_exists_primitive
    upperBorelSubgroup upperUnipotentSubgroup
    (rationalCoefficientComponent degree trivialCharacter) upperDiagonalHom
    upperDiagonal_mem upperDiagonal_normalizes upperBorel_decomposes restricted primitive differential
  refine ⟨averaged, ?_⟩
  intro vertices
  exact congrArg (fun cochain => cochain.val vertices) averaged_differential

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
