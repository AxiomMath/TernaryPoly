module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.UnipotentCoboundary
public import TernaryPeriodPolynomials.Building.BoundaryApartments.PrimitiveExtension

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix

theorem upperUnipotentElement_entries (left right integer : ℤ) :
    (upperUnipotentElement left right integer).val.val =
      !![1, (left : ℚ), (right : ℚ) + (left : ℚ) * (integer : ℚ);
         0, 1, (integer : ℚ); 0, 0, 1] := by
  rw [upperUnipotentElement, Subgroup.coe_mul, GeneralLinearGroup.coe_mul,
    integralRadical_val, (upperTranslationPower_entries integer).1]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Adelic.lineUnipotent, Adelic.upperUnipotent, Matrix.mul_apply,
      Fin.sum_univ_three, add_comm]

theorem upperUnipotentElement_zero : upperUnipotentElement 0 0 0 = 1 := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  rw [upperUnipotentElement_entries]
  fin_cases row <;> fin_cases column <;> norm_num

theorem upperUnipotentElement_injective {left right integer next_left next_right next_integer : ℤ}
    (equality : (upperUnipotentElement left right integer).val =
      (upperUnipotentElement next_left next_right next_integer).val) :
    left = next_left ∧ right = next_right ∧ integer = next_integer := by
  have entries := congrArg (fun matrix : RationalGL3 => matrix.val) equality
  rw [upperUnipotentElement_entries, upperUnipotentElement_entries] at entries
  have left_eq : left = next_left := by
    have entry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix 0 1) entries
    change (left : ℚ) = (next_left : ℚ) at entry
    exact_mod_cast entry
  have integer_eq : integer = next_integer := by
    have entry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix 1 2) entries
    change (integer : ℚ) = (next_integer : ℚ) at entry
    exact_mod_cast entry
  refine ⟨left_eq, ?_, integer_eq⟩
  have entry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix 0 2) entries
  change (right : ℚ) + (left : ℚ) * integer =
    (next_right : ℚ) + (next_left : ℚ) * next_integer at entry
  rw [left_eq, integer_eq] at entry
  exact_mod_cast add_right_cancel entry

theorem upperUnipotentElement_inv (left right integer : ℤ) :
    (upperUnipotentElement left right integer)⁻¹ =
      upperUnipotentElement (-left) (-right - integer * left) (-integer) := by
  apply inv_eq_of_mul_eq_one_right
  have coordinate : right + (-right - integer * left) - integer * (-left) = 0 := by ring
  rw [upperUnipotentElement_mul, add_neg_cancel, coordinate, add_neg_cancel,
    upperUnipotentElement_zero]

/-- The integral upper unitriangular matrices, as an actual subgroup of the rational group. -/
def upperUnipotentSubgroup : Subgroup RationalGL3 where
  carrier := {matrix | ∃ left right integer : ℤ,
    (upperUnipotentElement left right integer).val = matrix}
  one_mem' := ⟨0, 0, 0, congrArg Subtype.val upperUnipotentElement_zero⟩
  mul_mem' := by
    rintro first second ⟨left, right, integer, rfl⟩ ⟨next_left, next_right, next_integer, rfl⟩
    refine ⟨left + next_left, right + next_right - integer * next_left,
      integer + next_integer, ?_⟩
    exact congrArg Subtype.val
      (upperUnipotentElement_mul left right integer next_left next_right next_integer).symm
  inv_mem' := by
    rintro matrix ⟨left, right, integer, rfl⟩
    refine ⟨-left, -right - integer * left, -integer, ?_⟩
    exact congrArg Subtype.val (upperUnipotentElement_inv left right integer).symm

theorem upperUnipotentSubgroup_le_level : upperUnipotentSubgroup ≤ rationalLevel := by
  rintro matrix ⟨left, right, integer, rfl⟩
  exact (upperUnipotentElement left right integer).property

def upperUnipotentCoordinates (matrix : upperUnipotentSubgroup) : ℤ × ℤ × ℤ :=
  let left := matrix.property.choose
  let right := matrix.property.choose_spec.choose
  let integer := matrix.property.choose_spec.choose_spec.choose
  (left, right, integer)

theorem upperUnipotentCoordinates_spec (matrix : upperUnipotentSubgroup) :
    (upperUnipotentElement (upperUnipotentCoordinates matrix).1
      (upperUnipotentCoordinates matrix).2.1 (upperUnipotentCoordinates matrix).2.2).val =
        matrix.val :=
  matrix.property.choose_spec.choose_spec.choose_spec

theorem upperUnipotentCoordinates_mul (first second : upperUnipotentSubgroup) :
    upperUnipotentCoordinates (first * second) =
      ((upperUnipotentCoordinates first).1 + (upperUnipotentCoordinates second).1,
       (upperUnipotentCoordinates first).2.1 + (upperUnipotentCoordinates second).2.1 -
         (upperUnipotentCoordinates first).2.2 * (upperUnipotentCoordinates second).1,
       (upperUnipotentCoordinates first).2.2 + (upperUnipotentCoordinates second).2.2) := by
  have equality :
      (upperUnipotentElement (upperUnipotentCoordinates (first * second)).1
        (upperUnipotentCoordinates (first * second)).2.1
        (upperUnipotentCoordinates (first * second)).2.2).val =
      (upperUnipotentElement
        ((upperUnipotentCoordinates first).1 + (upperUnipotentCoordinates second).1)
        ((upperUnipotentCoordinates first).2.1 + (upperUnipotentCoordinates second).2.1 -
          (upperUnipotentCoordinates first).2.2 * (upperUnipotentCoordinates second).1)
        ((upperUnipotentCoordinates first).2.2 + (upperUnipotentCoordinates second).2.2)).val := by
    rw [upperUnipotentCoordinates_spec, ← upperUnipotentElement_mul]
    simp only [Subgroup.coe_mul, upperUnipotentCoordinates_spec]
  obtain ⟨left_eq, right_eq, integer_eq⟩ := upperUnipotentElement_injective equality
  exact Prod.ext left_eq (Prod.ext right_eq integer_eq)

theorem upperUnipotent_exists_cochain {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ primitive : cochains upperUnipotentSubgroup
        (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne upperUnipotentSubgroup
        (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
          cocycle.val.val vertices := by
  let restricted : cocycles upperUnipotentSubgroup
      (rationalCoefficientComponent degree trivialCharacter) :=
    ⟨⟨cocycle.val.val, fun matrix vertices =>
      cocycle.val.property ⟨matrix.val, upperUnipotentSubgroup_le_level matrix.property⟩ vertices⟩,
      cocycle.property⟩
  obtain ⟨primitive, primitive_differential⟩ := upperUnipotent_exists_primitive degree_positive
    solution functional_property realizes
  let subgroup_primitive (matrix : upperUnipotentSubgroup) : HomogeneousPoly degree :=
    primitive (upperUnipotentCoordinates matrix).1
      (upperUnipotentCoordinates matrix).2.1 (upperUnipotentCoordinates matrix).2.2
  have differential (first second : upperUnipotentSubgroup) :
      restricted.val.val ![1, first.val, (first * second).val] =
        rationalCoefficientComponent degree trivialCharacter first.val (subgroup_primitive second) -
          subgroup_primitive (first * second) + subgroup_primitive first := by
    have value := primitive_differential (upperUnipotentCoordinates first).1
      (upperUnipotentCoordinates first).2.1 (upperUnipotentCoordinates first).2.2
      (upperUnipotentCoordinates second).1 (upperUnipotentCoordinates second).2.1
      (upperUnipotentCoordinates second).2.2
    simp only [Subgroup.coe_mul, upperUnipotentCoordinates_spec] at value
    simpa only [restricted, subgroup_primitive, upperUnipotentCoordinates_mul,
      Subgroup.coe_mul] using value
  refine ⟨extendedPrimitive upperUnipotentSubgroup
    (rationalCoefficientComponent degree trivialCharacter) restricted subgroup_primitive, ?_⟩
  intro vertices
  exact congrArg (fun cochain => cochain.val vertices)
    (extendedPrimitive_differential upperUnipotentSubgroup
      (rationalCoefficientComponent degree trivialCharacter) restricted subgroup_primitive differential)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
