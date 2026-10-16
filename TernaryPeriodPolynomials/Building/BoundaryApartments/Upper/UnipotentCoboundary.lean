module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.CuspPowerPrimitive
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.PathDefects

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

def upperUnipotentElement (left right integer : ℤ) : rationalLevel :=
  integralRadical left right * upperTranslationPower integer

theorem upperTranslationPower_radical_commute (integer left right : ℤ) :
    upperTranslationPower integer * integralRadical left right =
      integralRadical left (right - integer * left) * upperTranslationPower integer := by
  have conjugate := upperTranslationPower_radical_conjugate integer left (right - integer * left)
  rw [show integer * left + (right - integer * left) = right by ring] at conjugate
  rw [← conjugate]
  group

theorem upperUnipotentElement_mul (left right integer next_left next_right next_integer : ℤ) :
    upperUnipotentElement left right integer *
      upperUnipotentElement next_left next_right next_integer =
        upperUnipotentElement (left + next_left) (right + next_right - integer * next_left)
          (integer + next_integer) := by
  simp only [upperUnipotentElement]
  rw [show (integralRadical left right * upperTranslationPower integer) *
      (integralRadical next_left next_right * upperTranslationPower next_integer) =
      integralRadical left right * (upperTranslationPower integer *
        integralRadical next_left next_right) * upperTranslationPower next_integer by group,
    upperTranslationPower_radical_commute, ← mul_assoc, integralRadical_mul,
    mul_assoc, ← upperTranslationPower_add]
  congr 2
  ring

theorem upperUnipotent_exists_primitive {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ primitive : ℤ → ℤ → ℤ → HomogeneousPoly degree,
      ∀ left right integer next_left next_right next_integer : ℤ,
        cocycle.val.val ![1, (upperUnipotentElement left right integer).val,
          (upperUnipotentElement left right integer *
            upperUnipotentElement next_left next_right next_integer).val] =
          rationalCoefficientComponent degree trivialCharacter
              (upperUnipotentElement left right integer).val
              (primitive next_left next_right next_integer) -
            primitive (left + next_left) (right + next_right - integer * next_left)
              (integer + next_integer) + primitive left right integer := by
  obtain ⟨first, second, corrections, first_binary, second_binary,
      _, _, corrections_add, mixed_eq⟩ := upperCusp_exists_powerPrimitive degree_positive
        solution functional_property realizes
  let radical_action (left right : ℤ) :=
    rationalCoefficientComponent degree trivialCharacter (integralRadical left right).val
  let levi_action (integer : ℤ) :=
    rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
  let linear := binaryRadicalValue first second
  let primitive (left right integer : ℤ) : HomogeneousPoly degree :=
    linear left right - radical_action left right (corrections integer)
  refine ⟨primitive, ?_⟩
  intro left right integer next_left next_right next_integer
  let conjugate_right := next_right - integer * next_left
  have matrix_commute :
      (upperTranslationPower integer).val * (integralRadical next_left next_right).val =
        (integralRadical next_left conjugate_right).val * (upperTranslationPower integer).val := by
    exact congrArg Subtype.val (upperTranslationPower_radical_commute integer next_left next_right)
  have action_commute (value : HomogeneousPoly degree) :
      levi_action integer (radical_action next_left next_right value) =
        radical_action next_left conjugate_right (levi_action integer value) := by
    change rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
        (rationalCoefficientComponent degree trivialCharacter
          (integralRadical next_left next_right).val value) = _
    rw [← Module.End.mul_apply, ← map_mul, matrix_commute, map_mul, Module.End.mul_apply]
  have radical_product (value : HomogeneousPoly degree) :
      radical_action (left + next_left) (right + conjugate_right) value =
        radical_action left right (radical_action next_left conjugate_right value) := by
    simp only [radical_action, ← integralRadical_mul, Subgroup.coe_mul,
      map_mul, Module.End.mul_apply]
  have linear_add : linear (left + next_left) (right + conjugate_right) =
      linear left right + linear next_left conjugate_right := by
    simp only [linear, binaryRadicalValue, add_zsmul]
    abel
  have linear_fixed : radical_action left right (linear next_left conjugate_right) =
      linear next_left conjugate_right := by
    dsimp only [radical_action]
    rw [integralRadical_val]
    exact rationalCoefficient_binary_fixed _
      (binaryRadicalValue_binary first second first_binary second_binary next_left conjugate_right) _ _
  have value := realizesPathClass_radicalLevi_product functional_property realizes left right
    next_left next_right next_left conjugate_right
    (upperTranslationPower integer) (upperTranslationPower next_integer)
    (upperTranslationPower_line integer) (upperTranslationPower_line next_integer)
    (upperTranslationPower_block integer) (upperTranslationPower_block next_integer)
    (upperTranslationPower_radical_commute integer next_left next_right)
  change cocycle.val.val ![1, (upperUnipotentElement left right integer).val,
    (upperUnipotentElement left right integer *
      upperUnipotentElement next_left next_right next_integer).val] =
      -radical_action left right
        (functional (mixedRadicalChain (upperTranslationPower integer) next_left conjugate_right)) at value
  rw [value]
  have mixed := mixed_eq integer next_left conjugate_right
  rw [mixedBarEdge_of_levi realizes (upperTranslationPower integer) next_left conjugate_right
    (upperTranslationPower_line integer), ← integralRadical_val next_left conjugate_right] at mixed
  have mixed_value : -functional (mixedRadicalChain (upperTranslationPower integer)
      next_left conjugate_right) = levi_action integer (linear next_left next_right) -
        linear next_left conjugate_right +
      (radical_action next_left conjugate_right (corrections integer) - corrections integer) := by
    apply Subtype.ext
    have coordinate : integer * next_left + conjugate_right = next_right := by
      dsimp only [conjugate_right]
      ring
    simpa only [levi_action, linear, radical_action, mixedRadicalChain,
      Submodule.coe_neg, coordinate] using mixed
  rw [← map_neg, mixed_value]
  have coordinate : right + next_right - integer * next_left = right + conjugate_right := by
    dsimp only [conjugate_right]
    ring
  rw [coordinate]
  rw [upperUnipotentElement, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  change radical_action left right
      (levi_action integer (linear next_left next_right) - linear next_left conjugate_right +
        (radical_action next_left conjugate_right (corrections integer) - corrections integer)) =
    radical_action left right
        (levi_action integer (primitive next_left next_right next_integer)) -
      primitive (left + next_left) (right + conjugate_right) (integer + next_integer) +
        primitive left right integer
  simp only [primitive, map_sub, map_add, corrections_add, linear_add]
  rw [action_commute, radical_product, radical_product, linear_fixed]
  abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
