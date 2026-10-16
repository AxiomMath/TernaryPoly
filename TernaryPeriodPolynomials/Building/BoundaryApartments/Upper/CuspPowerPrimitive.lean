module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.TranslationPowers

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

def upperRadicalFunctionAction (degree : ℕ) (integer : ℤ) :
    Module.End ℂ (ℤ → ℤ → HomogeneousPoly degree) where
  toFun value left right :=
    rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
      (value left (integer * left + right))
  map_add' first second := by
    funext left right
    exact map_add _ _ _
  map_smul' scalar value := by
    funext left right
    exact map_smul
      (rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val)
      scalar (value left (integer * left + right))

theorem upperRadicalFunctionAction_injective (degree : ℕ) (integer : ℤ) :
    Function.Injective (upperRadicalFunctionAction degree integer) := by
  intro first second equality
  funext left right
  have value := congrFun (congrFun equality left) (right - integer * left)
  change rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
      (first left (integer * left + (right - integer * left))) =
    rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
      (second left (integer * left + (right - integer * left))) at value
  rw [show integer * left + (right - integer * left) = right by ring] at value
  exact rationalCoefficient_injective degree _ value

theorem upperCusp_exists_powerPrimitive {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ (first second : HomogeneousPoly degree) (correction : ℤ → HomogeneousPoly degree),
      MvPolynomial.pderiv 0 first.val = 0 ∧ MvPolynomial.pderiv 0 second.val = 0 ∧
      rationalCoefficientComponent degree trivialCharacter binaryR (-first) = first ∧
      rationalCoefficientComponent degree trivialCharacter binaryR second = second ∧
      (∀ integers next : ℤ, correction (integers + next) =
        rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integers).val
          (correction next) + correction integers) ∧
      ∀ integer left right : ℤ,
        mixedBarEdge cocycle (upperTranslationPower integer).val
            (Adelic.lineUnipotent (left : ℚ) (right : ℚ)) =
          (rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
            (binaryRadicalValue first second left (integer * left + right)) -
              binaryRadicalValue first second left right +
            (rationalCoefficientComponent degree trivialCharacter
              (integralRadical left right).val (correction integer) - correction integer)).val := by
  obtain ⟨first, second, correction, first_binary, second_binary, first_reflection,
      second_reflection, generator_eq⟩ := upperCusp_exists_radicalCorrection degree_positive
        solution functional_property realizes
  obtain ⟨corrections, correction_one, correction_crossed⟩ := cyclicCrossed_exists
    (rationalCoefficientComponent degree trivialCharacter) upperCuspTranslation.val correction
  have corrections_add (integer next : ℤ) : corrections (integer + next) =
      rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
        (corrections next) + corrections integer := by
    rw [correction_crossed, upperTranslationPower_eq_zpow, Subgroup.coe_zpow]
  let values (integer left right : ℤ) : HomogeneousPoly degree :=
    -functional (mixedRadicalChain (upperTranslationPower integer) left right)
  have values_add (integer next left right : ℤ) : values (integer + next) left right =
      values integer left right +
        rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
          (values next left (integer * left + right)) := by
    simp only [values, upperTranslationPower_add,
      mixedRadicalValue_levi_product functional_property _ _
        (upperTranslationPower_line integer) (upperTranslationPower_line next)
        (upperTranslationPower_block integer) (upperTranslationPower_block next)
        left right left (integer * left + right)
        (upperTranslationPower_radical_conjugate integer left right), neg_add, map_neg]
  let proposed (integer left right : ℤ) : HomogeneousPoly degree :=
    rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
      (binaryRadicalValue first second left (integer * left + right)) -
        binaryRadicalValue first second left right +
      (rationalCoefficientComponent degree trivialCharacter (integralRadical left right).val
        (corrections integer) - corrections integer)
  have commute (integer left right : ℤ) :
      (upperTranslationPower integer).val *
          (integralRadical left (integer * left + right)).val =
        (integralRadical left right).val * (upperTranslationPower integer).val := by
    rw [← upperTranslationPower_radical_conjugate integer left right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have proposed_add (integer next left right : ℤ) : proposed (integer + next) left right =
      proposed integer left right +
        rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
          (proposed next left (integer * left + right)) := by
    have coordinate : (integer + next) * left + right =
        next * left + (integer * left + right) := by ring
    have action_commute :
        rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
            (rationalCoefficientComponent degree trivialCharacter
              (integralRadical left (integer * left + right)).val (corrections next)) =
          rationalCoefficientComponent degree trivialCharacter (integralRadical left right).val
            (rationalCoefficientComponent degree trivialCharacter
              (upperTranslationPower integer).val (corrections next)) := by
      rw [← Module.End.mul_apply, ← map_mul, commute, map_mul, Module.End.mul_apply]
    simp only [proposed, upperTranslationPower_add, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, corrections_add, map_add, map_sub]
    rw [coordinate, action_commute]
    abel
  let remainder (integer : ℤ) : ℤ → ℤ → HomogeneousPoly degree :=
    fun left right => values integer left right - proposed integer left right
  have crossed (integer next : ℤ) : remainder (integer + next) =
      upperRadicalFunctionAction degree integer (remainder next) + remainder integer := by
    funext left right
    change values (integer + next) left right - proposed (integer + next) left right =
      rationalCoefficientComponent degree trivialCharacter (upperTranslationPower integer).val
        (values next left (integer * left + right) - proposed next left (integer * left + right)) +
      (values integer left right - proposed integer left right)
    rw [values_add, proposed_add, map_sub]
    abel
  have generator_zero : remainder 1 = 0 := by
    funext left right
    change values 1 left right - proposed 1 left right = 0
    apply sub_eq_zero.mpr
    apply Subtype.ext
    have generator := generator_eq left right
    rw [mixedBarEdge_of_levi realizes upperCuspTranslation left right upperCuspTranslation_line,
      ← integralRadical_val left right] at generator
    simpa only [values, proposed, upperTranslationPower_one, correction_one,
      one_mul, Submodule.coe_neg, mixedRadicalChain] using generator
  have vanishing := integerCrossed_zero (upperRadicalFunctionAction degree) remainder crossed
    (upperRadicalFunctionAction_injective degree 1) generator_zero
  refine ⟨first, second, corrections, first_binary, second_binary, first_reflection,
    second_reflection, corrections_add, ?_⟩
  intro integer left right
  rw [mixedBarEdge_of_levi realizes (upperTranslationPower integer) left right
    (upperTranslationPower_line integer), ← integralRadical_val left right]
  have normal := sub_eq_zero.mp (congrFun (congrFun (vanishing integer) left) right)
  exact congrArg Subtype.val normal

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
