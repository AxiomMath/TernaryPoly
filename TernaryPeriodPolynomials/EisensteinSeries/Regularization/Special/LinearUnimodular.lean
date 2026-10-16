module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearCharacters
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearDomain
public import Mathlib.MeasureTheory.Group.ModularCharacter

@[expose] public section


open Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem ternary_commutative_monoid_character_trivial {C : Type*} [CommMonoid C]
    (character : SpecialLinearGroup (Fin 3) ℝ →* C) (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    character matrix = 1 := by
  exact congrArg Units.val (ternary_commutative_character_trivial character.toHomUnits matrix)

theorem realSpecialLinear_modularCharacter (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    Measure.modularCharacterFun matrix = 1 :=
  ternary_commutative_monoid_character_trivial Measure.modularCharacter matrix

theorem realSpecialLinearHaar_right_translate (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    Measure.map (fun point => point * matrix) realSpecialLinearHaar = realSpecialLinearHaar := by
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, realSpecialLinear_modularCharacter, one_smul]

instance realSpecialLinearHaar_rightInvariant : realSpecialLinearHaar.IsMulRightInvariant :=
  ⟨realSpecialLinearHaar_right_translate⟩

theorem realSpecialLinearHaar_right_measurePreserving (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    MeasurePreserving (fun point => point * matrix) realSpecialLinearHaar realSpecialLinearHaar :=
  ⟨(continuous_id.mul continuous_const).measurable, realSpecialLinearHaar_right_translate matrix⟩

theorem integerSpecialLinearDomain_right_fundamental (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    IsFundamentalDomain integerSpecialLinearSubgroup
      ((fun point => point * matrix) '' integerSpecialLinearDomain) realSpecialLinearHaar := by
  apply integerSpecialLinearDomain_fundamental.image_of_equiv (Equiv.mulRight matrix)
    (realSpecialLinearHaar_right_measurePreserving matrix⁻¹).quasiMeasurePreserving
    (Equiv.refl integerSpecialLinearSubgroup)
  intro element point
  exact mul_assoc element.val point matrix

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
