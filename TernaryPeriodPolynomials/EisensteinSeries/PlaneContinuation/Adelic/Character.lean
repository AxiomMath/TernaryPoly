module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Character

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicCharacter

def character : AddChar Adeles Circle where
  toFun value := Real.fourierChar value.1 * FiniteCharacter.character value.2
  map_zero_eq_one' := by simp only [Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one, one_mul]
  map_add_eq_mul' first second := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ac_rfl

def phase (value : Adeles) : ℂ := character value

theorem phase_apply (value : Adeles) :
    phase value = (Real.fourierChar value.1 : ℂ) * FiniteCharacter.phase value.2 := Circle.coe_mul _ _

theorem character_continuous : Continuous character :=
  (Real.continuous_fourierChar.comp continuous_fst).mul
    (FiniteCharacter.character_continuous.comp continuous_snd)

theorem phase_continuous : Continuous phase :=
  continuous_subtype_val.comp character_continuous

theorem phase_norm (value : Adeles) : ‖phase value‖ = 1 := Circle.norm_coe _

theorem phase_zero : phase 0 = 1 := by
  simp only [phase, AddChar.map_zero_eq_one, Circle.coe_one]

theorem phase_add (first second : Adeles) : phase (first + second) = phase first * phase second := by
  simp only [phase, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem phase_neg (value : Adeles) : phase (-value) = (phase value)⁻¹ := by
  simp only [phase, AddChar.map_neg_eq_inv, Circle.coe_inv]

theorem phase_rational (value : ℚ) : phase (rationalAdele value) = 1 := by
  rw [phase_apply]
  change (Real.fourierChar (value : ℝ) : ℂ) * FiniteCharacter.phase (algebraMap ℚ FiniteAdeles value) = 1
  rw [Real.fourierChar_apply, FiniteCharacter.phase_rational, ← Complex.exp_add]
  have exponent : ((2 * Real.pi * (value : ℝ) : ℝ) : ℂ) * Complex.I +
      -(2 * (Real.pi : ℂ) * ((value : ℝ) : ℂ)) * Complex.I = 0 := by push_cast; ring
  rw [exponent, Complex.exp_zero]

theorem character_rational (value : ℚ) : character (rationalAdele value) = 1 :=
  Circle.coe_inj.mp ((phase_rational value).trans Circle.coe_one.symm)

theorem phase_rational_translate (rational : ℚ) (value : Adeles) :
    phase (rationalAdele rational + value) = phase value := by
  rw [phase_add, phase_rational, one_mul]

theorem phase_infinity (value : ℝ) : phase (value, 0) = (Real.fourierChar value : ℂ) := by
  rw [phase_apply, FiniteCharacter.phase_zero, mul_one]

theorem phase_finite (value : FiniteAdeles) : phase (0, value) = FiniteCharacter.phase value := by
  rw [phase_apply, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicCharacter
