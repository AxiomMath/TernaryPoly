module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.TranslationLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.CyclicCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def integralUpperTranslationAt (k : ℤ) : IntegralGL3 :=
  ⟨!![1,0,0;0,1,k;0,0,1], !![1,0,0;0,1,-k;0,0,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three]⟩

def integralUpperTranslationHom : Multiplicative ℤ →* IntegralGL3 where
  toFun k := integralUpperTranslationAt k.toAdd
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' k l := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [integralUpperTranslationAt,Matrix.mul_apply,Fin.sum_univ_three,add_comm]

def upperTranslationHom : Multiplicative ℤ →* RationalGL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp integralUpperTranslationHom

def upperTranslationAt (k : ℤ) : RationalGL3 := upperTranslationHom (Multiplicative.ofAdd k)

theorem upperTranslationAt_one : upperTranslationAt 1 = upperTranslation := rfl

theorem upperTranslationAt_zero : upperTranslationAt 0 = 1 := upperTranslationHom.map_one

theorem upperTranslationAt_add (k l : ℤ) :
    upperTranslationAt (k+l) = upperTranslationAt k * upperTranslationAt l :=
  upperTranslationHom.map_mul (Multiplicative.ofAdd k) (Multiplicative.ofAdd l)

theorem integralUpperTranslationAt_levi (k : ℤ) : BadLineLevi (integralUpperTranslationAt k) := by
  refine ⟨?_,rfl,rfl,rfl,rfl⟩
  rw [arithmeticLevel_mem_iff]
  intro i
  fin_cases i <;> simp [integralUpperTranslationAt]

theorem upperTranslationAt_mem (k : ℤ) : upperTranslationAt k ∈ rationalLevel :=
  rationalLevel_badLineLevi (integralUpperTranslationAt k) (integralUpperTranslationAt_levi k)

theorem upperTranslationAt_conjugate (k : ℤ) (s t : ℚ) :
    (upperTranslationAt k)⁻¹ * Adelic.lineUnipotent s t * upperTranslationAt k =
      Adelic.lineUnipotent s ((k : ℚ)*s+t) := by
  change ((GeneralLinearGroup.map (Int.castRingHom ℚ)) (integralUpperTranslationAt k))⁻¹ *
    Adelic.lineUnipotent s t *
    (GeneralLinearGroup.map (Int.castRingHom ℚ)) (integralUpperTranslationAt k) = _
  rw [← map_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralUpperTranslationAt,Adelic.lineUnipotent,Adelic.upperUnipotent,
      Matrix.mul_apply,Fin.sum_univ_three]
  ring

theorem upperTranslationAt_normalizes (k s t : ℤ) : ∃ s' t' : ℤ,
    (upperTranslationAt k)⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * upperTranslationAt k =
      Adelic.lineUnipotent (s' : ℚ) (t' : ℚ) := by
  exact ⟨s,k*s+t,by simpa only [Int.cast_add,Int.cast_mul] using
    upperTranslationAt_conjugate k (s : ℚ) (t : ℚ)⟩

theorem pureMixed_upperTranslation_bar (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (k l : ℤ) :
    barValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
      (upperTranslationAt k) (upperTranslationAt l) = 0 :=
  pureMixed_levi_bar c pure (integralUpperTranslationAt k) (integralUpperTranslationAt l)
    (integralUpperTranslationAt_levi k) (integralUpperTranslationAt_levi l)

def shearPair (k : ℤ) (x : ℤ × ℤ) : ℤ × ℤ := (x.1,k*x.1+x.2)

theorem shearPair_zero (x : ℤ × ℤ) : shearPair 0 x = x := by
  simp [shearPair]

theorem shearPair_add (k l : ℤ) (x : ℤ × ℤ) :
    shearPair (k+l) x = shearPair l (shearPair k x) := by
  ext <;> simp [shearPair]
  ring

theorem upperTranslationAt_radical_conjugate (k : ℤ) (x : ℤ × ℤ) :
    (upperTranslationAt k)⁻¹ * integralRadicalHom (Multiplicative.ofAdd x) * upperTranslationAt k =
      integralRadicalHom (Multiplicative.ofAdd (shearPair k x)) := by
  simpa only [integralRadicalHom,MonoidHom.coe_mk,OneHom.coe_mk,toAdd_ofAdd,
    shearPair,Int.cast_add,Int.cast_mul] using upperTranslationAt_conjugate k (x.1 : ℚ) (x.2 : ℚ)

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
