module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.CyclicShear
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.SemidirectCorrection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def upperElement (s t k : ℤ) : RationalGL3 :=
  Adelic.lineUnipotent (s : ℚ) (t : ℚ) * upperTranslationAt k

theorem upperElement_val (s t k : ℤ) :
    (upperElement s t k).val = !![1,(s : ℚ),(s*k+t : ℤ);0,1,(k : ℚ);0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperElement,upperTranslationAt,upperTranslationHom,integralUpperTranslationHom,
      integralUpperTranslationAt,Adelic.lineUnipotent,Adelic.upperUnipotent,
      Matrix.mul_apply,Fin.sum_univ_three,Int.cast_add,Int.cast_mul]

theorem upperElement_mul (s t k s' t' k' : ℤ) :
    upperElement s t k * upperElement s' t' k' =
      upperElement (s+s') (t+t'-k*s') (k+k') := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_mul,upperElement_val,upperElement_val,upperElement_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,Int.cast_add,Int.cast_sub,Int.cast_mul] <;> ring

theorem upperElement_zero : upperElement 0 0 0 = 1 := by
  apply Units.ext
  rw [upperElement_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem upperElement_unique {s t k s' t' k' : ℤ}
    (equal : upperElement s t k = upperElement s' t' k') : s = s' ∧ t = t' ∧ k = k' := by
  have first := congrArg (fun g : RationalGL3 => g.val 0 1) equal
  have second := congrArg (fun g : RationalGL3 => g.val 0 2) equal
  have third := congrArg (fun g : RationalGL3 => g.val 1 2) equal
  have hs : s = s' := by exact_mod_cast (by simpa [upperElement_val] using first : (s : ℚ) = (s' : ℚ))
  have hk : k = k' := by exact_mod_cast (by simpa [upperElement_val] using third : (k : ℚ) = (k' : ℚ))
  refine ⟨hs,?_,hk⟩
  subst s'
  subst k'
  have equal_sum : s*k+t = s*k+t' := by
    exact_mod_cast (by simpa [upperElement_val] using second :
      ((s*k+t : ℤ) : ℚ) = ((s*k+t' : ℤ) : ℚ))
  exact add_left_cancel equal_sum

def integralUpperGroup : Subgroup RationalGL3 where
  carrier := {g | ∃ p : ℤ × ℤ × ℤ, upperElement p.1 p.2.1 p.2.2 = g}
  one_mem' := ⟨(0,0,0),upperElement_zero⟩
  mul_mem' := by
    rintro g h ⟨⟨s,t,k⟩,rfl⟩ ⟨⟨s',t',k'⟩,rfl⟩
    exact ⟨(s+s',t+t'-k*s',k+k'),(upperElement_mul s t k s' t' k').symm⟩
  inv_mem' := by
    rintro g ⟨⟨s,t,k⟩,rfl⟩
    refine ⟨(-s,-t-k*s,-k),?_⟩
    apply mul_left_cancel (a := upperElement s t k)
    rw [mul_inv_cancel,upperElement_mul]
    have arithmetic : t+(-t-k*s)-k*(-s) = 0 := by ring
    rw [add_neg_cancel,add_neg_cancel,arithmetic]
    exact upperElement_zero

def upperParameters (g : integralUpperGroup) : ℤ × ℤ × ℤ := Classical.choose g.property

theorem upperParameters_spec (g : integralUpperGroup) :
    upperElement (upperParameters g).1 (upperParameters g).2.1 (upperParameters g).2.2 = g.val :=
  Classical.choose_spec g.property

theorem upperParameters_mul (g h : integralUpperGroup) :
    upperParameters (g*h) =
      ((upperParameters g).1+(upperParameters h).1,
        (upperParameters g).2.1+(upperParameters h).2.1-(upperParameters g).2.2*(upperParameters h).1,
        (upperParameters g).2.2+(upperParameters h).2.2) := by
  have equal : upperElement (upperParameters (g*h)).1 (upperParameters (g*h)).2.1
      (upperParameters (g*h)).2.2 =
      upperElement ((upperParameters g).1+(upperParameters h).1)
        ((upperParameters g).2.1+(upperParameters h).2.1-(upperParameters g).2.2*(upperParameters h).1)
        ((upperParameters g).2.2+(upperParameters h).2.2) := by
    rw [← upperElement_mul,upperParameters_spec,upperParameters_spec,upperParameters_spec]
    rfl
  rcases upperElement_unique equal with ⟨hs,ht,hk⟩
  exact Prod.ext hs (Prod.ext ht hk)

theorem integralUpperGroup_le : integralUpperGroup ≤ rationalLevel := by
  rintro g ⟨⟨s,t,k⟩,rfl⟩
  exact rationalLevel.mul_mem (rationalLevel_lineUnipotent s t) (upperTranslationAt_mem k)

def upperRadical (g : integralUpperGroup) : rationalLevel :=
  ⟨Adelic.lineUnipotent ((upperParameters g).1 : ℚ) ((upperParameters g).2.1 : ℚ),
    rationalLevel_lineUnipotent _ _⟩

def upperLevi (g : integralUpperGroup) : rationalLevel :=
  ⟨upperTranslationAt (upperParameters g).2.2,upperTranslationAt_mem _⟩

theorem upper_factorization (g : integralUpperGroup) :
    (upperRadical g).val * (upperLevi g).val = g.val := upperParameters_spec g

theorem upperLevi_product (g h : integralUpperGroup) :
    (upperLevi (g*h)).val = (upperLevi g).val*(upperLevi h).val := by
  change upperTranslationAt (upperParameters (g*h)).2.2 = _
  rw [upperParameters_mul]
  exact upperTranslationAt_add _ _

theorem upperTranslationAt_inverse (k : ℤ) : (upperTranslationAt k)⁻¹ = upperTranslationAt (-k) := by
  change (upperTranslationHom (Multiplicative.ofAdd k))⁻¹ =
    upperTranslationHom ((Multiplicative.ofAdd k)⁻¹)
  exact (upperTranslationHom.map_inv _).symm

theorem upperTranslationAt_forward_conjugate (k s t : ℤ) :
    upperTranslationAt k * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * (upperTranslationAt k)⁻¹ =
      Adelic.lineUnipotent (s : ℚ) ((t-k*s : ℤ) : ℚ) := by
  have conjugate := upperTranslationAt_conjugate (-k) (s : ℚ) (t : ℚ)
  rw [← upperTranslationAt_inverse,inv_inv] at conjugate
  simpa only [Int.cast_neg,Int.cast_add,Int.cast_sub,Int.cast_mul,sub_eq_add_neg,neg_mul,add_comm] using conjugate

theorem upperRadical_product (g h : integralUpperGroup) :
    (upperRadical (g*h)).val = (upperRadical g).val*
      ((upperLevi g).val*(upperRadical h).val*(upperLevi g).val⁻¹) := by
  change Adelic.lineUnipotent ((upperParameters (g*h)).1 : ℚ) ((upperParameters (g*h)).2.1 : ℚ) =
    Adelic.lineUnipotent ((upperParameters g).1 : ℚ) ((upperParameters g).2.1 : ℚ)*
      (upperTranslationAt (upperParameters g).2.2*
        Adelic.lineUnipotent ((upperParameters h).1 : ℚ) ((upperParameters h).2.1 : ℚ)*
        (upperTranslationAt (upperParameters g).2.2)⁻¹)
  rw [upperParameters_mul,upperTranslationAt_forward_conjugate,← Adelic.lineUnipotent_add]
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul]
  congr 1
  ring

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
