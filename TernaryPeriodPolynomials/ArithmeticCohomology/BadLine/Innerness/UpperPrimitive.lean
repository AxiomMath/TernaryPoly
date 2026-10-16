module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.UpperGroup

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def radicalLinearValues (n : ℕ) (a b : HomogeneousPoly n) (g : RationalGL3) : HomogeneousPoly n :=
  (g.val 0 1 : ℂ) • a+(g.val 0 2 : ℂ) • b

theorem radicalLinearValues_apply (n : ℕ) (a b : HomogeneousPoly n) (s t : ℤ) :
    radicalLinearValues n a b (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) = s • a+t • b := by
  change ((s : ℚ) : ℂ) • a+((t : ℚ) : ℂ) • b = s • a+t • b
  rw [Rat.cast_intCast,Rat.cast_intCast]
  exact congrArg₂ (fun x y : HomogeneousPoly n => x+y)
    (Int.cast_smul_eq_zsmul ℂ s a) (Int.cast_smul_eq_zsmul ℂ t b)

theorem radicalLinearValues_add (n : ℕ) (a b : HomogeneousPoly n)
    (ha : pderiv 0 a.val = 0) (hb : pderiv 0 b.val = 0) (s t s' t' : ℤ) :
    radicalLinearValues n a b
      (Adelic.lineUnipotent (s : ℚ) (t : ℚ)*Adelic.lineUnipotent (s' : ℚ) (t' : ℚ)) =
      radicalLinearValues n a b (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) +
        rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent (s : ℚ) (t : ℚ))
          (radicalLinearValues n a b (Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))) := by
  rw [← Adelic.lineUnipotent_add,← Int.cast_add,← Int.cast_add]
  simp only [radicalLinearValues_apply]
  exact independent_pair_cocycle n a b ha hb (s,t) (s',t')

theorem normalizedBadLine_upperGroup_primitive (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∃ primitive : cochains integralUpperGroup (rationalCoefficientComponent n trivialCharacter) 1,
      ∀ vertices, (differentialOne integralUpperGroup
        (rationalCoefficientComponent n trivialCharacter) primitive).val vertices = c.val.val vertices := by
  obtain ⟨a,b,correction,ha,hb,correction_relation,mixed⟩ :=
    normalizedBadLine_cyclic_mixed_primitive n positive f solution c normalized
  apply cocycle_primitive_of_factorization_correction rationalLevel integralUpperGroup
    integralUpperGroup_le (rationalCoefficientComponent n trivialCharacter) c upperRadical upperLevi
    upper_factorization upperRadical_product upperLevi_product
    ?_ ?_ (radicalLinearValues n a b) ?_ (fun g => correction (upperParameters g).2.2) ?_ ?_
  · intro g h
    change barValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
      (Adelic.lineUnipotent ((upperParameters g).1 : ℚ) ((upperParameters g).2.1 : ℚ))
      (upperTranslationAt (upperParameters g).2.2*
        Adelic.lineUnipotent ((upperParameters h).1 : ℚ) ((upperParameters h).2.1 : ℚ)*
          (upperTranslationAt (upperParameters g).2.2)⁻¹) = 0
    rw [upperTranslationAt_forward_conjugate]
    exact pureMixed_radical_bar c normalized.1 _ _ _ _
  · intro g h
    exact pureMixed_upperTranslation_bar n c normalized.1 _ _
  · intro g h
    change radicalLinearValues n a b
        (Adelic.lineUnipotent ((upperParameters g).1 : ℚ) ((upperParameters g).2.1 : ℚ)*
          (upperTranslationAt (upperParameters g).2.2*
            Adelic.lineUnipotent ((upperParameters h).1 : ℚ) ((upperParameters h).2.1 : ℚ)*
              (upperTranslationAt (upperParameters g).2.2)⁻¹)) = _
    simp only [upperRadical,upperLevi,upperTranslationAt_forward_conjugate]
    exact radicalLinearValues_add n a b ha hb _ _ _ _
  · intro g h
    rw [upperParameters_mul]
    exact correction_relation _ _
  · intro g h
    change mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
        (upperTranslationAt (upperParameters g).2.2)
        (upperTranslationAt (upperParameters g).2.2*
          Adelic.lineUnipotent ((upperParameters h).1 : ℚ) ((upperParameters h).2.1 : ℚ)*
            (upperTranslationAt (upperParameters g).2.2)⁻¹) + _ - _ = _
    simp only [upperRadical,upperLevi,upperTranslationAt_forward_conjugate,radicalLinearValues_apply]
    have equation := mixed (upperParameters g).2.2 (upperParameters h).1
      ((upperParameters h).2.1-(upperParameters g).2.2*(upperParameters h).1)
    have cancellation : (upperParameters g).2.2*(upperParameters h).1+
        ((upperParameters h).2.1-(upperParameters g).2.2*(upperParameters h).1) =
      (upperParameters h).2.1 := by ring
    rw [cancellation] at equation
    exact equation

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
