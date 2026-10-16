module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BinaryMatrices

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def bernoulliEnd (n : ℕ) (positive : 0 < n) (t : Poly) (linear : t.IsHomogeneous 1) :
    Module.End ℂ (HomogeneousPoly n) :=
  ∑ k ∈ Finset.range (n+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) •
    (polynomialTranslationDerivative n positive t linear)^k

def translationEnd (n : ℕ) (positive : 0 < n) (t : Poly) (linear : t.IsHomogeneous 1) :
    Module.End ℂ (HomogeneousPoly n) :=
  ∑ k ∈ Finset.range (n+1), (k.factorial : ℂ)⁻¹ •
    (polynomialTranslationDerivative n positive t linear)^k

theorem bernoulliEnd_apply (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) :
    (bernoulliEnd n positive t linear p).val = bernoulliOperator n t p.val :=
  (bernoulliOperator_eq_endomorphism n positive t linear independent p).symm

theorem translationEnd_apply (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) :
    (translationEnd n positive t linear p).val = bind₁ ![X 0-t,X 1,X 2] p.val := by
  simp only [translationEnd, LinearMap.sum_apply, Submodule.coe_sum,
    LinearMap.smul_apply, Submodule.coe_smul,
    polynomialTranslationDerivative_pow n positive t linear independent]
  exact (homogeneous_translation_taylor p t).symm

theorem bernoulliEnd_translation (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0) :
    bernoulliEnd n positive t linear * (translationEnd n positive t linear - 1) =
      polynomialTranslationDerivative n positive t linear :=
  nilpotent_bernoulli_sum_identity (N := n+1) (by omega)
    (polynomialTranslationDerivative n positive t linear)
    (polynomialTranslationDerivative_nilpotent n positive t linear independent)

theorem polynomialTranslationDerivative_commute (n : ℕ) (positive : 0 < n)
    (s t : Poly) (s_linear : s.IsHomogeneous 1) (t_linear : t.IsHomogeneous 1)
    (s_independent : pderiv 0 s = 0) (t_independent : pderiv 0 t = 0) :
    Commute (polynomialTranslationDerivative n positive s s_linear)
      (polynomialTranslationDerivative n positive t t_linear) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change -s * pderiv 0 (-t * pderiv 0 p.val) =
    -t * pderiv 0 (-s * pderiv 0 p.val)
  rw [pderiv_mul, pderiv_mul, map_neg, map_neg, s_independent, t_independent]
  ring

theorem derivative_bernoulliEnd_commute (n : ℕ) (positive : 0 < n)
    (s t : Poly) (s_linear : s.IsHomogeneous 1) (t_linear : t.IsHomogeneous 1)
    (s_independent : pderiv 0 s = 0) (t_independent : pderiv 0 t = 0) :
    Commute (polynomialTranslationDerivative n positive s s_linear)
      (bernoulliEnd n positive t t_linear) := by
  apply Commute.sum_right
  intro k _
  exact ((polynomialTranslationDerivative_commute n positive s t s_linear t_linear
    s_independent t_independent).pow_right k).smul_right _

theorem bernoulliEnd_commute (n : ℕ) (positive : 0 < n)
    (s t : Poly) (s_linear : s.IsHomogeneous 1) (t_linear : t.IsHomogeneous 1)
    (s_independent : pderiv 0 s = 0) (t_independent : pderiv 0 t = 0) :
    Commute (bernoulliEnd n positive s s_linear) (bernoulliEnd n positive t t_linear) := by
  apply Commute.sum_left
  intro k _
  exact ((derivative_bernoulliEnd_commute n positive s t s_linear t_linear
    s_independent t_independent).pow_left k).smul_left _

theorem radicalCoordinate_pderiv_zero (n : ℕ) (positive : 0 < n)
    (first second : HomogeneousPoly n)
    (compatibility :
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 0 1) first - first =
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 1 0) second - second) :
    pderiv 0 (X 2 * bernoulliOperator n (X 1) first.val -
      X 1 * bernoulliOperator n (X 2) second.val) = 0 := by
  let D₁ := polynomialTranslationDerivative n positive (X 1) (isHomogeneous_X ℂ 1)
  let D₂ := polynomialTranslationDerivative n positive (X 2) (isHomogeneous_X ℂ 2)
  let B₁ := bernoulliEnd n positive (X 1) (isHomogeneous_X ℂ 1)
  let B₂ := bernoulliEnd n positive (X 2) (isHomogeneous_X ℂ 2)
  let E₁ := translationEnd n positive (X 1) (isHomogeneous_X ℂ 1)
  let E₂ := translationEnd n positive (X 2) (isHomogeneous_X ℂ 2)
  have first_translation (p : HomogeneousPoly n) : E₁ p =
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 1 0) p := by
    apply Subtype.ext
    rw [translationEnd_apply n positive (X 1) (isHomogeneous_X ℂ 1) (by simp),
      rationalCoefficient_lineUnipotent]
    simp [evalTriple, aeval_eq_bind₁]
  have second_translation (p : HomogeneousPoly n) : E₂ p =
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 0 1) p := by
    apply Subtype.ext
    rw [translationEnd_apply n positive (X 2) (isHomogeneous_X ℂ 2) (by simp),
      rationalCoefficient_lineUnipotent]
    simp [evalTriple, aeval_eq_bind₁]
  have first_inverse : B₁ * (E₁-1) = D₁ :=
    bernoulliEnd_translation n positive (X 1) (isHomogeneous_X ℂ 1) (by simp)
  have second_inverse : B₂ * (E₂-1) = D₂ :=
    bernoulliEnd_translation n positive (X 2) (isHomogeneous_X ℂ 2) (by simp)
  have derivative_first : Commute D₂ B₁ := derivative_bernoulliEnd_commute n positive
    (X 2) (X 1) (isHomogeneous_X ℂ 2) (isHomogeneous_X ℂ 1) (by simp) (by simp)
  have derivative_second : Commute D₁ B₂ := derivative_bernoulliEnd_commute n positive
    (X 1) (X 2) (isHomogeneous_X ℂ 1) (isHomogeneous_X ℂ 2) (by simp) (by simp)
  have bernoulli_commute : Commute B₁ B₂ := bernoulliEnd_commute n positive
    (X 1) (X 2) (isHomogeneous_X ℂ 1) (isHomogeneous_X ℂ 2) (by simp) (by simp)
  have differences : (E₂-1) first = (E₁-1) second := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, first_translation,
      second_translation] using compatibility
  have relation : D₂ (B₁ first) = D₁ (B₂ second) := by
    calc
      D₂ (B₁ first) = B₁ (D₂ first) := congrArg (fun operator => operator first) derivative_first.eq
      _ = B₁ (B₂ ((E₂-1) first)) := by rw [← Module.End.mul_apply B₂, second_inverse]
      _ = B₁ (B₂ ((E₁-1) second)) := by rw [differences]
      _ = B₂ (B₁ ((E₁-1) second)) :=
        congrArg (fun operator => operator ((E₁-1) second)) bernoulli_commute.eq
      _ = B₂ (D₁ second) := by rw [← Module.End.mul_apply B₁, first_inverse]
      _ = D₁ (B₂ second) :=
        (congrArg (fun operator => operator second) derivative_second.eq).symm
  have coefficients := congrArg Subtype.val relation
  change -X 2 * pderiv 0 (B₁ first).val = -X 1 * pderiv 0 (B₂ second).val at coefficients
  rw [bernoulliEnd_apply n positive (X 1) (isHomogeneous_X ℂ 1) (by simp),
    bernoulliEnd_apply n positive (X 2) (isHomogeneous_X ℂ 2) (by simp)] at coefficients
  simp only [map_sub, pderiv_mul, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0),
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0), zero_mul, zero_add]
  linear_combination -coefficients

theorem mixedBernoulliCoordinate_pderiv_zero (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ)) :
    pderiv 0 (mixedBernoulliCoordinate c levi.val) = 0 := by
  let b := fun x : ℤ × ℤ => mixedValue rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c levi.val
      (integralRadicalHom (Multiplicative.ofAdd x))
  have first := mixedValue_integralRadical_cocycle n c pure levi normalizes (1,0) (0,1)
  have second := mixedValue_integralRadical_cocycle n c pure levi normalizes (0,1) (1,0)
  have relation : b (1,0) + rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 1 0) (b (0,1)) =
    b (0,1) + rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 0 1) (b (1,0)) := by
    simpa [b, integralRadicalHom] using first.symm.trans second
  have compatibility : rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 0 1) (b (1,0)) - b (1,0) =
    rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 1 0) (b (0,1)) - b (0,1) := by
    apply sub_eq_zero.mp
    calc
      _ = (b (0,1) + rationalCoefficientComponent n trivialCharacter
          (Adelic.lineUnipotent 0 1) (b (1,0))) -
        (b (1,0) + rationalCoefficientComponent n trivialCharacter
          (Adelic.lineUnipotent 1 0) (b (0,1))) := by abel
      _ = 0 := sub_eq_zero.mpr relation.symm
  have independent := radicalCoordinate_pderiv_zero n positive (b (1,0)) (b (0,1)) compatibility
  simpa [b, integralRadicalHom, mixedValue_eq_mixedBarEdge, mixedBernoulliCoordinate]
    using independent

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
