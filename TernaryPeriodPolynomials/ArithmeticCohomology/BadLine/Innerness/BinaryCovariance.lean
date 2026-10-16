module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.UpperTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem radicalPairCoordinate_covariant (n : ℕ) (positive : 0 < n)
    (g : RationalGL3) (a b d e : ℤ) (coordinateAction : Poly →ₐ[ℂ] Poly)
    (first_conjugate : g⁻¹ * Adelic.lineUnipotent 1 0 * g =
      Adelic.lineUnipotent (a : ℚ) (b : ℚ))
    (second_conjugate : g⁻¹ * Adelic.lineUnipotent 0 1 * g =
      Adelic.lineUnipotent (d : ℚ) (e : ℚ))
    (preserves : ∀ q : HomogeneousPoly n, pderiv 0 q.val = 0 →
      pderiv 0 (rationalCoefficientComponent n trivialCharacter g q).val = 0)
    (constant_pair : ∀ q r : HomogeneousPoly n,
      X 2 * (a • rationalCoefficientComponent n trivialCharacter g q +
        b • rationalCoefficientComponent n trivialCharacter g r).val -
      X 1 * (d • rationalCoefficientComponent n trivialCharacter g q +
        e • rationalCoefficientComponent n trivialCharacter g r).val =
      coordinateAction (X 2*q.val-X 1*r.val))
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    radicalPairCoordinate n (rationalCoefficientComponent n trivialCharacter g (values (a,b)))
      (rationalCoefficientComponent n trivialCharacter g (values (d,e))) =
      coordinateAction (radicalPairCoordinate n (values (1,0)) (values (0,1))) := by
  obtain ⟨primitive,q,r,hq,hr,normal_form⟩ := radical_cocycle_normal_form n positive values relation
  let representation := rationalCoefficientComponent n trivialCharacter
  let p' := representation g primitive
  let q' := a • representation g q + b • representation g r
  let r' := d • representation g q + e • representation g r
  have hq' : pderiv 0 q'.val = 0 := by
    simp only [q', Submodule.coe_add,Submodule.coe_smul_of_tower,map_add,map_zsmul,
      preserves q hq,preserves r hr,smul_zero,add_zero,representation]
  have hr' : pderiv 0 r'.val = 0 := by
    simp only [r', Submodule.coe_add,Submodule.coe_smul_of_tower,map_add,map_zsmul,
      preserves q hq,preserves r hr,smul_zero,add_zero,representation]
  have acted (s t : ℤ) (u : RationalGL3)
      (conjugate : g⁻¹*u*g = Adelic.lineUnipotent (s : ℚ) (t : ℚ)) :
      representation g (values (s,t)) = p' - representation u p' +
        (s • representation g q + t • representation g r) := by
    have value := normal_form (s,t)
    change values (s,t) = primitive - representation
      (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive + s • q + t • r at value
    rw [value,map_add,map_add,← conjugate,representation_coboundary_conjugate,
      map_zsmul,map_zsmul]
    exact add_assoc _ _ _
  have first_original : values (1,0) = primitive - representation (Adelic.lineUnipotent 1 0)
      primitive + q := by simpa [integralRadicalHom] using normal_form (1,0)
  have second_original : values (0,1) = primitive - representation (Adelic.lineUnipotent 0 1)
      primitive + r := by simpa [integralRadicalHom] using normal_form (0,1)
  change radicalPairCoordinate n (representation g _) (representation g _) = _
  rw [acted a b _ first_conjugate,acted d e _ second_conjugate,first_original,second_original]
  change radicalPairCoordinate n (p'-representation (Adelic.lineUnipotent 1 0) p'+q')
    (p'-representation (Adelic.lineUnipotent 0 1) p'+r') = _
  simp only [radicalPairCoordinate]
  rw [radicalCoordinate_normal_form n positive p' q' r' hq' hr',
    radicalCoordinate_normal_form n positive primitive q r hq hr]
  exact constant_pair q r

def binaryRSubstitution : Poly →ₐ[ℂ] Poly := bind₁ ![X 0,-X 1,X 2]
def upperTranslationSubstitution : Poly →ₐ[ℂ] Poly := bind₁ ![X 0,X 1-X 2,X 2]

theorem rationalCoefficient_binaryR (n : ℕ) (p : HomogeneousPoly n) :
    (rationalCoefficientComponent n trivialCharacter binaryR p).val =
      -binaryRSubstitution p.val := by
  rw [rationalCoefficient_trivial_coe,action_apply]
  let matrix := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) binaryR)
  have determinant_eq : determinantCharacter (-1) matrix = -1 := by
    simp [matrix,determinantCharacter,GeneralLinearGroup.det,
      GeneralLinearGroup.map_apply,binaryR,Matrix.det_fin_three]
  rw [determinant_eq,neg_one_smul]
  congr 1
  have forms : linearForm (matrix⁻¹).val = ![X 0,-X 1,X 2] := by
    dsimp only [matrix]
    rw [← map_inv,← map_inv]
    funext i
    fin_cases i <;> simp [linearForm,GeneralLinearGroup.map_apply,binaryR,Fin.sum_univ_three]
  change substitute (matrix⁻¹).val p.val = binaryRSubstitution p.val
  rw [substitute,forms]
  rfl

theorem rationalCoefficient_upperTranslation (n : ℕ) (p : HomogeneousPoly n) :
    (rationalCoefficientComponent n trivialCharacter upperTranslation p).val =
      upperTranslationSubstitution p.val := by
  rw [rationalCoefficient_trivial_coe,action_apply]
  let matrix := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) upperTranslation)
  have determinant_eq : determinantCharacter (-1) matrix = 1 := by
    simp [matrix,determinantCharacter,GeneralLinearGroup.det,
      GeneralLinearGroup.map_apply,upperTranslation,integralUpperTranslation,Matrix.det_fin_three]
  rw [determinant_eq,one_smul]
  have forms : linearForm (matrix⁻¹).val = ![X 0,X 1-X 2,X 2] := by
    dsimp only [matrix]
    rw [← map_inv,← map_inv]
    unfold upperTranslation
    rw [← map_inv]
    funext i
    fin_cases i <;>
      simp [linearForm,GeneralLinearGroup.map_apply,integralUpperTranslation,
        Fin.sum_univ_three,sub_eq_add_neg]
  change substitute (matrix⁻¹).val p.val = upperTranslationSubstitution p.val
  rw [substitute,forms]
  rfl

theorem binaryRSubstitution_preserves (p : Poly) (independent : pderiv 0 p = 0) :
    pderiv 0 (binaryRSubstitution p) = 0 := by
  rw [← removeFirstVariable_eq_of_pderiv_zero p independent]
  change pderiv 0 (bind₁ _ (removeFirstVariable p)) = 0
  rw [bind_removeFirstVariable]
  apply pderiv_bind_eq_zero
  intro i
  fin_cases i <;> simp

theorem upperTranslationSubstitution_preserves (p : Poly) (independent : pderiv 0 p = 0) :
    pderiv 0 (upperTranslationSubstitution p) = 0 := by
  rw [← removeFirstVariable_eq_of_pderiv_zero p independent]
  change pderiv 0 (bind₁ _ (removeFirstVariable p)) = 0
  rw [bind_removeFirstVariable]
  apply pderiv_bind_eq_zero
  intro i
  fin_cases i <;> simp

theorem radicalPairCoordinate_binaryR (n : ℕ) (positive : 0 < n)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    radicalPairCoordinate n (rationalCoefficientComponent n trivialCharacter binaryR (values (-1,0)))
      (rationalCoefficientComponent n trivialCharacter binaryR (values (0,1))) =
      binaryRSubstitution (radicalPairCoordinate n (values (1,0)) (values (0,1))) := by
  apply radicalPairCoordinate_covariant n positive binaryR (-1) 0 0 1 binaryRSubstitution
    (by simpa using binaryR_conjugate 1 0) (by simpa using binaryR_conjugate 0 1)
    ?_ ?_ values relation
  · intro p hp
    rw [rationalCoefficient_binaryR,map_neg,binaryRSubstitution_preserves p.val hp,neg_zero]
  · intro q r
    simp [rationalCoefficient_binaryR,binaryRSubstitution]

theorem radicalPairCoordinate_upperTranslation (n : ℕ) (positive : 0 < n)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    radicalPairCoordinate n
      (rationalCoefficientComponent n trivialCharacter upperTranslation (values (1,1)))
      (rationalCoefficientComponent n trivialCharacter upperTranslation (values (0,1))) =
      upperTranslationSubstitution (radicalPairCoordinate n (values (1,0)) (values (0,1))) := by
  apply radicalPairCoordinate_covariant n positive upperTranslation 1 1 0 1 upperTranslationSubstitution
    (by simpa using upperTranslation_conjugate 1 0) (by simpa using upperTranslation_conjugate 0 1)
    ?_ ?_ values relation
  · intro p hp
    rw [rationalCoefficient_upperTranslation]
    exact upperTranslationSubstitution_preserves p.val hp
  · intro q r
    simp [rationalCoefficient_upperTranslation,upperTranslationSubstitution]
    ring

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
