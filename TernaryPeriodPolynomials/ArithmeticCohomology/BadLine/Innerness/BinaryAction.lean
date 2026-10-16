module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalNormalForm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def binaryASubstitution : Poly →ₐ[ℂ] Poly := bind₁ ![X 0,-2*X 1+X 2,-3*X 1+X 2]

theorem rationalCoefficient_binaryA (n : ℕ) (p : HomogeneousPoly n) :
    (rationalCoefficientComponent n trivialCharacter binaryA p).val =
      binaryASubstitution p.val := by
  rw [rationalCoefficient_trivial_coe, action_apply]
  let matrix := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) binaryA)
  have determinant_eq : determinantCharacter (-1) matrix = 1 := by
    simp [matrix, determinantCharacter, GeneralLinearGroup.det,
      GeneralLinearGroup.map_apply, binaryA, Matrix.det_fin_three]
    norm_num
  rw [determinant_eq, one_smul]
  have forms : linearForm (matrix⁻¹).val = ![X 0,-2*X 1+X 2,-3*X 1+X 2] := by
    dsimp only [matrix]
    rw [← map_inv, ← map_inv]
    funext i
    fin_cases i <;>
      simp [linearForm, GeneralLinearGroup.map_apply, binaryA, Fin.sum_univ_three,
        map_ofNat]
  change substitute (matrix⁻¹).val p.val = binaryASubstitution p.val
  rw [substitute, forms]
  rfl

theorem pderiv_bind_eq_zero (values : Fin 3 → Poly)
    (independent : ∀ i, pderiv 0 (values i) = 0) (p : Poly) :
    pderiv 0 (bind₁ values p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [map_mul, pderiv_mul, hp, bind₁_X_right, independent, zero_mul, mul_zero, add_zero]

theorem bind_removeFirstVariable (values : Fin 3 → Poly) (p : Poly) :
    bind₁ values (removeFirstVariable p) = bind₁ ![0,values 1,values 2] p := by
  have hom_eq : (bind₁ values).comp removeFirstVariable = bind₁ ![0,values 1,values 2] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [removeFirstVariable]
  exact congrArg (fun hom : Poly →ₐ[ℂ] Poly => hom p) hom_eq

theorem binaryASubstitution_preserves_independence (p : Poly)
    (independent : pderiv 0 p = 0) : pderiv 0 (binaryASubstitution p) = 0 := by
  have derivative_two : pderiv 0 (2 : Poly) = 0 := by
    change pderiv 0 (C (2 : ℂ)) = 0
    exact pderiv_C
  have derivative_three : pderiv 0 (3 : Poly) = 0 := by
    change pderiv 0 (C (3 : ℂ)) = 0
    exact pderiv_C
  rw [← removeFirstVariable_eq_of_pderiv_zero p independent]
  change pderiv 0 (bind₁ _ (removeFirstVariable p)) = 0
  rw [bind_removeFirstVariable]
  apply pderiv_bind_eq_zero
  intro i
  fin_cases i <;> simp [derivative_two, derivative_three]

theorem bernoulliOperator_add (n : ℕ) (t p q : Poly) :
    bernoulliOperator n t (p+q) = bernoulliOperator n t p + bernoulliOperator n t q := by
  rw [← sub_neg_eq_add, bernoulliOperator_sub, bernoulliOperator_neg, sub_neg_eq_add]

theorem radicalCoordinate_normal_form (n : ℕ) (positive : 0 < n)
    (primitive a b : HomogeneousPoly n)
    (a_independent : pderiv 0 a.val = 0) (b_independent : pderiv 0 b.val = 0) :
    X 2 * bernoulliOperator n (X 1)
      (primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 1 0) primitive + a).val -
    X 1 * bernoulliOperator n (X 2)
      (primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 0 1) primitive + b).val = X 2*a.val - X 1*b.val := by
  simp only [Submodule.coe_add, Submodule.coe_sub, bernoulliOperator_add,
    bernoulliOperator_eq_of_pderiv_zero n (X 1) a.val a_independent,
    bernoulliOperator_eq_of_pderiv_zero n (X 2) b.val b_independent]
  linear_combination radical_coboundary_bernoulli_zero n positive primitive

theorem representation_coboundary_conjugate {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] (representation : Representation ℂ G V) (g u : G) (p : V) :
    representation g (p - representation (g⁻¹*u*g) p) =
      representation g p - representation u (representation g p) := by
  rw [map_sub, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem radicalCoordinate_binaryA (n : ℕ) (positive : 0 < n)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    X 2 * bernoulliOperator n (X 1)
        (rationalCoefficientComponent n trivialCharacter binaryA (values (1,-1))).val -
      X 1 * bernoulliOperator n (X 2)
        (rationalCoefficientComponent n trivialCharacter binaryA (values (3,-2))).val =
    binaryASubstitution (X 2 * bernoulliOperator n (X 1) (values (1,0)).val -
      X 1 * bernoulliOperator n (X 2) (values (0,1)).val) := by
  obtain ⟨primitive,a,b,ha,hb,normal_form⟩ := radical_cocycle_normal_form n positive values relation
  let representation := rationalCoefficientComponent n trivialCharacter
  let p' := representation binaryA primitive
  let a' := representation binaryA a - representation binaryA b
  let b' := (3 : ℤ) • representation binaryA a - (2 : ℤ) • representation binaryA b
  have acted_independent (q : HomogeneousPoly n) (hq : pderiv 0 q.val = 0) :
      pderiv 0 (representation binaryA q).val = 0 := by
    rw [rationalCoefficient_binaryA]
    exact binaryASubstitution_preserves_independence q.val hq
  have ha' : pderiv 0 a'.val = 0 := by
    simp only [a', Submodule.coe_sub, map_sub, acted_independent a ha, acted_independent b hb,
      sub_self]
  have hb' : pderiv 0 b'.val = 0 := by
    simp only [b', Submodule.coe_sub, Submodule.coe_smul_of_tower, map_sub, map_zsmul,
      acted_independent a ha, acted_independent b hb, smul_zero, sub_self]
  have first_conjugate : binaryA⁻¹ * Adelic.lineUnipotent 1 0 * binaryA =
      Adelic.lineUnipotent (1 : ℚ) (-1 : ℚ) := by
    simpa using binaryA_conjugate 1 0
  have second_conjugate : binaryA⁻¹ * Adelic.lineUnipotent 0 1 * binaryA =
      Adelic.lineUnipotent (3 : ℚ) (-2 : ℚ) := by
    simpa using binaryA_conjugate 0 1
  have first_value : representation binaryA (values (1,-1)) =
      p' - representation (Adelic.lineUnipotent 1 0) p' + a' := by
    have value := normal_form (1,-1)
    simp only [one_smul, neg_smul, integralRadicalHom,
      MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Int.cast_one, Int.cast_neg] at value
    rw [value, map_add, map_add]
    rw [← first_conjugate, representation_coboundary_conjugate, map_neg]
    dsimp only [p', a']
    simp only [sub_eq_add_neg, add_assoc]
  have second_value : representation binaryA (values (3,-2)) =
      p' - representation (Adelic.lineUnipotent 0 1) p' + b' := by
    have value := normal_form (3,-2)
    simp only [integralRadicalHom,
      MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Int.cast_ofNat, Int.cast_neg] at value
    rw [value, map_add, map_add, ← second_conjugate, representation_coboundary_conjugate]
    simp only [map_zsmul, neg_smul, map_neg]
    dsimp only [p', b']
    simp only [sub_eq_add_neg, add_assoc]
  have first_original : values (1,0) = primitive - representation (Adelic.lineUnipotent 1 0)
      primitive + a := by simpa [integralRadicalHom] using normal_form (1,0)
  have second_original : values (0,1) = primitive - representation (Adelic.lineUnipotent 0 1)
      primitive + b := by simpa [integralRadicalHom] using normal_form (0,1)
  rw [first_value, second_value, radicalCoordinate_normal_form n positive p' a' b' ha' hb',
    first_original, second_original, radicalCoordinate_normal_form n positive primitive a b ha hb]
  simp only [a', b', Submodule.coe_sub, Submodule.coe_smul_of_tower, zsmul_eq_mul, representation,
    rationalCoefficient_binaryA, map_sub, map_mul]
  simp [binaryASubstitution]
  ring

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
