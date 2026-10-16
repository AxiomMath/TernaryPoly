module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalCoordinate

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def removeFirstVariable : Poly →ₐ[ℂ] Poly := bind₁ ![0,X 1,X 2]

theorem removeFirstVariable_pderiv (p : Poly) : pderiv 0 (removeFirstVariable p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [removeFirstVariable]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [map_mul, pderiv_mul, hp, zero_mul, zero_add]
    fin_cases i <;> simp [removeFirstVariable]

theorem removeFirstVariable_homogeneous {n : ℕ} (p : Poly)
    (homogeneous : p.IsHomogeneous n) : (removeFirstVariable p).IsHomogeneous n := by
  have homogeneous_images (i : Fin 3) : (![0,X 1,X 2] i : Poly).IsHomogeneous 1 := by
    fin_cases i
    · exact isHomogeneous_zero (Fin 3) ℂ 1
    · exact isHomogeneous_X ℂ 1
    · exact isHomogeneous_X ℂ 2
  simpa only [removeFirstVariable, aeval_eq_bind₁, one_mul] using
    homogeneous.aeval ![0,X 1,X 2] homogeneous_images

def independentPart (n : ℕ) (p : HomogeneousPoly n) : HomogeneousPoly n :=
  ⟨removeFirstVariable p.val, removeFirstVariable_homogeneous p.val p.property⟩

theorem firstPolynomial_constant_of_pderiv_zero (p : Poly) (independent : pderiv 0 p = 0) :
    firstPolynomial p = Polynomial.C ((firstPolynomial p).coeff 0) := by
  apply Polynomial.eq_C_of_derivative_eq_zero
  rw [← firstPolynomial_pderiv, independent, map_zero]

theorem removeFirstVariable_eq_of_pderiv_zero (p : Poly) (independent : pderiv 0 p = 0) :
    removeFirstVariable p = p := by
  have constant := firstPolynomial_constant_of_pderiv_zero p independent
  have first := congrArg (Polynomial.eval (0 : Poly)) constant
  have second := congrArg (Polynomial.eval (X 0 : Poly)) constant
  rw [firstPolynomial_eval, Polynomial.eval_C] at first
  rw [firstPolynomial_eval_X, Polynomial.eval_C] at second
  exact first.trans second.symm

theorem bernoulliOperator_eq_of_pderiv_zero (n : ℕ) (t p : Poly)
    (independent : pderiv 0 p = 0) : bernoulliOperator n t p = p := by
  have higher_zero (k : ℕ) (positive : 0 < k) :
      ((fun q : Poly => pderiv 0 q)^[k]) p = 0 := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    rw [Function.iterate_succ_apply, independent]
    clear positive
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, map_zero]
  unfold bernoulliOperator
  rw [Finset.sum_eq_single 0]
  · simp [bernoulli_zero]
  · intro k _ nonzero
    rw [higher_zero k (Nat.pos_of_ne_zero nonzero), mul_zero]
  · simp

theorem bernoulliOperator_sub (n : ℕ) (t p q : Poly) :
    bernoulliOperator n t (p-q) = bernoulliOperator n t p - bernoulliOperator n t q := by
  have derivative_sub (k : ℕ) : ((fun r : Poly => pderiv 0 r)^[k]) (p-q) =
      ((fun r : Poly => pderiv 0 r)^[k]) p - ((fun r : Poly => pderiv 0 r)^[k]) q := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_sub,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
  simp only [bernoulliOperator, derivative_sub, mul_sub, Finset.sum_sub_distrib]

theorem rationalCoefficient_fixes_independent (n : ℕ) (p : HomogeneousPoly n)
    (independent : pderiv 0 p.val = 0) (s t : ℚ) :
    rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent s t) p = p := by
  apply Subtype.ext
  rw [rationalCoefficient_lineUnipotent]
  change bind₁ ![X 0-C (s : ℂ)*X 1-C (t : ℂ)*X 2,X 1,X 2] p.val = p.val
  rw [← firstPolynomial_eval, firstPolynomial_constant_of_pderiv_zero p.val independent,
    Polynomial.eval_C]
  have constant := congrArg (Polynomial.eval (X 0 : Poly))
    (firstPolynomial_constant_of_pderiv_zero p.val independent)
  simpa only [firstPolynomial_eval_X, Polynomial.eval_C] using constant.symm

theorem radical_pair_normal_form (n : ℕ) (positive : 0 < n)
    (first second : HomogeneousPoly n)
    (compatibility :
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 0 1) first - first =
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 1 0) second - second) :
    ∃ primitive a b : HomogeneousPoly n,
      pderiv 0 a.val = 0 ∧ pderiv 0 b.val = 0 ∧
      first = primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 1 0) primitive + a ∧
      second = primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 0 1) primitive + b := by
  let alpha := bernoulliEnd n positive (X 1) (isHomogeneous_X ℂ 1) first
  let beta := bernoulliEnd n positive (X 2) (isHomogeneous_X ℂ 2) second
  let a := independentPart n alpha
  let b := independentPart n beta
  have a_independent : pderiv 0 a.val = 0 := removeFirstVariable_pderiv alpha.val
  have b_independent : pderiv 0 b.val = 0 := removeFirstVariable_pderiv beta.val
  have alpha_eq : alpha.val = bernoulliOperator n (X 1) first.val :=
    bernoulliEnd_apply n positive (X 1) (isHomogeneous_X ℂ 1) (by simp) first
  have beta_eq : beta.val = bernoulliOperator n (X 2) second.val :=
    bernoulliEnd_apply n positive (X 2) (isHomogeneous_X ℂ 2) (by simp) second
  have independent : pderiv 0 (X 2 * alpha.val - X 1 * beta.val) = 0 := by
    rw [alpha_eq,beta_eq]
    exact radicalCoordinate_pderiv_zero n positive first second compatibility
  have projected := removeFirstVariable_eq_of_pderiv_zero _ independent
  have coordinate_eq : X 2 * a.val - X 1 * b.val = X 2 * alpha.val - X 1 * beta.val := by
    simpa [a, b, independentPart, removeFirstVariable] using projected
  have zero_coordinate : X 2 * bernoulliOperator n (X 1) (first-a).val -
      X 1 * bernoulliOperator n (X 2) (second-b).val = 0 := by
    simp only [Submodule.coe_sub, bernoulliOperator_sub,
      bernoulliOperator_eq_of_pderiv_zero n (X 1) a.val a_independent,
      bernoulliOperator_eq_of_pderiv_zero n (X 2) b.val b_independent]
    rw [← alpha_eq, ← beta_eq]
    linear_combination -coordinate_eq
  obtain ⟨primitive,first_eq,second_eq⟩ := radical_primitive_of_bernoulli_zero n positive
    (first-a) (second-b) zero_coordinate
  refine ⟨primitive,a,b,a_independent,b_independent,?_,?_⟩
  · exact (sub_eq_iff_eq_add.mp first_eq)
  · exact (sub_eq_iff_eq_add.mp second_eq)

theorem radical_cocycle_normal_form (n : ℕ) (positive : 0 < n)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    ∃ primitive a b : HomogeneousPoly n,
      pderiv 0 a.val = 0 ∧ pderiv 0 b.val = 0 ∧ ∀ x : ℤ × ℤ,
      values x = primitive - rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) primitive + x.1 • a + x.2 • b := by
  have first := relation (1,0) (0,1)
  have second := relation (0,1) (1,0)
  have equation : values (1,0) + rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 1 0) (values (0,1)) =
    values (0,1) + rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 0 1) (values (1,0)) := by
    simpa [integralRadicalHom] using first.symm.trans second
  have compatibility : rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 0 1) (values (1,0)) - values (1,0) =
    rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 1 0) (values (0,1)) - values (0,1) := by
    apply sub_eq_zero.mp
    calc
      _ = (values (0,1) + rationalCoefficientComponent n trivialCharacter
          (Adelic.lineUnipotent 0 1) (values (1,0))) -
        (values (1,0) + rationalCoefficientComponent n trivialCharacter
          (Adelic.lineUnipotent 1 0) (values (0,1))) := by abel
      _ = 0 := sub_eq_zero.mpr equation.symm
  obtain ⟨primitive,a,b,a_independent,b_independent,first_eq,second_eq⟩ :=
    radical_pair_normal_form n positive (values (1,0)) (values (0,1)) compatibility
  let representation := (rationalCoefficientComponent n trivialCharacter).comp integralRadicalHom
  have fixes_a (x : ℤ × ℤ) : representation (Multiplicative.ofAdd x) a = a :=
    rationalCoefficient_fixes_independent n a a_independent (x.1 : ℚ) (x.2 : ℚ)
  have fixes_b (x : ℤ × ℤ) : representation (Multiplicative.ofAdd x) b = b :=
    rationalCoefficient_fixes_independent n b b_independent (x.1 : ℚ) (x.2 : ℚ)
  have equal := integerPair_cocycle_ext representation values
    (fun x => primitive - representation (Multiplicative.ofAdd x) primitive + x.1 • a + x.2 • b)
    relation (by
      intro x y
      simp only [ofAdd_add, map_mul, Module.End.mul_apply, Prod.fst_add, Prod.snd_add,
        add_smul, map_add, map_sub, map_zsmul, fixes_a, fixes_b]
      abel)
    (by simpa [representation, integralRadicalHom] using first_eq)
    (by simpa [representation, integralRadicalHom] using second_eq)
  exact ⟨primitive,a,b,a_independent,b_independent,fun x => congrFun equal x⟩

theorem mixed_radical_normal_form (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ)) :
    ∃ primitive a b : HomogeneousPoly n,
      pderiv 0 a.val = 0 ∧ pderiv 0 b.val = 0 ∧ ∀ s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi.val
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive + s • a + t • b := by
  obtain ⟨primitive,a,b,ha,hb,values⟩ := radical_cocycle_normal_form n positive
    (fun x => mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c levi.val (integralRadicalHom (Multiplicative.ofAdd x)))
    (mixedValue_integralRadical_cocycle n c pure levi normalizes)
  exact ⟨primitive,a,b,ha,hb,fun s t => values (s,t)⟩

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
