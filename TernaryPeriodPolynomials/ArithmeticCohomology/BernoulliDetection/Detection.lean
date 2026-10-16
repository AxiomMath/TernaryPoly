module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Binary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

theorem eval_bind_three (first second third : ℂ) (left middle right polynomial : Poly) :
    eval ![first, second, third] (bind₁ ![left, middle, right] polynomial) =
      eval ![eval ![first, second, third] left, eval ![first, second, third] middle,
        eval ![first, second, third] right] polynomial := by
  rw [eval_bind]
  have coordinates : (fun index => eval ![first, second, third] (![left, middle, right] index)) =
      ![eval ![first, second, third] left, eval ![first, second, third] middle,
        eval ![first, second, third] right] := by
    ext index
    fin_cases index <;> simp
  rw [coordinates]

noncomputable def specializeThird (first second : ℂ) (polynomial : Poly) : Polynomial ℂ :=
  eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C second, Polynomial.X] polynomial

theorem specializeThird_eval (first second third : ℂ) (polynomial : Poly) :
    (specializeThird first second polynomial).eval third =
      eval ![first, second, third] polynomial := by
  let evaluation := (Polynomial.evalRingHom third).comp
    (eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C second, Polynomial.X])
  have equality : evaluation = eval ![first, second, third] := by
    apply ringHom_ext
    · intro coefficient
      simp [evaluation]
    · intro index
      fin_cases index <;> simp [evaluation]
  exact congrArg (fun hom => hom polynomial) equality

theorem eval_eq_third_of_eval_ne (left right : Poly) (first second excluded : ℂ)
    (equality : ∀ third : ℂ, third ≠ excluded →
      eval ![first, second, third] left = eval ![first, second, third] right) :
    ∀ third : ℂ, eval ![first, second, third] left =
      eval ![first, second, third] right := by
  have polynomial_eq : specializeThird first second left = specializeThird first second right := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ.sdiff (Set.finite_singleton excluded)).mono
    intro third membership
    have third_ne : third ≠ excluded := by simpa using membership.2
    simpa only [Set.mem_ofPred_eq, specializeThird_eval] using equality third third_ne
  intro third
  simpa only [specializeThird_eval] using
    congrArg (fun polynomial : Polynomial ℂ => polynomial.eval third) polynomial_eq

theorem polynomial_eq_of_second_ne (left right : Poly)
    (equality : ∀ first second third : ℂ, second ≠ 0 →
      eval ![first, second, third] left = eval ![first, second, third] right) :
    left = right := by
  classical
  let sets : Fin 3 → Set ℂ := ![Set.univ, Set.univ \ {0}, Set.univ]
  apply MvPolynomial.funext_set sets
  · intro index
    fin_cases index
    · exact Set.infinite_univ
    · exact Set.infinite_univ.sdiff (Set.finite_singleton 0)
    · exact Set.infinite_univ
  · intro values membership
    have second_ne : values 1 ≠ 0 := by
      have included := membership 1 (Set.mem_univ 1)
      simpa [sets] using included
    have coordinates : ![values 0, values 1, values 2] = values := by
      ext index
      fin_cases index <;> rfl
    simpa only [coordinates] using equality (values 0) (values 1) (values 2) second_ne

theorem primitiveCoordinate_first_independent {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (pure : PureMixedBadLine cocycle) :
    primitiveCoordinate primitive = bind₁ ![0, X 1, X 2] (primitiveCoordinate primitive) := by
  apply polynomial_eq_of_second_ne
  intro first second third second_ne
  simpa [eval_bind_three] using
    primitiveCoordinate_constant_first cocycle primitive primitive_eq pure first second third second_ne

theorem primitiveCoordinate_third_independent {degree : ℕ}
    (polynomial : HomogeneousPoly degree)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (normalized : NormalizedBadLine polynomial cocycle) :
    primitiveCoordinate primitive = bind₁ ![X 0, X 1, 0] (primitiveCoordinate primitive) := by
  apply polynomial_eq_of_second_ne
  intro first second third second_ne
  have periodic (parameter : ℂ) :
      (specializeThird first second (primitiveCoordinate primitive)).eval
          (parameter + 3 * second) =
        (specializeThird first second (primitiveCoordinate primitive)).eval parameter := by
    have first_eq := binary_mixed_coordinate_eval cocycle primitive primitive_eq normalized.1
      1 first second (parameter + 3 * second) (by
        simpa [binaryTransformedSecond] using neg_ne_zero.mpr second_ne)
    have second_eq := binary_mixed_coordinate_eval cocycle primitive primitive_eq normalized.1
      2 first second parameter (by
        simpa [binaryTransformedSecond] using neg_ne_zero.mpr second_ne)
    simp [binaryRational, binaryTransformedSecond, binaryTransformedThird,
      normalized.2.2.1, normalized.2.2.2] at first_eq second_eq
    rw [specializeThird_eval, specializeThird_eval]
    linear_combination first_eq - second_eq
  have constant := polynomial_periodic_constant
    (specializeThird first second (primitiveCoordinate primitive)) (3 * second)
    (mul_ne_zero (by norm_num) second_ne) periodic
  have evaluated := congrArg (fun polynomial : Polynomial ℂ => polynomial.eval third) constant
  simpa [specializeThird_eval, eval_bind_three] using evaluated

theorem normalized_primitiveCoordinate_zero {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (symmetric : SymmetricSolution polynomial)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (normalized : NormalizedBadLine polynomial cocycle) : primitiveCoordinate primitive = 0 := by
  have first_independent := primitiveCoordinate_first_independent cocycle primitive primitive_eq normalized.1
  have third_independent := primitiveCoordinate_third_independent polynomial cocycle primitive primitive_eq normalized
  have reduction (first second third : ℂ) :
      eval ![first, second, third] (primitiveCoordinate primitive) =
        eval ![0, second, 0] (primitiveCoordinate primitive) := by
    have first_eq := congrArg (eval ![first, second, third]) first_independent
    have third_eq := congrArg (eval ![0, second, third]) third_independent
    simp [eval_bind_three] at first_eq third_eq
    exact first_eq.trans third_eq
  have origin : eval ![0, 0, 0] (primitiveCoordinate primitive) = 0 := by
    simp [primitiveCoordinate, radicalContraction]
  have vanishing (second : ℂ) : eval ![0, second, 0] (primitiveCoordinate primitive) = 0 := by
    by_cases second_ne : second ≠ 0
    · have obstruction_zero : eval ![0, 0, second] (bernoulliObstruction polynomial) = 0 := by
        have equality := congrArg (eval ![0, 0, second])
          (bernoulliObstruction_zero_second_variable polynomial symmetric)
        simpa [eval_bind_three] using equality
      have equality := binary_mixed_coordinate_eval cocycle primitive primitive_eq normalized.1
        0 0 0 second (by simpa [binaryTransformedSecond] using second_ne)
      simp [binaryRational, binaryTransformedSecond, binaryTransformedThird,
        normalized.2.1, obstruction_zero, reduction] at equality
      rw [origin, sub_zero] at equality
      exact equality.symm
    · have second_zero : second = 0 := not_ne_iff.mp second_ne
      simpa only [second_zero] using origin
  apply MvPolynomial.funext
  intro values
  have coordinates : ![values 0, values 1, values 2] = values := by
    ext index
    fin_cases index <;> rfl
  have equality := (reduction (values 0) (values 1) (values 2)).trans (vanishing (values 1))
  simpa only [coordinates, map_zero] using equality

theorem normalized_bernoulli_detection {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (symmetric : SymmetricSolution polynomial)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (normalized : NormalizedBadLine polynomial cocycle)
    (vanishing : (globalCoordinates degree trivialCharacter cocycle).2 = 0) :
    bernoulliObstruction polynomial = 0 := by
  obtain ⟨primitive, primitive_eq⟩ := line_primitive_of_zero cocycle vanishing
  have primitive_zero := normalized_primitiveCoordinate_zero polynomial symmetric cocycle
    primitive primitive_eq normalized
  have evaluation (first second third : ℂ) :
      eval ![first, second, third] (bernoulliObstruction polynomial) = 0 := by
    apply eval_eq_third_of_eval_ne (bernoulliObstruction polynomial) 0 first second (2 * second)
      (third := third)
    intro parameter parameter_ne
    have transformed_ne : binaryTransformedSecond 0 second parameter ≠ 0 := by
      simp only [binaryTransformedSecond, Matrix.cons_val_zero]
      intro equality
      apply parameter_ne
      linear_combination equality
    have equality := binary_mixed_coordinate_eval cocycle primitive primitive_eq normalized.1
      0 first second parameter transformed_ne
    simpa [binaryRational, normalized.2.1, primitive_zero] using equality
  apply MvPolynomial.funext
  intro values
  have coordinates : ![values 0, values 1, values 2] = values := by
    ext index
    fin_cases index <;> rfl
  simpa only [coordinates, map_zero] using evaluation (values 0) (values 1) (values 2)

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
