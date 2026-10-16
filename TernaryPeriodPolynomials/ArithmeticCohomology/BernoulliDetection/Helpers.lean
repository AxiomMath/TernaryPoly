module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

open MvPolynomial

theorem line_primitive_of_zero {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (vanishing : (globalCoordinates degree trivialCharacter cocycle).2 = 0) :
    ∃ primitive : MaximalCochains degree trivialCharacter .line 1,
      ∀ vertices flag, cocycle.val.val vertices =
        primitive.val ![vertices 1, vertices 2] flag -
          primitive.val ![vertices 0, vertices 2] flag +
          primitive.val ![vertices 0, vertices 1] flag := by
  change classOf rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) .line)
    (restrictionCocycle degree trivialCharacter .line cocycle) = 0 at vanishing
  have membership : restrictionCocycle degree trivialCharacter .line cocycle ∈
      LinearMap.range (boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) .line)) := by
    exact (Submodule.Quotient.mk_eq_zero _).mp vanishing
  obtain ⟨primitive, equality⟩ := membership
  refine ⟨primitive, ?_⟩
  intro vertices flag
  exact (congrArg (fun cycle => cycle.val.val vertices flag) equality).symm

theorem line_primitive_bar {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (gamma : rationalLevel) (other : RationalGL3) (flag : Flags .line)
    (fixed : gamma.val⁻¹ • flag = flag) :
    cocycle.val.val ![1, gamma.val, gamma.val * other] =
      rationalCoefficientComponent degree trivialCharacter gamma.val
        (primitive.val ![1, other] flag) -
      primitive.val ![1, gamma.val * other] flag +
      primitive.val ![1, gamma.val] flag := by
  have equivariance := congrFun (primitive.property gamma ![1, other]) flag
  change primitive.val (fun index => gamma.val * ![1, other] index) flag =
    rationalCoefficientComponent degree trivialCharacter gamma.val
      (primitive.val ![1, other] (gamma.val⁻¹ • flag)) at equivariance
  have vertices_eq : (fun index : Fin 2 => gamma.val * ![1, other] index) =
      ![gamma.val, gamma.val * other] := by
    ext index
    fin_cases index <;> simp
  rw [vertices_eq, fixed] at equivariance
  have equality := primitive_eq ![1, gamma.val, gamma.val * other] flag
  change cocycle.val.val ![1, gamma.val, gamma.val * other] =
    primitive.val ![gamma.val, gamma.val * other] flag -
      primitive.val ![1, gamma.val * other] flag +
      primitive.val ![1, gamma.val] flag at equality
  rw [equivariance] at equality
  exact equality

theorem line_primitive_mixed {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (levi radical : rationalLevel) (flag : Flags .line)
    (levi_fixed : levi.val⁻¹ • flag = flag)
    (radical_fixed : radical.val⁻¹ • flag = flag) :
    mixedBarEdge cocycle levi.val radical.val =
      (rationalCoefficientComponent degree trivialCharacter levi.val
        (primitive.val ![1, levi.val⁻¹ * radical.val * levi.val] flag)).val -
      (primitive.val ![1, radical.val] flag).val +
      (primitive.val ![1, levi.val] flag).val -
      (rationalCoefficientComponent degree trivialCharacter radical.val
        (primitive.val ![1, levi.val] flag)).val := by
  have levi_eq := line_primitive_bar cocycle primitive primitive_eq levi
    (levi.val⁻¹ * radical.val * levi.val) flag levi_fixed
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at levi_eq
  have radical_eq := line_primitive_bar cocycle primitive primitive_eq radical
    levi.val flag radical_fixed
  unfold mixedBarEdge
  rw [levi_eq, radical_eq]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

theorem line_primitive_radical_cocycle {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (first second : rationalLevel) (flag : Flags .line)
    (first_fixed : first.val⁻¹ • flag = flag)
    (pure_zero : cocycle.val.val ![1, first.val, first.val * second.val] = 0) :
    primitive.val ![1, first.val * second.val] flag =
      primitive.val ![1, first.val] flag +
      rationalCoefficientComponent degree trivialCharacter first.val
        (primitive.val ![1, second.val] flag) := by
  have equality := line_primitive_bar cocycle primitive primitive_eq first
    second.val flag first_fixed
  rw [pure_zero] at equality
  apply eq_of_sub_eq_zero
  calc
    _ = -(rationalCoefficientComponent degree trivialCharacter first.val
        (primitive.val ![1, second.val] flag) -
        primitive.val ![1, first.val * second.val] flag +
        primitive.val ![1, first.val] flag) := by abel
    _ = 0 := by rw [← equality, neg_zero]

theorem iterate_pderiv_zero (iterations : ℕ) :
    ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) 0 = 0 := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    rw [Function.iterate_succ_apply', induction_hypothesis, map_zero]

theorem iterate_pderiv_add (iterations : ℕ) (left right : Poly) :
    ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) (left + right) =
      ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) left +
      ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) right := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    simp only [Function.iterate_succ_apply', induction_hypothesis, map_add]

theorem bernoulliOperator_zero (degree : ℕ) (parameter : Poly) :
    bernoulliOperator degree parameter 0 = 0 := by
  simp only [bernoulliOperator, iterate_pderiv_zero, mul_zero, Finset.sum_const_zero]

theorem bernoulliOperator_add (degree : ℕ) (parameter left right : Poly) :
    bernoulliOperator degree parameter (left + right) =
      bernoulliOperator degree parameter left + bernoulliOperator degree parameter right := by
  simp only [bernoulliOperator, iterate_pderiv_add, mul_add, Finset.sum_add_distrib]

theorem bernoulliOperator_neg (degree : ℕ) (parameter polynomial : Poly) :
    bernoulliOperator degree parameter (-polynomial) =
      -bernoulliOperator degree parameter polynomial := by
  have equality := bernoulliOperator_add degree parameter polynomial (-polynomial)
  rw [add_neg_cancel, bernoulliOperator_zero] at equality
  exact eq_neg_of_add_eq_zero_right equality.symm

theorem bernoulliOperator_sub (degree : ℕ) (parameter left right : Poly) :
    bernoulliOperator degree parameter (left - right) =
      bernoulliOperator degree parameter left - bernoulliOperator degree parameter right := by
  simp only [sub_eq_add_neg, bernoulliOperator_add, bernoulliOperator_neg]

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
