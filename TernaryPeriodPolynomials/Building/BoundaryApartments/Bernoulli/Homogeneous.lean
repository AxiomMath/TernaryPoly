module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Boundary
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous MvPolynomial

theorem derivative_iterate_homogeneous {degree : ℕ} {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous degree) (iterations : ℕ) :
    (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial).IsHomogeneous
      (degree - iterations) := by
  induction iterations with
  | zero => simpa using homogeneous
  | succ iterations induction_hypothesis =>
    rw [Function.iterate_succ_apply']
    simpa only [Nat.sub_sub, Nat.add_comm] using
      (MvPolynomial.IsHomogeneous.pderiv induction_hypothesis (i := (0 : Fin 3)))

theorem derivative_homogeneous_zero {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous 0) : pderiv 0 polynomial = 0 := by
  have constant : polynomial = C (polynomial.coeff 0) := by
    calc
      polynomial = homogeneousComponent 0 polynomial :=
        (homogeneousComponent_eq_self homogeneous).symm
      _ = C (polynomial.coeff 0) := homogeneousComponent_zero polynomial
  rw [constant, pderiv_C]

theorem derivative_iterate_terminates {degree : ℕ} {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous degree) :
    ((fun value : Poly => pderiv 0 value)^[degree + 1]) polynomial = 0 := by
  rw [Function.iterate_succ_apply']
  exact derivative_homogeneous_zero (by
    simpa only [Nat.sub_self] using derivative_iterate_homogeneous homogeneous degree)

theorem derivative_iterate_zero_of_degree_lt {degree iterations : ℕ} {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous degree) (degree_lt : degree < iterations) :
    ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial = 0 := by
  obtain ⟨remaining, equality⟩ := Nat.exists_eq_add_of_le degree_lt
  rw [equality, Nat.add_comm degree.succ remaining, Function.iterate_add_apply]
  have terminated := derivative_iterate_terminates homogeneous
  rw [terminated]
  exact Function.iterate_fixed (map_zero (pderiv (0 : Fin 3))) remaining

theorem bernoulliOperator_homogeneous {degree : ℕ} {parameter polynomial : Poly}
    (parameter_homogeneous : parameter.IsHomogeneous 1)
    (polynomial_homogeneous : polynomial.IsHomogeneous degree) :
    (bernoulliOperator degree parameter polynomial).IsHomogeneous degree := by
  unfold bernoulliOperator
  apply IsHomogeneous.sum
  intro iterations iterations_range
  have iterations_le : iterations ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp iterations_range)
  have parameter_power := parameter_homogeneous.neg.pow iterations
  have differentiated := derivative_iterate_homogeneous polynomial_homogeneous iterations
  have term := (parameter_power.mul differentiated).C_mul
    ((bernoulli iterations : ℂ) / (iterations.factorial : ℂ))
  simpa only [one_mul, Nat.add_sub_of_le iterations_le, mul_assoc] using term

theorem bind_homogeneous {degree : ℕ} {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous degree) (substitution : Fin 3 → Poly)
    (substitution_homogeneous : ∀ index, (substitution index).IsHomogeneous 1) :
    (bind₁ substitution polynomial).IsHomogeneous degree := by
  simpa only [aeval_eq_bind₁, one_mul] using homogeneous.aeval substitution substitution_homogeneous

theorem bernoulliObstruction_homogeneous {degree : ℕ} (polynomial : HomogeneousPoly degree) :
    (bernoulliObstruction polynomial).IsHomogeneous (degree + 1) := by
  have variable_homogeneous (index : Fin 3) : (X index : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ index
  have first_frame : (bind₁ (![X 2 - 2 * X 1, -X 0, X 0 - X 1] : Fin 3 → Poly)
      polynomial.val).IsHomogeneous degree := by
    refine bind_homogeneous polynomial.property ![X 2 - 2 * X 1, -X 0, X 0 - X 1] ?_
    intro index
    fin_cases index
    · exact (variable_homogeneous 2).sub ((variable_homogeneous 1).C_mul 2)
    · exact (variable_homogeneous 0).neg
    · exact (variable_homogeneous 0).sub (variable_homogeneous 1)
  have second_frame : (bind₁ (![X 2 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly)
      polynomial.val).IsHomogeneous degree := by
    refine bind_homogeneous polynomial.property ![X 2 - X 0, X 0 - 2 * X 1, -X 1] ?_
    intro index
    fin_cases index
    · exact (variable_homogeneous 2).sub (variable_homogeneous 0)
    · exact (variable_homogeneous 0).sub ((variable_homogeneous 1).C_mul 2)
    · exact (variable_homogeneous 1).neg
  have third_frame : (bind₁ (![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] : Fin 3 → Poly)
      polynomial.val).IsHomogeneous degree := by
    refine bind_homogeneous polynomial.property ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] ?_
    intro index
    fin_cases index
    · exact (variable_homogeneous 2).sub ((variable_homogeneous 1).C_mul 2)
    · exact (variable_homogeneous 1).sub (variable_homogeneous 0)
    · exact (variable_homogeneous 0).sub ((variable_homogeneous 1).C_mul 2)
  have first_term := (variable_homogeneous 2).mul
    (bernoulliOperator_homogeneous (degree := degree) (parameter := X 1)
      (polynomial := bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val)
      (variable_homogeneous 1) first_frame)
  have second_term := (variable_homogeneous 1).mul
    (bernoulliOperator_homogeneous (variable_homogeneous 2) ((first_frame.sub second_frame).add third_frame))
  simpa only [bernoulliObstruction, Nat.add_comm] using first_term.sub second_term

theorem bernoulliObstruction_zero_second {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    bind₁ (![X 0, 0, X 2] : Fin 3 → Poly) (bernoulliObstruction polynomial) = 0 := by
  apply IsHomogeneous.eq_zero_of_forall_eval_eq_zero
    (bind_homogeneous (bernoulliObstruction_homogeneous polynomial) ![X 0, 0, X 2] (by
      intro index
      fin_cases index
      · exact isHomogeneous_X ℂ 0
      · exact isHomogeneous_zero (Fin 3) ℂ 1
      · exact isHomogeneous_X ℂ 2))
  intro coordinates
  have coordinates_eta : coordinates = ![coordinates 0, coordinates 1, coordinates 2] := by
    funext index
    fin_cases index <;> rfl
  conv_lhs => rw [coordinates_eta]
  change polynomialValue (bind₁ ![X 0, 0, X 2] (bernoulliObstruction polynomial))
    (coordinates 0) (coordinates 1) (coordinates 2) = 0
  rw [polynomialValue_bind]
  have coordinate_eq : (fun index => polynomialValue (![X 0, 0, X 2] index)
      (coordinates 0) (coordinates 1) (coordinates 2)) = ![coordinates 0, 0, coordinates 2] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinate_eq]
  exact bernoulliObstruction_goodBoundary solution _ _

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
