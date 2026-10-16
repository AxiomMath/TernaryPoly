module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.SymBoundaryFactors
public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Polynomial

@[expose] public section


/-!
# First-order data of the Bernoulli obstruction on `w = 0`: `J_v(X, 0, Z) = Z · v(Z, -X, X)` (MR-6)

Formalized by Claude Sonnet 5.5.  Proof of Lemma `lem:period-extraction`,:
"First, `J_v(X,0,Z) = Z v(Z,-X,X)`. Thus `J_v = 0` implies vanishing on each opposite-pair plane, and hence `c₊ ∣ v`."

`J` is the paper's `bernoulliObstruction` (`GeneralEisenstein.bernoulliObstruction`, equation `eq:Jdef`).  NO norm hypothesis and in fact no symmetry hypothesis is needed for the identity (`J_opposite_line`,
`J_bind_second_zero`): at `Y = 0` the Bernoulli operator `B(0·∂_X)` is the identity and the second term carries the factor `Y`.  Symmetry (invariance under the permutations of the three variables) is used
only for the consequence `cPlus ∣ v` (`cPlus_dvd_of_J_zero`), exactly as in the paper.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
open TernaryPeriodPolynomials.Argument.FiberModel.SymBoundaryFactors

/-- **`J_v(X, 0, Z) = Z · v(Z, -X, X)`** for every homogeneous `v` (no norm hypothesis, no symmetry hypothesis). -/
theorem J_opposite_line {n : ℕ} (f : HomogeneousPoly n) (first third : ℂ) :
    polynomialValue (bernoulliObstruction f) first 0 third = third * eval ![third, -first, first] f.val := by
  have parameter_zero : eval ![first, (0 : ℂ), third] (X (1 : Fin 3)) = 0 := by simp
  have evaluated := bernoulliOperator_eval_parameter_zero n (X 1)
    (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val)
    ![first, 0, third] parameter_zero
  unfold polynomialValue bernoulliObstruction
  simp only [map_sub, map_mul, eval_X, Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail, zero_mul, sub_zero]
  rw [evaluated]
  change third * polynomialValue (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val) first 0 third =
    third * eval ![third, -first, first] f.val
  rw [polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      (![X 2 - 2 * X 1, -X 0, X 0 - X 1] index) first 0 third) = ![third, -first, first] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]

/-- The same identity as an identity of polynomials: `J_v(X, 0, Z) = Z · v(Z, -X, X)`. -/
theorem J_bind_second_zero {n : ℕ} (f : HomogeneousPoly n) :
    bind₁ (![X 0, 0, X 2] : Fin 3 → Poly) (bernoulliObstruction f) = (X 2 : Poly) * bind₁ (![X 2, -X 0, X 0] : Fin 3 → Poly) f.val := by
  let substitution : Fin 3 → Poly := ![X 0, 0, X 2]
  have second_variable_zero : bind₁ substitution (X 1) = 0 := by
    simp [substitution]
  have first_frame :
      bind₁ substitution (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val) =
        bind₁ (![X 2, -X 0, X 0] : Fin 3 → Poly) f.val := by
    rw [bind₁_bind₁]
    congr 1
    ext index
    fin_cases index <;> simp [substitution]
  change bind₁ substitution (bernoulliObstruction f) = _
  simp only [bernoulliObstruction, map_sub, map_mul, second_variable_zero, zero_mul, sub_zero]
  rw [TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers.bernoulliOperator_bind_zero n substitution (X 1) _ second_variable_zero, first_frame]
  simp [substitution]

/-- **`J_v = 0` forces vanishing on the opposite-pair plane `y + z = 0`**: `v(Z, -X, X) = 0`. -/
theorem opposite_plane_of_J_zero {n : ℕ} (f : HomogeneousPoly n) (h : bernoulliObstruction f = 0) :
    bind₁ (![X 2, -X 0, X 0] : Fin 3 → Poly) f.val = 0 := by
  have h1 := J_bind_second_zero f
  rw [h, map_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left (X_ne_zero (2 : Fin 3))

theorem eval_opposite_of_J_zero {n : ℕ} (f : HomogeneousPoly n) (h : bernoulliObstruction f = 0) (a c : ℂ) :
    eval ![c, -a, a] f.val = 0 := by
  have h1 := opposite_plane_of_J_zero f h
  have h2 : polynomialValue (bind₁ (![X 2, -X 0, X 0] : Fin 3 → Poly) f.val) a 0 c = 0 := by
    rw [h1]; simp [polynomialValue]
  rw [polynomialValue_bind] at h2
  have coordinates : (fun index => polynomialValue (![X 2, -X 0, X 0] index) a 0 c) = ![c, -a, a] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rwa [coordinates] at h2


theorem poly_eq_zero_of_polynomialValue (P : Poly) (h : ∀ a b c, polynomialValue P a b c = 0) : P = 0 := by
  apply MvPolynomial.funext
  intro values
  have eta : values = ![values 0, values 1, values 2] := by
    funext index; fin_cases index <;> rfl
  rw [map_zero, eta]
  exact h _ _ _

private theorem update_X_zero' (p : Poly) : Function.update (X : Fin 3 → Poly) (0 : Fin 3) p = ![p, X 1, X 2] := by
  funext i
  fin_cases i <;> simp

private theorem update_X_one' (p : Poly) : Function.update (X : Fin 3 → Poly) (1 : Fin 3) p = ![X 0, p, X 2] := by
  funext i
  fin_cases i <;> simp

/-- Invariance under a permutation of the arguments, as an identity of values. -/
theorem eval_perm_of_symmetric {n : ℕ} (f : HomogeneousPoly n)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) f.val = f.val) (p : Equiv.Perm (Fin 3))
    (a b c : ℂ) : eval (fun i => (![a, b, c] : Fin 3 → ℂ) (p i)) f.val = eval ![a, b, c] f.val := by
  have h := congrArg (fun P => polynomialValue P a b c) (hs p)
  simp only [polynomialValue_bind] at h
  have e : (fun i => (![a, b, c] : Fin 3 → ℂ) (p i)) = fun index => polynomialValue (X (p index)) a b c := by
    funext i; simp [polynomialValue]
  rw [e]
  exact h

/-- **`J_v = 0` for symmetric `v` forces `c₊ ∣ v`** ("`J_v = 0` implies vanishing on each opposite-pair plane, and hence `c₊ ∣ v`"). -/
theorem cPlus_dvd_of_J_zero {n : ℕ} (f : HomogeneousPoly n)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) f.val = f.val)
    (h : bernoulliObstruction f = 0) : cPlus ℂ ∣ f.val := by
  have hop := eval_opposite_of_J_zero f h
  have h01 : bind₁ (Function.update (X : Fin 3 → Poly) (0 : Fin 3) (-X 1)) f.val = 0 := by
    rw [update_X_zero']
    apply poly_eq_zero_of_polynomialValue
    intro a b c
    rw [polynomialValue_bind]
    have coordinates : (fun index => polynomialValue
        (![-X 1, X 1, X 2] index : Poly) a b c) = ![-b, b, c] := by
      funext index; fin_cases index <;> simp [polynomialValue]
    rw [coordinates]
    have := eval_perm_of_symmetric f hs (finRotate 3).symm (-b) b c
    have e : (fun i => (![-b, b, c] : Fin 3 → ℂ) ((finRotate 3).symm i)) = ![c, -b, b] := by
      funext i; fin_cases i <;> simp
    rw [e] at this
    rw [← this]
    exact hop b c
  have h02 : bind₁ (Function.update (X : Fin 3 → Poly) (0 : Fin 3) (-X 2)) f.val = 0 := by
    rw [update_X_zero']
    apply poly_eq_zero_of_polynomialValue
    intro a b c
    rw [polynomialValue_bind]
    have coordinates : (fun index => polynomialValue
        (![-X 2, X 1, X 2] index : Poly) a b c) = ![-c, b, c] := by
      funext index; fin_cases index <;> simp [polynomialValue]
    rw [coordinates]
    have := eval_perm_of_symmetric f hs (Equiv.swap 0 1) (-c) b c
    have e : (fun i => (![-c, b, c] : Fin 3 → ℂ) (Equiv.swap 0 1 i)) = ![b, -c, c] := by
      funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [e] at this
    rw [← this]
    exact hop c b
  have h12 : bind₁ (Function.update (X : Fin 3 → Poly) (1 : Fin 3) (-X 2)) f.val = 0 := by
    rw [update_X_one']
    apply poly_eq_zero_of_polynomialValue
    intro a b c
    rw [polynomialValue_bind]
    have coordinates : (fun index => polynomialValue
        (![X 0, -X 2, X 2] index : Poly) a b c) = ![a, -c, c] := by
      funext index; fin_cases index <;> simp [polynomialValue]
    rw [coordinates]
    exact hop c a
  have hd01 : X 0 + X 1 ∣ f.val := by
    simpa only [sub_neg_eq_add] using TernaryPoly.linear_factor_dvd_of_substitution_zero f.val 0 (-X 1) h01
  have hkeep02 : bind₁ (Function.update (X : Fin 3 → Poly) (0 : Fin 3) (-X 2)) (X 0 + X 1 : Poly) ≠ 0 := by
    intro h
    have h' := congrArg (eval (![0, 1, 0] : Fin 3 → ℂ)) h
    norm_num [update_X_zero', Matrix.cons_val_two] at h'
  have hd02 : (X 0 + X 1) * (X 0 + X 2) ∣ f.val := by
    simpa only [sub_neg_eq_add] using
      TernaryPoly.mul_linear_factor_dvd_of_substitution_zero f.val (X 0 + X 1) 0 (-X 2) hd01 h02 hkeep02
  have hkeep12 : bind₁ (Function.update (X : Fin 3 → Poly) (1 : Fin 3) (-X 2))
      ((X 0 + X 1) * (X 0 + X 2) : Poly) ≠ 0 := by
    intro h
    have h' := congrArg (eval (![1, 0, 0] : Fin 3 → ℂ)) h
    norm_num [update_X_one', Matrix.cons_val_two] at h'
  simpa only [sub_neg_eq_add] using
    TernaryPoly.mul_linear_factor_dvd_of_substitution_zero f.val ((X 0 + X 1) * (X 0 + X 2))
      1 (-X 2) hd02 h12 hkeep12

end TernaryPeriodPolynomials.Argument.Identities
