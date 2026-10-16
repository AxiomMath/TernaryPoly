module

public import TernaryPeriodPolynomials.Polynomial.Definitions

@[expose] public section


/-! # Polynomial substitution and normalized binary periods

These identities use the literal full period relations, over arbitrary commutative
rings. Characteristic hypotheses are introduced only where cancellation needs them.
-/


open MvPolynomial

noncomputable section
namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-- Evaluate a binary polynomial at two polynomial arguments. -/
def binaryEval {σ : Type*} (q : Binary R) (a b : MvPolynomial σ R) :
    MvPolynomial σ R := bind₁ ![a, b] q

@[simp] theorem binaryEval_add {σ : Type*} (q r : Binary R)
    (a b : MvPolynomial σ R) : binaryEval (q + r) a b = binaryEval q a b + binaryEval r a b :=
  map_add _ _ _

@[simp] theorem binaryEval_neg {σ : Type*} (q : Binary R)
    (a b : MvPolynomial σ R) : binaryEval (-q) a b = -binaryEval q a b := map_neg _ _

@[simp] theorem binaryEval_zero {σ : Type*} (a b : MvPolynomial σ R) :
    binaryEval (0 : Binary R) a b = 0 := map_zero _

@[simp] theorem binaryEval_X (q : Binary R) : binaryEval q (X 0) (X 1) = q := by
  change bind₁ _ q = q
  have hv : (![X 0, X 1] : Fin 2 → Binary R) = X := by
    funext i
    fin_cases i <;> rfl
  rw [hv, bind₁_X_left, AlgHom.id_apply]

/-- Coordinate-vector form of composition, useful for reducing concrete substitutions. -/
theorem bind_vec2 {σ : Type*} (u v : Binary R) (a b : MvPolynomial σ R) :
    (fun i => bind₁ ![a,b] (![u,v] i)) = ![bind₁ ![a,b] u, bind₁ ![a,b] v] := by
  funext i
  fin_cases i <;> rfl

/-- Substituting after binary evaluation substitutes just its two arguments. -/
theorem bind_binaryEval {σ τ : Type*} (g : σ → MvPolynomial τ R)
    (q : Binary R) (a b : MvPolynomial σ R) :
    bind₁ g (binaryEval q a b) = binaryEval q (bind₁ g a) (bind₁ g b) := by
  simp only [binaryEval, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- A binary substitution followed by evaluation is ordinary composition. -/
theorem binaryEval_bind {σ : Type*} (q : Binary R) (u v : Binary R)
    (a b : MvPolynomial σ R) :
    binaryEval (bind₁ ![u, v] q) a b =
      binaryEval q (binaryEval u a b) (binaryEval v a b) :=
  bind_binaryEval _ q u v

/-- The first axis condition holds with every polynomial on the other axis. -/
theorem PeriodRelations.eval_zero_first {σ : Type*} {q : Binary R}
    (hq : PeriodRelations q) (b : MvPolynomial σ R) : binaryEval q 0 b = 0 := by
  have h := congrArg (fun p : Binary R => binaryEval p (0 : MvPolynomial σ R) b) hq.axis_first
  simpa [binaryEval, bind₁_bind₁, bind_vec2] using h

/-- The second axis condition holds after arbitrary substitution. -/
theorem PeriodRelations.eval_zero_second {σ : Type*} {q : Binary R}
    (hq : PeriodRelations q) (a : MvPolynomial σ R) : binaryEval q a 0 = 0 := by
  have h := congrArg (fun p : Binary R => binaryEval p a (0 : MvPolynomial σ R)) hq.axis_second
  simpa [binaryEval, bind₁_bind₁, bind_vec2] using h

/-- The two-term relation can be used at arbitrary polynomial arguments. -/
theorem PeriodIdentities.eval_two_term {σ : Type*} {q : Binary R}
    (hq : PeriodIdentities q) (a b : MvPolynomial σ R) :
    binaryEval q a b + binaryEval q (-b) a = 0 := by
  have h := congrArg (fun p => binaryEval p a b) hq.1
  simpa [binaryEval, bind₁_bind₁, bind_vec2] using h

/-- The order-three relation can be used at arbitrary polynomial arguments. -/
theorem PeriodIdentities.eval_three_term {σ : Type*} {q : Binary R}
    (hq : PeriodIdentities q) (a b : MvPolynomial σ R) :
    binaryEval q a b + binaryEval q (-b) (a-b) + binaryEval q (b-a) (-a) = 0 := by
  have h := congrArg (fun p => binaryEval p a b) hq.2
  simpa [binaryEval, bind₁_bind₁, bind_vec2] using h

/-- Normalized periods in particular satisfy both period identities. -/
theorem PeriodRelations.identities {q : Binary R} (hq : PeriodRelations q) :
    PeriodIdentities q := hq.2.2

/-- The two-term relation forces simultaneous evenness, with no division by two. -/
theorem PeriodIdentities.eval_neg_neg {σ : Type*} {q : Binary R}
    (hq : PeriodIdentities q) (a b : MvPolynomial σ R) :
    binaryEval q (-a) (-b) = binaryEval q a b := by
  have h₁ := hq.eval_two_term a b
  have h₂ := hq.eval_two_term (-b) a
  linear_combination h₂ - h₁

/-- Simultaneous evenness as a formal binary polynomial identity. -/
theorem PeriodIdentities.neg_neg {q : Binary R} (hq : PeriodIdentities q) :
    bind₁ ![-X 0, -X 1] q = q := by
  have h := hq.eval_neg_neg (X 0 : Binary R) (X 1)
  rw [binaryEval_X] at h
  exact h

end TernaryPoly.Paper
