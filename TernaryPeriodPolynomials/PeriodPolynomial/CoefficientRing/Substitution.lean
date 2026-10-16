module

public import TernaryPeriodPolynomials.Polynomial.Restriction
public import TernaryPeriodPolynomials.Polynomial.Definitions
public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-!
# Substitution helpers for the Section 6-7 displayed claims

Formalized by Claude Haiku 5.5.
Composition of `bind₁` substitutions, the alternation transport, the two period
relations at linear substitutions, the involution `S : q ↦ q(-X,Y)`, and the order-three
substitution `T : q ↦ q(-Y,X-Y)`. Paper: Section 6 (`lem:alternating-classification`) and the proof of Corollary 1.3.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Section67Claims

variable {F : Type*} [CommRing F]

/-- Composition of two substitutions by vectors: `u` applied after `v` is `w`
when `u (v i) = w i` for every `i`. -/
theorem bind_bind_vec {σ τ υ : Type*} (u : τ → MvPolynomial υ F) (v : σ → MvPolynomial τ F)
    (w : σ → MvPolynomial υ F) (h : ∀ i, bind₁ u (v i) = w i) (f : MvPolynomial σ F) :
    bind₁ u (bind₁ v f) = bind₁ w f := by
  have hfun : (fun i => bind₁ u (v i)) = w := funext h
  rw [bind₁_bind₁, hfun]

/-- Alternation of a binary polynomial, `q(X,Y) = -q(Y,X)`, transported to any substitution:
`q(b,a) = -q(a,b)`. -/
theorem alt_subst (q : MvPolynomial (Fin 2) F) (hq : bind₁ ![X 1, X 0] q = -q)
    {σ : Type*} (a b : MvPolynomial σ F) :
    bind₁ ![b, a] q = -bind₁ ![a, b] q := by
  have h1 : bind₁ ![a, b] (bind₁ ![X 1, X 0] q) = bind₁ ![b, a] q :=
    bind_bind_vec _ _ _ (fun i => by fin_cases i <;> simp) q
  rw [← h1, hq, map_neg]

/-- Substituting `(U,V)` into the involution image `q(-X,Y)`: `q(-U,V)`. -/
theorem bind_involution (q : MvPolynomial (Fin 2) F) (U V : MvPolynomial (Fin 2) F) :
    bind₁ ![U, V] (bind₁ ![-X 0, X 1] q) = bind₁ ![-U, V] q :=
  bind_bind_vec _ _ _ (fun i => by fin_cases i <;> simp) q

/-- The two-term relation at the substitution `(U,V)`:
`q(U,V) + q(-V,U) = 0`. -/
theorem two_term_inst (q : MvPolynomial (Fin 2) F) (hR2 : q + bind₁ ![-X 1, X 0] q = 0)
    (U V : MvPolynomial (Fin 2) F) :
    bind₁ ![U, V] q + bind₁ ![-V, U] q = 0 := by
  have h := congrArg (bind₁ ![U, V]) hR2
  have h2 : bind₁ ![U, V] (bind₁ ![-X 1, X 0] q) = bind₁ ![-V, U] q :=
    bind_bind_vec _ _ _ (fun i => by fin_cases i <;> simp) q
  rw [map_add, map_zero, h2] at h
  exact h

/-- The three-term relation at the substitution `(U,V)`:
`q(U,V) + q(-V,U-V) + q(V-U,-U) = 0`. -/
theorem three_term_inst (q : MvPolynomial (Fin 2) F)
    (hR3 : q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0)
    (U V : MvPolynomial (Fin 2) F) :
    bind₁ ![U, V] q + bind₁ ![-V, U - V] q + bind₁ ![V - U, -U] q = 0 := by
  have h := congrArg (bind₁ ![U, V]) hR3
  have h2 : bind₁ ![U, V] (bind₁ ![-X 1, X 0 - X 1] q) = bind₁ ![-V, U - V] q :=
    bind_bind_vec _ _ _ (fun i => by fin_cases i <;> simp) q
  have h3 : bind₁ ![U, V] (bind₁ ![X 1 - X 0, -X 0] q) = bind₁ ![V - U, -U] q :=
    bind_bind_vec _ _ _ (fun i => by fin_cases i <;> simp) q
  rw [map_add, map_add, map_zero, h2, h3] at h
  exact h

/-- The identity substitution fixes binary polynomials. -/
theorem bind_id_pair (q : MvPolynomial (Fin 2) F) : bind₁ ![X 0, X 1] q = q := by
  rw [show (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) F) = X from by
    funext i; fin_cases i <;> rfl]
  rw [bind₁_X_left]
  rfl

/-- Evenness of a binary period relation: `q(-X,-Y) = q(X,Y)`. -/
theorem even_of_two_term (q : MvPolynomial (Fin 2) F) (hR2 : q + bind₁ ![-X 1, X 0] q = 0) :
    bind₁ ![-X 0, -X 1] q = q := by
  have a := two_term_inst q hR2 (X 0) (X 1)
  have b := two_term_inst q hR2 (-X 1) (X 0)
  rw [bind_id_pair] at a
  linear_combination b - a

/-- The order-three substitution `T(X,Y) = (-Y, X-Y)` satisfies `T^3 = id`
on binary polynomials. -/
theorem bind_T_cube (q : MvPolynomial (Fin 2) F) :
    bind₁ ![-X 1, X 0 - X 1] (bind₁ ![-X 1, X 0 - X 1] (bind₁ ![-X 1, X 0 - X 1] q)) = q := by
  rw [bind_bind_vec (![-X 1, X 0 - X 1]) (![-X 1, X 0 - X 1]) (![X 1 - X 0, -X 0])
    (fun i => by fin_cases i <;> (simp; try ring))]
  rw [bind_bind_vec (![X 1 - X 0, -X 0]) (![-X 1, X 0 - X 1]) (![X 0, X 1])
    (fun i => by fin_cases i <;> simp)]
  exact bind_id_pair q

/-- The numeral `4` of a binary polynomial is fixed by every substitution.
-/
theorem bind_ofNat_four {τ : Type*} (u : Fin 2 → MvPolynomial τ F) :
    bind₁ u (4 : MvPolynomial (Fin 2) F) = 4 :=
  map_ofNat _ 4

end TernaryPeriodPolynomials.Argument.Section67Claims
