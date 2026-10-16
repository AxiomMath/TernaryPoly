/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Source: Vasily Ilin and Ken Ono, Ternary polynomial relations and periods of cusp forms,
paper, Theorems 1.1 and 1.2.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly.Paper

abbrev Ternary (R : Type*) [CommSemiring R] := MvPolynomial (Fin 3) R
abbrev Binary (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R

variable {R : Type*} [CommRing R]

/-- Evaluate a binary polynomial at two polynomial arguments. -/
def binaryEval {σ : Type*} (q : Binary R) (a b : MvPolynomial σ R) :
    MvPolynomial σ R := bind₁ ![a, b] q

/-- The cyclic sum Φ(q) = q(x,y) + q(y,z) + q(z,x). -/
def cyclicLift (q : Binary R) : Ternary R :=
  binaryEval q (X 0) (X 1) + binaryEval q (X 1) (X 2) + binaryEval q (X 2) (X 0)

end TernaryPoly.Paper

namespace TernaryPeriodPolynomials

theorem bachmann_van_ittersum {F : Type*} [Field F] [CharZero F] (f : MvPolynomial (Fin 3) F)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    (∃ p q r : MvPolynomial (Fin 2) F,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![2, 0] : Fin 2 → Fin 3) r) ∧
    pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 ∧
    (∀ n, f.IsHomogeneous n → Odd n → f = 0) := by
  sorry

theorem symmetric_solution_iff_eq_cyclicLift {F : Type*} [Field F] [CharZero F]
    {f : MvPolynomial (Fin 3) F} {n : ℕ}
    (hf : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) ↔
    ∃! q : MvPolynomial (Fin 2) F, q.IsHomogeneous n ∧
      (bind₁ ![X 1, X 0] q = q ∧ bind₁ ![-X 0, X 1] q = -q ∧
        bind₁ ![X 0, -X 1] q = -q ∧
        q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) ∧
      f = TernaryPoly.Paper.cyclicLift q := by
  sorry

end TernaryPeriodPolynomials
