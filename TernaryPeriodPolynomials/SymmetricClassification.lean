module

public import TernaryPeriodPolynomials.Polynomial.Classification.Restriction
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section


/-!
# Theorem 1.2: symmetric solutions are cyclic sums of binary period polynomials

For a symmetric homogeneous `f ∈ F[x, y, z]` of degree `n` over a field of characteristic zero,
`f` satisfies the three-term relation iff `f = Φ(q) = q(x, y) + q(y, z) + q(z, x)` for a unique
homogeneous `q ∈ F[X, Y]` of degree `n` that is symmetric, odd in each variable and satisfies
`q(X, Y) + q(-Y, X - Y) + q(Y - X, -X) = 0` (`TernaryPeriodPolynomials.symmetric_solution_iff_eq_cyclicLift`).
The binary polynomial is the restriction `q(X, Y) = f(X, Y, 0)`.
-/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.Classification

/-- A symmetric homogeneous `f` of degree `n` over a field of characteristic zero satisfies the
three-term relation iff `f = Φ(q)` for a unique homogeneous binary `q` of degree `n` satisfying the
odd period relations `TernaryPoly.BinaryComplexPeriod.Relations`. -/
theorem symmetric_classification {F : Type*} [Field F] [CharZero F]
    {f : Ternary F} {n : ℕ} (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1,X 0-X 1,X 2] f + bind₁ ![X 1-X 0,-X 0,X 2] f = 0) ↔
      ∃! q : Binary F, q.IsHomogeneous n ∧ TernaryPoly.BinaryComplexPeriod.Relations F q ∧
        f = cyclicLift q := by
  constructor
  · intro hn
    have hf : Solution f := ⟨IsSymmetric.cyclic hs, hn⟩
    refine ⟨restriction f, ⟨restriction_homogeneous hh,
      (odd_relations_iff _).mp ⟨restriction_periodRelations hf,
        (restriction_symmetric_iff hf).mp (IsSymmetric.swap hs)⟩,
      (cyclicLift_restriction hf).symm⟩, ?_⟩
    intro q hq
    have hrel := ((odd_relations_iff q).mpr hq.2.1).1
    rw [hq.2.2, restriction_cyclicLift hrel]
  · rintro ⟨q, ⟨_, hq, rfl⟩, _⟩
    exact cyclicLift_norm ((odd_relations_iff q).mpr hq).1

/-- `symmetric_classification` with the binary period relations written out: `q` is symmetric,
odd in each variable and satisfies the binary three-term relation. -/
theorem symmetric_classification_literal {F : Type*} [Field F] [CharZero F]
    {f : Ternary F} {n : ℕ} (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1,X 0-X 1,X 2] f + bind₁ ![X 1-X 0,-X 0,X 2] f = 0) ↔
      ∃! q : Binary F, q.IsHomogeneous n ∧
        (bind₁ ![X 1,X 0] q = q ∧ bind₁ ![-X 0,X 1] q = -q ∧
          bind₁ ![X 0,-X 1] q = -q ∧
          q + bind₁ ![-X 1,X 0-X 1] q + bind₁ ![X 1-X 0,-X 0] q = 0) ∧
        f = cyclicLift q := by
  simpa only [symmetric_binary_relations_literal] using symmetric_classification hh hs

end TernaryPeriodPolynomials.Argument.Classification

namespace TernaryPeriodPolynomials

/-- **Theorem 1.2.** Let `F` be a field of characteristic zero and `f ∈ F[x, y, z]` symmetric and
homogeneous of degree `n`. Then `f(x, y, z) + f(-y, x - y, z) + f(y - x, -x, z) = 0` if and only if
`f = Φ(q)` for a unique homogeneous `q ∈ F[X, Y]` of degree `n` with `q(Y, X) = q(X, Y)`,
`q(-X, Y) = -q(X, Y)`, `q(X, -Y) = -q(X, Y)` and `q(X, Y) + q(-Y, X - Y) + q(Y - X, -X) = 0`.
(For odd `n` both sides force `f = 0`.) -/
theorem symmetric_solution_iff_eq_cyclicLift {F : Type*} [Field F] [CharZero F]
    {f : MvPolynomial (Fin 3) F} {n : ℕ}
    (hf : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) ↔
    ∃! q : MvPolynomial (Fin 2) F, q.IsHomogeneous n ∧
      (bind₁ ![X 1, X 0] q = q ∧ bind₁ ![-X 0, X 1] q = -q ∧
        bind₁ ![X 0, -X 1] q = -q ∧
        q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) ∧
      f = TernaryPoly.Paper.cyclicLift q :=
  Argument.Classification.symmetric_classification_literal hf hs

end TernaryPeriodPolynomials
