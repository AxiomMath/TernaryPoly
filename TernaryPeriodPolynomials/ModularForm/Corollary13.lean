module

public import TernaryPeriodPolynomials.BoundaryComparison.Statements

@[expose] public section


/-!
# Corollary 1.3 (`cor:complete-periods`) for fields of characteristic zero, in the paper's notation

Formalized by Claude Sonnet 5.5.

Paper: Corollary 1.3:

> For every `n ≥ 0`, restriction is an `F`-linear isomorphism `W_n(F) → 𝒫⁰_n(F)`, `f ↦ f(X,Y,0)`.  Its inverse is
> `q ↦ Φ(q)`.  It identifies `W_n^{sym}(F)` with `𝒫_n^{0,odd}(F)` and `W_n^{alt}(F)` with `𝒫_n^{0,ev}(F)`.

`corollary_1_3` below states exactly this for every field `F : Type u` of characteristic zero, with the restriction written as
`TernaryPoly.Paper.restriction` (`= bind₁ ![X 0, X 1, 0]`, i.e. `f(X,Y,0)`) and the inverse as the cyclic sum
`TernaryPoly.Paper.cyclicLift` (`Φ(q)(x,y,z) = q(x,y) + q(y,z) + q(z,x)`); it adds the two characterizations
"a solution is symmetric (alternating) iff its restriction is odd (even) in the first variable".  It is derived from
`Statements.PaperDeliverables.corollary_1_3`, which holds over every commutative `ℚ`-algebra and whose proof goes (`Proofs/RouteIndependent/RestrictionEquivNew.lean`).  The paper has no target for this corollary;
this statement is its literal Lean form.
-/

open MvPolynomial TernaryPoly.Paper

universe u

namespace TernaryPeriodPolynomials.Argument.Statements.Corollary13

/-- **Corollary 1.3.** Over a field `F` of characteristic zero and for every `n ≥ 0`: restriction to `z = 0` is an `F`-linear
isomorphism `W_n(F) ≃ 𝒫⁰_n(F)` with inverse the cyclic sum `Φ`; it restricts to isomorphisms
`W_n^{sym}(F) ≃ 𝒫_n^{0,odd}(F)` and `W_n^{alt}(F) ≃ 𝒫_n^{0,ev}(F)` (same two formulas); and a solution is symmetric
(alternating) exactly when its restriction is odd (even) in the first variable. -/
theorem corollary_1_3 (F : Type u) [Field F] [CharZero F] (n : ℕ) :
    (∃ e : solutionSpace F n ≃ₗ[F] periodSpace F n,
      (∀ f, (e f : Binary F) = restriction (f : Ternary F)) ∧
      ∀ q, ((e.symm q : solutionSpace F n) : Ternary F) = cyclicLift (q : Binary F)) ∧
    (∃ e : symmetricSolutionSpace F n ≃ₗ[F] oddPeriodSpace F n,
      (∀ f, (e f : Binary F) = restriction (f : Ternary F)) ∧
      ∀ q, ((e.symm q : symmetricSolutionSpace F n) : Ternary F) = cyclicLift (q : Binary F)) ∧
    (∃ e : alternatingSolutionSpace F n ≃ₗ[F] evenPeriodSpace F n,
      (∀ f, (e f : Binary F) = restriction (f : Ternary F)) ∧
      ∀ q, ((e.symm q : alternatingSolutionSpace F n) : Ternary F) = cyclicLift (q : Binary F)) ∧
    (∀ f ∈ solutionSpace F n, (f ∈ symmetricSolutionSpace F n ↔ restriction f ∈ oddPeriodSpace F n)) ∧
    (∀ f ∈ solutionSpace F n, (f ∈ alternatingSolutionSpace F n ↔ restriction f ∈ evenPeriodSpace F n)) := by
  obtain ⟨⟨e₁, h₁, h₁'⟩, ⟨e₂, h₂, h₂'⟩, ⟨e₃, h₃, h₃'⟩, h₄, h₅⟩ := Statements.corollary_1_3 F n
  exact ⟨⟨e₁, h₁, h₁'⟩, ⟨e₂, h₂, h₂'⟩, ⟨e₃, h₃, h₃'⟩, h₄, h₅⟩

end TernaryPeriodPolynomials.Argument.Statements.Corollary13
