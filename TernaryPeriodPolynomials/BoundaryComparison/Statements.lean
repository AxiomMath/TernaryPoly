module

public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.SymmetricSolution.Factors

@[expose] public section



/-!
# Route-independent exports of paper results without a target

Formalized by Claude Sonnet 5.5.

Literal-statement theorems for results of the paper
that have no target: Corollary 1.3 (`cor:complete-periods`), Lemma 7.1
(`lem:alternating-classification`), Proposition 6.1 (`prop:coefficient-base-change`), Lemma 2.2
(`lem:sym-boundary-factors`) and the last sentence of Theorem 1.2
(`thm:symmetric-classification`, `q(X,Y) = f(X,Y,0)`). All are proved
(`Proofs/NewRoute/RestrictionNew.lean`, `Proofs/RouteIndependent/RestrictionEquivNew.lean`,
the base-change module `TernaryPoly.Paper.CoefficientBaseChange`, and the original library's
divisibility lemmas, which do not use the original support route).

Notation as in the paper: `Φ(q) = q(x,y) + q(y,z) + q(z,x)` is `cyclicLift q`, restriction
is `f ↦ f(X,Y,0)`, `W_n(R) = solutionSpace R n`, `𝒫⁰_n(R) = periodSpace R n`,
`𝒫^{0,odd}_n(R) = oddPeriodSpace R n`, `𝒫^{0,ev}_n(R) = evenPeriodSpace R n`.
-/

open MvPolynomial TensorProduct TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification
open TernaryPeriodPolynomials.Argument.RouteIndependent

namespace TernaryPeriodPolynomials.Argument.Statements

/-- **Corollary 1.3** (`cor:complete-periods`, `eq:period-restriction`). For every `n ≥ 0`, over
every commutative `ℚ`-algebra `R` (in particular every field of characteristic zero),
restriction `f ↦ f(X,Y,0)` is an `R`-linear isomorphism `W_n(R) → 𝒫⁰_n(R)` whose inverse is the
cyclic sum `q ↦ Φ(q)`; the same formulas give isomorphisms `W_n^{sym}(R) ≅ 𝒫^{0,odd}_n(R)` and
`W_n^{alt}(R) ≅ 𝒫^{0,ev}_n(R)`, and a solution is symmetric (alternating) if and only if its
restriction is odd (even) in the first variable. -/
theorem corollary_1_3 (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    (∃ e : solutionSpace R n ≃ₗ[R] periodSpace R n,
      (∀ f, (e f : Binary R) = bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) (f : Ternary R)) ∧
      ∀ q, ((e.symm q : solutionSpace R n) : Ternary R) =
        bind₁ (![X 0, X 1] : Fin 2 → Ternary R) (q : Binary R) +
          bind₁ (![X 1, X 2] : Fin 2 → Ternary R) (q : Binary R) +
            bind₁ (![X 2, X 0] : Fin 2 → Ternary R) (q : Binary R)) ∧
    (∃ e : symmetricSolutionSpace R n ≃ₗ[R] oddPeriodSpace R n,
      (∀ f, (e f : Binary R) = bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) (f : Ternary R)) ∧
      ∀ q, ((e.symm q : symmetricSolutionSpace R n) : Ternary R) =
        bind₁ (![X 0, X 1] : Fin 2 → Ternary R) (q : Binary R) +
          bind₁ (![X 1, X 2] : Fin 2 → Ternary R) (q : Binary R) +
            bind₁ (![X 2, X 0] : Fin 2 → Ternary R) (q : Binary R)) ∧
    (∃ e : alternatingSolutionSpace R n ≃ₗ[R] evenPeriodSpace R n,
      (∀ f, (e f : Binary R) = bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) (f : Ternary R)) ∧
      ∀ q, ((e.symm q : alternatingSolutionSpace R n) : Ternary R) =
        bind₁ (![X 0, X 1] : Fin 2 → Ternary R) (q : Binary R) +
          bind₁ (![X 1, X 2] : Fin 2 → Ternary R) (q : Binary R) +
            bind₁ (![X 2, X 0] : Fin 2 → Ternary R) (q : Binary R)) ∧
    (∀ f ∈ solutionSpace R n,
      (f ∈ symmetricSolutionSpace R n ↔
        bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f ∈ oddPeriodSpace R n)) ∧
    (∀ f ∈ solutionSpace R n,
      (f ∈ alternatingSolutionSpace R n ↔
        bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f ∈ evenPeriodSpace R n)) := by
  refine ⟨⟨TernaryPeriodPolynomials.Argument.RouteIndependent.restrictionEquiv R n, fun _ => rfl, fun _ => rfl⟩,
    ⟨TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv R n, fun _ => rfl, fun _ => rfl⟩,
    ⟨TernaryPeriodPolynomials.Argument.RouteIndependent.alternatingRestrictionEquiv R n, fun _ => rfl, fun _ => rfl⟩, ?_, ?_⟩
  · intro f hf
    have hsol := ((mem_solutionSpace n f).mp hf).2
    refine ⟨fun h => (TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv R n ⟨f, h⟩).property, fun h => ?_⟩
    have e : (((TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv R n).symm
        ⟨bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f, h⟩ : symmetricSolutionSpace R n) :
          Ternary R) = f :=
      TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hsol
    exact (congrArg (· ∈ symmetricSolutionSpace R n) e).mp
      ((TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv R n).symm
        ⟨bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f, h⟩).property
  · intro f hf
    have hsol := ((mem_solutionSpace n f).mp hf).2
    refine ⟨fun h => (TernaryPeriodPolynomials.Argument.RouteIndependent.alternatingRestrictionEquiv R n ⟨f, h⟩).property, fun h => ?_⟩
    have e : (((TernaryPeriodPolynomials.Argument.RouteIndependent.alternatingRestrictionEquiv R n).symm
        ⟨bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f, h⟩ : alternatingSolutionSpace R n) :
          Ternary R) = f :=
      TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hsol
    exact (congrArg (· ∈ alternatingSolutionSpace R n) e).mp
      ((TernaryPeriodPolynomials.Argument.RouteIndependent.alternatingRestrictionEquiv R n).symm
        ⟨bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f, h⟩).property

/-- The literal list of properties in Lemma 7.1 gives the full normalized period relations. -/
private theorem periodRelations_of_alternating_literal {F : Type*} [Field F] {q : Binary F}
    (h1 : bind₁ (![X 1, X 0] : Fin 2 → Binary F) q = -q)
    (h2 : bind₁ (![-X 0, X 1] : Fin 2 → Binary F) q = q)
    (h4 : bind₁ (![0, X 1] : Fin 2 → Binary F) q = 0)
    (h5 : bind₁ (![X 0, 0] : Fin 2 → Binary F) q = 0)
    (h6 : q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) :
    PeriodRelations q := by
  refine ⟨h4, h5, ?_, h6⟩
  have h := binaryEval_even_first h2 (X 1 : Binary F) (X 0)
  change q + binaryEval q (-X 1) (X 0) = 0
  rw [h]
  change q + bind₁ (![X 1, X 0] : Fin 2 → Binary F) q = 0
  rw [h1]
  exact add_neg_cancel q

/-- **Lemma 7.1** (`lem:alternating-classification`). Let `F` be a field of characteristic zero.
An alternating `f ∈ F[x,y,z]_n` (`f(y,x,z) = -f(x,y,z)`) is a solution (cyclic and
`f + f∘A + f∘A² = 0`) if and only if `f = Φ(q)` for a unique `q ∈ F[X,Y]_n` that is alternating,
even in each variable, zero on both axes and satisfies the binary three-term relation
`q(X,Y) + q(-Y,X-Y) + q(Y-X,-X) = 0`; in that case `q(X,Y) = f(X,Y,0)`. (The paper assumes
`n > 0` even; the statement is proved for every `n`, the odd case being vacuous on both sides.) -/
theorem lemma_7_1 {F : Type*} [Field F] [CharZero F] {n : ℕ} {f : Ternary F}
    (hf : f.IsHomogeneous n) (ha : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f = -f) :
    (Solution f ↔
      ∃! q : Binary F, q.IsHomogeneous n ∧
        (bind₁ (![X 1, X 0] : Fin 2 → Binary F) q = -q ∧
          bind₁ (![-X 0, X 1] : Fin 2 → Binary F) q = q ∧
          bind₁ (![X 0, -X 1] : Fin 2 → Binary F) q = q ∧
          bind₁ (![0, X 1] : Fin 2 → Binary F) q = 0 ∧
          bind₁ (![X 0, 0] : Fin 2 → Binary F) q = 0 ∧
          q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) ∧
        f = cyclicLift q) ∧
    (∀ q : Binary F, q.IsHomogeneous n →
      (bind₁ (![X 1, X 0] : Fin 2 → Binary F) q = -q ∧
          bind₁ (![-X 0, X 1] : Fin 2 → Binary F) q = q ∧
          bind₁ (![X 0, -X 1] : Fin 2 → Binary F) q = q ∧
          bind₁ (![0, X 1] : Fin 2 → Binary F) q = 0 ∧
          bind₁ (![X 0, 0] : Fin 2 → Binary F) q = 0 ∧
          q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) →
        f = cyclicLift q → q = bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) := by
  refine ⟨⟨fun hsol => ?_, ?_⟩, ?_⟩
  · have hr := TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hsol
    have he : bind₁ (![-X 0, X 1] : Fin 2 → Binary F) (restriction f) = restriction f :=
      (TernaryPeriodPolynomials.Argument.RouteIndependent.restriction_alternating_iff hsol).mp ha
    have halt : bind₁ (![X 1, X 0] : Fin 2 → Binary F) (restriction f) = -restriction f := by
      have h := restriction_swap f
      rw [ha] at h
      exact h.symm.trans (map_neg _ _)
    have hsecond : bind₁ (![X 0, -X 1] : Fin 2 → Binary F) (restriction f) = restriction f := by
      have e1 := hr.eval_swap_of_even he (X 0 : Binary F) (-X 1)
      have e2 := binaryEval_even_first he (X 1 : Binary F) (X 0)
      have e3 := hr.eval_swap_of_even he (X 0 : Binary F) (X 1)
      rw [binaryEval_X] at e3
      change binaryEval (restriction f) (X 0) (-X 1) = restriction f
      linear_combination e1 - e2 - e3
    have hprops : (bind₁ (![X 1, X 0] : Fin 2 → Binary F) (restriction f) = -restriction f ∧
          bind₁ (![-X 0, X 1] : Fin 2 → Binary F) (restriction f) = restriction f ∧
          bind₁ (![X 0, -X 1] : Fin 2 → Binary F) (restriction f) = restriction f ∧
          bind₁ (![0, X 1] : Fin 2 → Binary F) (restriction f) = 0 ∧
          bind₁ (![X 0, 0] : Fin 2 → Binary F) (restriction f) = 0 ∧
          restriction f + bind₁ ![-X 1, X 0 - X 1] (restriction f) +
            bind₁ ![X 1 - X 0, -X 0] (restriction f) = 0) :=
      ⟨halt, he, hsecond, restriction_axis_first hsol, restriction_axis_second hsol,
        restriction_three_term hsol⟩
    refine ⟨restriction f, ⟨restriction_homogeneous hf, hprops,
      (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hsol).symm⟩, ?_⟩
    rintro q ⟨-, ⟨h1, h2, -, h4, h5, h6⟩, hfq⟩
    have hrel := periodRelations_of_alternating_literal h1 h2 h4 h5 h6
    rw [hfq, restriction_cyclicLift hrel]
  · rintro ⟨q, ⟨-, ⟨h1, h2, -, h4, h5, h6⟩, hfq⟩, -⟩
    rw [hfq]
    exact cyclicLift_solution (periodRelations_of_alternating_literal h1 h2 h4 h5 h6)
  · rintro q - ⟨h1, h2, -, h4, h5, h6⟩ hfq
    have hrel := periodRelations_of_alternating_literal h1 h2 h4 h5 h6
    rw [hfq]
    exact (restriction_cyclicLift hrel).symm

/-- **Proposition 6.1** (`prop:coefficient-base-change`). For every commutative `ℚ`-algebra `A` and
every `n ≥ 0`, the natural maps `a ⊗ f ↦ a • f` (coefficient extension) are `A`-linear isomorphisms
`A ⊗_ℚ W_n → W_n(A)` and `A ⊗_ℚ 𝒫⁰_n → 𝒫⁰_n(A)`, and likewise for the symmetric and alternating
solution spaces and for the even and odd period spaces; coefficient extension commutes with
restriction to a coordinate plane and with cyclic summation. -/
theorem proposition_6_1 (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    (∃ e : A ⊗[ℚ] solutionSpace ℚ n ≃ₗ[A] solutionSpace A n,
      ∀ (a : A) (f : solutionSpace ℚ n),
        ((e (a ⊗ₜ[ℚ] f) : solutionSpace A n) : Ternary A) =
          a • map (algebraMap ℚ A) (f : Ternary ℚ)) ∧
    (∃ e : A ⊗[ℚ] periodSpace ℚ n ≃ₗ[A] periodSpace A n,
      ∀ (a : A) (q : periodSpace ℚ n),
        ((e (a ⊗ₜ[ℚ] q) : periodSpace A n) : Binary A) = a • map (algebraMap ℚ A) (q : Binary ℚ)) ∧
    (∃ e : A ⊗[ℚ] symmetricSolutionSpace ℚ n ≃ₗ[A] symmetricSolutionSpace A n,
      ∀ (a : A) (f : symmetricSolutionSpace ℚ n),
        ((e (a ⊗ₜ[ℚ] f) : symmetricSolutionSpace A n) : Ternary A) =
          a • map (algebraMap ℚ A) (f : Ternary ℚ)) ∧
    (∃ e : A ⊗[ℚ] alternatingSolutionSpace ℚ n ≃ₗ[A] alternatingSolutionSpace A n,
      ∀ (a : A) (f : alternatingSolutionSpace ℚ n),
        ((e (a ⊗ₜ[ℚ] f) : alternatingSolutionSpace A n) : Ternary A) =
          a • map (algebraMap ℚ A) (f : Ternary ℚ)) ∧
    (∃ e : A ⊗[ℚ] evenPeriodSpace ℚ n ≃ₗ[A] evenPeriodSpace A n,
      ∀ (a : A) (q : evenPeriodSpace ℚ n),
        ((e (a ⊗ₜ[ℚ] q) : evenPeriodSpace A n) : Binary A) =
          a • map (algebraMap ℚ A) (q : Binary ℚ)) ∧
    (∃ e : A ⊗[ℚ] oddPeriodSpace ℚ n ≃ₗ[A] oddPeriodSpace A n,
      ∀ (a : A) (q : oddPeriodSpace ℚ n),
        ((e (a ⊗ₜ[ℚ] q) : oddPeriodSpace A n) : Binary A) =
          a • map (algebraMap ℚ A) (q : Binary ℚ)) ∧
    (∀ f : Ternary ℚ,
      map (algebraMap ℚ A) (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary ℚ) f) =
        bind₁ (![X 0, X 1, 0] : Fin 3 → Binary A) (map (algebraMap ℚ A) f)) ∧
    (∀ q : Binary ℚ,
      map (algebraMap ℚ A) (bind₁ (![X 0, X 1] : Fin 2 → Ternary ℚ) q +
          bind₁ (![X 1, X 2] : Fin 2 → Ternary ℚ) q + bind₁ (![X 2, X 0] : Fin 2 → Ternary ℚ) q) =
        bind₁ (![X 0, X 1] : Fin 2 → Ternary A) (map (algebraMap ℚ A) q) +
          bind₁ (![X 1, X 2] : Fin 2 → Ternary A) (map (algebraMap ℚ A) q) +
            bind₁ (![X 2, X 0] : Fin 2 → Ternary A) (map (algebraMap ℚ A) q)) :=
  ⟨⟨solution_baseChangeEquiv A n, solution_baseChangeEquiv_tmul A n⟩,
    ⟨normalizedPeriod_baseChangeEquiv A n, normalizedPeriod_baseChangeEquiv_tmul A n⟩,
    ⟨symmetricSolution_baseChangeEquiv A n, symmetricSolution_baseChangeEquiv_tmul A n⟩,
    ⟨alternatingSolution_baseChangeEquiv A n, alternatingSolution_baseChangeEquiv_tmul A n⟩,
    ⟨evenPeriod_baseChangeEquiv A n, evenPeriod_baseChangeEquiv_tmul A n⟩,
    ⟨oddPeriod_baseChangeEquiv A n, oddPeriod_baseChangeEquiv_tmul A n⟩,
    map_coordinateRestriction (algebraMap ℚ A), map_cyclicSum (algebraMap ℚ A)⟩

/-- **Lemma 2.2** (`lem:sym-boundary-factors`). A symmetric homogeneous solution `f ∈ V_n` (over
`ℚ`) is divisible by `c₊ = (x+y)(x+z)(y+z)`; in positive even degree it is divisible by `w c₊`
with `w = x+y+z`. (Symmetry is the swap `f(y,x,z) = f(x,y,z)` together with the cyclic equation
of a solution.) -/
theorem lemma_2_2 {n : ℕ} {f : MvPolynomial (Fin 3) ℚ} (hh : f.IsHomogeneous n)
    (hc : bind₁ (![X 1, X 2, X 0] : Fin 3 → MvPolynomial (Fin 3) ℚ) f = f)
    (hn : f + bind₁ (![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℚ) f +
      bind₁ (![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) ℚ) f = 0)
    (hs : bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) ℚ) f = f) :
    ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2) : MvPolynomial (Fin 3) ℚ) ∣ f ∧
      (0 < n → Even n →
        ((X 0 + X 1 + X 2) * ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2)) :
          MvPolynomial (Fin 3) ℚ) ∣ f) :=
  ⟨TernaryPoly.homogeneous_symmetric_pair_sum_product_dvd ⟨hc, hn⟩ hs hh,
    fun _ he => TernaryPoly.homogeneous_symmetric_total_pair_sum_product_dvd ⟨hc, hn⟩ hs hh he⟩

/-- **Theorem 1.2, last sentence** (`thm:symmetric-classification`). In the situation of
Theorem 1.2 (a symmetric homogeneous `f` over a field of characteristic zero satisfying the
three-term relation), the binary polynomial `q` with `f = Φ(q)` is uniquely `q(X,Y) = f(X,Y,0)`:
the restriction `f(X,Y,0)` is homogeneous of degree `n`, symmetric, odd in each variable and
satisfies the binary three-term relation, `f = Φ(f(X,Y,0))`, and every `q` with these properties
and `f = Φ(q)` equals `f(X,Y,0)`. -/
theorem theorem_1_2_restriction {F : Type*} [Field F] [CharZero F]
    {f : MvPolynomial (Fin 3) F} {n : ℕ} (hf : f.IsHomogeneous n) (hs : f.IsSymmetric)
    (hn : f + bind₁ ![-X 1, X 0 - X 1, X 2] f + bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f).IsHomogeneous n ∧
      (bind₁ ![X 1, X 0] (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) =
          bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f ∧
        bind₁ ![-X 0, X 1] (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) =
          -bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f ∧
        bind₁ ![X 0, -X 1] (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) =
          -bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f ∧
        bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f +
          bind₁ ![-X 1, X 0 - X 1] (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) +
          bind₁ ![X 1 - X 0, -X 0] (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) = 0) ∧
      f = cyclicLift (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f) ∧
      ∀ q : Binary F, q.IsHomogeneous n →
        (bind₁ ![X 1, X 0] q = q ∧ bind₁ ![-X 0, X 1] q = -q ∧ bind₁ ![X 0, -X 1] q = -q ∧
          q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) →
        f = cyclicLift q → q = bind₁ (![X 0, X 1, 0] : Fin 3 → Binary F) f := by
  obtain ⟨q₀, ⟨hh₀, hrel₀, hf₀⟩, -⟩ := (TernaryPeriodPolynomials.Argument.RouteIndependent.symmetric_classification hf hs).mp hn
  have hper : PeriodRelations q₀ := ((odd_relations_iff q₀).mpr hrel₀).1
  have hq₀ : restriction f = q₀ := by
    rw [hf₀]
    exact restriction_cyclicLift hper
  have hlit := (symmetric_binary_relations_literal q₀).mp hrel₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (restriction f).IsHomogeneous n
    rw [hq₀]; exact hh₀
  · change (bind₁ ![X 1, X 0] (restriction f) = restriction f ∧
      bind₁ ![-X 0, X 1] (restriction f) = -restriction f ∧
        bind₁ ![X 0, -X 1] (restriction f) = -restriction f ∧
      restriction f + bind₁ ![-X 1, X 0 - X 1] (restriction f) +
        bind₁ ![X 1 - X 0, -X 0] (restriction f) = 0)
    rw [hq₀]; exact hlit
  · change f = cyclicLift (restriction f)
    rw [hq₀]; exact hf₀
  · intro q _ hq hfq
    have hrel : TernaryPoly.BinaryComplexPeriod.Relations F q :=
      (symmetric_binary_relations_literal q).mpr hq
    have hper' : PeriodRelations q := ((odd_relations_iff q).mpr hrel).1
    rw [hfq]
    exact (restriction_cyclicLift hper').symm

end TernaryPeriodPolynomials.Argument.Statements
