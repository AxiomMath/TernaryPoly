module

public import TernaryPeriodPolynomials.Polynomial.Classification.Pairwise
public import TernaryPeriodPolynomials.Polynomial.RestrictionRecovery
public import TernaryPeriodPolynomials.Polynomial.ClassificationEquivalence
public import TernaryPeriodPolynomials.Polynomial.PeriodNormalization

@[expose] public section



/-!
# Restriction to `z = 0` determines every solution

For a solution `f ∈ R[x, y, z]` of the cyclic and three-term relations over a `ℚ`-algebra `R`,
the restriction `q(X, Y) = f(X, Y, 0)` satisfies the normalized binary period relations and
`f = Φ(q) = q(x, y) + q(y, z) + q(z, x)` (`cyclicLift_restriction`). The pairwise decomposition used
here is `Argument.Classification.solution_pairwise`; we also derive the odd-degree vanishing
`solution_odd_eq_zero` and the description of the symmetric sector.
-/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.Classification

variable {R : Type*} [CommRing R]

/-- Every solution is the cyclic sum of its literal binary restriction. -/
theorem cyclicLift_restriction [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    cyclicLift (restriction f) = f := by
  have h := (solution_pairwise f hf).inclusion_exclusion (X 0 : Ternary R) (X 1) (X 2)
  have h₀ : ternaryEval f (X 0 : Ternary R) 0 0 = 0 :=
    (hf.eval_cyclic (X 0) 0 0).symm.trans (hf.axis_zero (X 0))
  have h₁ : ternaryEval f (0 : Ternary R) (X 1) 0 = 0 :=
    (hf.eval_cyclic 0 0 (X 1)).trans (hf.axis_zero (X 1))
  rw [ternaryEval_X, h₀, h₁, hf.axis_zero, hf.axis_zero, sub_zero, sub_zero,
    sub_zero, add_zero] at h
  rw [cyclicLift, binaryEval_restriction, binaryEval_restriction, binaryEval_restriction]
  rw [hf.eval_cyclic 0 (X 1) (X 2), ← hf.eval_cyclic (X 2) (X 0) 0]
  exact h.symm

/-- The ternary norm makes the binary reflection defect additive. -/
theorem restriction_defect_doubling [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    bind₁ ![2*X 0, X 1] (reflectionDefect (restriction f)) =
      2 * reflectionDefect (restriction f) := by
  let q := restriction f
  have hF : Solution (cyclicLift q) := by
    simpa only [q, cyclicLift_restriction hf] using hf
  have hN (a b : Binary R) :
      binaryEval q a b + binaryEval q (-b) (a-b) + binaryEval q (b-a) (-a) = 0 := by
    have h := congrArg (fun p : Binary R => binaryEval p a b) (restriction_three_term hf)
    simpa [q, binaryEval, bind₁_bind₁, bind_vec2] using h
  have hres (a b c : Binary R) :
      binaryEval (reflectionDefect q) b c + binaryEval (reflectionDefect q) (a-b) c +
        binaryEval (reflectionDefect q) (-a) c = 0 := by
    have h := hF.eval_norm a b c
    simp only [ternaryEval, bind_cyclicLift] at h
    have hn := hN a b
    simp only [reflectionDefect, binaryEval_add]
    simp only [binaryEval, bind₁_bind₁, bind_vec2, map_neg, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]
    simp only [binaryEval] at h hn
    have he : -(a-b)=b-a := by ring
    rw [he]
    linear_combination h - hn
  have hzero (c : Binary R) : binaryEval (reflectionDefect q) 0 c = 0 := by
    have h₀ := congrArg (fun p : Binary R => binaryEval p 0 c) (restriction_axis_first hf)
    have h₁ := congrArg (fun p : Binary R => binaryEval p c 0) (restriction_axis_second hf)
    simp [binaryEval, bind₁_bind₁, bind_vec2] at h₀ h₁
    simp [reflectionDefect, q, binaryEval, bind₁_bind₁, bind_vec2, h₀, h₁]
  have h₁ := hres (2*X 0) (X 0) (X 1)
  have h₂ := hres (2*X 0) (2*X 0) (X 1)
  have he : (2*X 0-X 0 : Binary R) = X 0 := by ring
  rw [he] at h₁
  rw [sub_self, hzero, add_zero] at h₂
  change binaryEval (reflectionDefect q) (2*X 0) (X 1) = 2 * reflectionDefect q
  have hh : binaryEval (reflectionDefect q) (2*X 0 : Binary R) (X 1) =
      2 * binaryEval (reflectionDefect q) (X 0) (X 1) := by
    linear_combination h₂ - h₁
  simpa only [binaryEval_X] using hh

/-- Every ternary solution restricts to the full normalized period relations. -/
theorem restriction_periodRelations [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    PeriodRelations (restriction f) := by
  refine ⟨restriction_axis_first hf, restriction_axis_second hf, ?_, restriction_three_term hf⟩
  exact two_term_of_defect_doubling (restriction f) (restriction_axis_first hf)
    (restriction_axis_second hf) (restriction_three_term hf) (restriction_defect_doubling hf)

/-- The symmetric ternary sector restricts exactly to odd binary periods. -/
theorem restriction_symmetric_iff [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    bind₁ ![X 1,X 0,X 2] f = f ↔
      bind₁ ![-X 0,X 1] (restriction f) = -restriction f := by
  constructor
  · intro hs
    have hswap : bind₁ ![X 1,X 0] (restriction f) = restriction f := by
      rw [← restriction_swap, hs]
    have hn := (restriction_periodRelations hf).identities.eval_two_term
      (X 1 : Binary R) (X 0)
    change bind₁ ![X 1,X 0] (restriction f) +
      bind₁ ![-X 0,X 1] (restriction f) = 0 at hn
    rw [hswap] at hn
    exact eq_neg_of_add_eq_zero_right hn
  · intro ho
    rw [← cyclicLift_restriction hf]
    exact cyclicLift_symmetric (restriction_periodRelations hf) ho

/-- Odd-degree homogeneous solutions vanish (same mechanism as
`TernaryPoly.Paper.ClassificationEquivalence.solution_odd_eq_zero`: binary restriction plus
the generic binary odd-vanishing lemma `period_odd_eq_zero`). -/
theorem solution_odd_eq_zero {F : Type*} [Field F] [CharZero F] {f : Ternary F} {n : ℕ}
    (hh : f.IsHomogeneous n) (hf : Solution f) (hn : Odd n) : f = 0 := by
  have hq := period_odd_eq_zero (restriction_homogeneous hh)
    (restriction_periodRelations hf).identities hn
  rw [← cyclicLift_restriction hf, hq]
  simp [cyclicLift]

end TernaryPeriodPolynomials.Argument.Classification
