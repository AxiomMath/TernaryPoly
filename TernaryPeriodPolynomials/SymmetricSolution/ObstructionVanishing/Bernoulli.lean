module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction
public import TernaryPeriodPolynomials.Polynomial.NormKernelDegree
public import TernaryPeriodPolynomials.Building.BoundaryApartments

@[expose] public section



/-! For `n ≥ 4`, `TernaryPeriodPolynomials.PolynomialBoundaryBridge.polynomial_boundary_bridge` builds a global cocycle
`c` whose boundary coordinates already satisfy `line_restriction_eq_zero_of_good_vertices`'s two hypotheses
(`GoodBoundaryVanishing`, line `InnerBoundary`), and packages the implication from the line
coordinate's vanishing to the Bernoulli obstruction's vanishing; so `line_restriction_eq_zero_of_good_vertices` finishes
this case directly, no Hochschild–Serre computation needed.

For `n ≤ 3`, `SymmetricSolution f` specializes (via the cyclic permutation `finRotate 3`) to the
two-term `TernaryPoly.Paper.Solution f.val`, so `solution_homogeneous_symmetric_alternating_parts`'s low-degree vanishing clause gives
`f.val = 0`; the Bernoulli obstruction manifestly vanishes once the underlying polynomial does. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Classification

/-- The finite Bernoulli contraction operator sends the zero polynomial to zero: every iterate of
`pderiv 0` fixes `0`, so every term of the sum vanishes. -/
theorem bernoulliOperator_zero (n : ℕ) (t : Poly) : bernoulliOperator n t 0 = 0 := by
  unfold bernoulliOperator
  apply Finset.sum_eq_zero
  intro r _
  have hiter : (fun p : Poly => pderiv 0 p)^[r] (0 : Poly) = 0 :=
    Function.iterate_fixed (by simp) r
  rw [hiter]
  ring

/-- The Bernoulli obstruction depends on `f` only through `f.val`, and vanishes once that does. -/
theorem bernoulliObstruction_eq_zero_of_val_eq_zero {n : ℕ} (f : HomogeneousPoly n)
    (hf : f.val = 0) : bernoulliObstruction f = 0 := by
  simp [bernoulliObstruction, hf, bernoulliOperator_zero]

/-- `SymmetricSolution` specializes to the paper's generic-field `Solution` predicate on
`f.val`: the permutation-invariance clause is `SymmetricSolution`'s first conjunct specialized at
the cyclic permutation `finRotate 3` (which sends `0,1,2 ↦ 1,2,0`), and the two-term relation is
syntactically the same formula. -/
theorem symmetricSolution_to_solution {n : ℕ} (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) : TernaryPoly.Paper.Solution f.val := by
  have hp : (fun i => X (finRotate 3 i) : Fin 3 → Poly) = ![X 1, X 2, X 0] := by
    funext i
    fin_cases i <;> simp
  have hcyc := hf.1 (finRotate 3)
  rw [hp] at hcyc
  exact ⟨hcyc, hf.2⟩

/-- The proof of `symmetric_obstruction_vanishes`: split on whether `n ≥ 4`. -/
theorem symmetric_obstruction_vanishes_of_route (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    bernoulliObstruction f = 0 := by
  by_cases hn4 : 4 ≤ n
  · obtain ⟨F, τ, c, hFunc, hPath, hRealizes, hUniq, hgood, hline, hPure, hA, hB, hR, himp⟩ :=
      TernaryPeriodPolynomials.PolynomialBoundaryBridge.polynomial_boundary_bridge n hn f hf
    exact himp (TernaryPeriodPolynomials.line_restriction_eq_zero_of_good_vertices n hn4 c hline hgood)
  · have hn3 : n ≤ 3 := by omega
    have hhom : f.val.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n f.val).mp f.2
    have hsol : TernaryPoly.Paper.Solution f.val := symmetricSolution_to_solution f hf
    have hzero : f.val = 0 :=
      (TernaryPeriodPolynomials.solution_homogeneous_symmetric_alternating_parts (F := ℂ)).2.2 n f.val hn3 hhom hsol
    exact bernoulliObstruction_eq_zero_of_val_eq_zero f hzero

end TernaryPeriodPolynomials.Argument.Classification
