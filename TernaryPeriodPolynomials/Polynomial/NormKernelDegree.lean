module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Corollaries.Lemma21Parts
public import TernaryPeriodPolynomials.Polynomial.Corollaries.Lemma21Degree3

@[expose] public section


/-! Target: Lemma 2.1 (`lem:sector-decomp`) of the paper. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma 2.1.** Homogeneous components of a solution are solutions. Its symmetric and
alternating parts `(f + Sf)/2` and `(f - Sf)/2` are also solutions. There are no nonzero
solutions of degree at most three. -/
theorem solution_homogeneous_symmetric_alternating_parts {F : Type*} [Field F] [CharZero F] :
    (∀ f : MvPolynomial (Fin 3) F, Solution f → ∀ n : ℕ, Solution (homogeneousComponent n f)) ∧
    (∀ f : MvPolynomial (Fin 3) F, Solution f →
      Solution ((2 : F)⁻¹ • (f + bind₁ ![X 1, X 0, X 2] f)) ∧
      Solution ((2 : F)⁻¹ • (f - bind₁ ![X 1, X 0, X 2] f))) ∧
    (∀ (n : ℕ) (f : MvPolynomial (Fin 3) F), n ≤ 3 → f.IsHomogeneous n → Solution f → f = 0) := by
  refine ⟨fun f hf n => ?_, fun f hf => ⟨?_, ?_⟩, fun n f hn hh hf => ?_⟩
  · exact Solution.homogeneousComponent hf n
  · exact Solution.symmPart hf
  · exact Solution.altPart hf
  · exact degree_le_three_eq_zero n f hn hh hf

end TernaryPeriodPolynomials
