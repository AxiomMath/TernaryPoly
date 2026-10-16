module

public import TernaryPeriodPolynomials.SymmetricSolution.CoefficientCondition.CoefficientCondition
public import TernaryPeriodPolynomials.PeriodPolynomial.SignedBinary.SignedBinary

@[expose] public section


/-!
# MR-3 connected to the paper's objects `𝓑_22^+`

Formalized by Claude Haiku 5.5. This file restates the MR-3 witness of
`CoefficientCondition.lean` as a member of the space `signedBinary 1 22` of S1's
`MainBodyRows/SignedBinary.lean` (the literal `eq:signed-binary` system with `ε = +1`), and of the
period space `oddPeriodSpace ℚ 22` through S1's `signedBinary_one_eq`.

No new mathematics: the six relations are the ones proved in `CoefficientCondition.lean`, and the
only extra step is `one_smul` / `neg_smul` to match `SignedBinaryRelations 1`, whose conjuncts
read `q = 1 • q` and `-q = (-1) • q` literally.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

/-- **MR-3 in `𝓑_22^+`**: some nonzero `q ∈ 𝓑_22^+ = signedBinary 1 22` has vanishing
`XY²¹`-coefficient `[XY^{d-1}] q = 0` with `d = 22`. -/
theorem coefficient_condition_not_sufficient_B :
    ∃ q ∈ signedBinary 1 22,
      q.coeff (Finsupp.single 0 1 + Finsupp.single 1 21) = 0 ∧ q ≠ 0 := by
  obtain ⟨q, hhom, r₁, r₂, r₃, r₄, r₅, r₆, hc, hne⟩ := coefficient_condition_not_sufficient
  refine ⟨q, ?_, hc, hne⟩
  rw [mem_signedBinary]
  refine ⟨hhom, ?_⟩
  unfold SignedBinaryRelations
  simp only [one_smul, neg_smul]
  exact ⟨r₁, r₂, r₃, r₄, r₅, r₆⟩

/-- **MR-3 in the period space**: the same statement for `𝒫_22^{0,odd}(ℚ) = oddPeriodSpace ℚ 22`,
transported through `signedBinary_one_eq`. -/
theorem coefficient_condition_not_sufficient_odd :
    ∃ q ∈ TernaryPoly.Paper.oddPeriodSpace ℚ 22,
      q.coeff (Finsupp.single 0 1 + Finsupp.single 1 21) = 0 ∧ q ≠ 0 := by
  rw [← signedBinary_one_eq]
  exact coefficient_condition_not_sufficient_B

end TernaryPeriodPolynomials.Argument.Identities

end
