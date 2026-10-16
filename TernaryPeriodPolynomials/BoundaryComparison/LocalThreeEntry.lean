module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.LocalThreeEntry.Construction

@[expose] public section


/-! Target: the level-three local entry `ar:eq:local3` of Appendix C.6. -/

open GeneralEisenstein

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix C.6, level-three entry.** For a right `K₁`-invariant section supported on the
bad-plane double coset `P K₁`, the local intertwining integral at the good-line representative
`g₀` is supported on `(3ℤ₃)²` and equals `(T₃φ)(g₀) = v₀/9` (equation `ar:eq:local3`). -/
theorem local_three_entry : LocalBadPlaneEntry := by
  exact TernaryPeriodPolynomials.Argument.Classification.local_three_entry

end TernaryPeriodPolynomials
