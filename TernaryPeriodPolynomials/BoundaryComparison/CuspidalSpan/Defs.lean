module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# The span of the cusp-form seeds (Lemma C.3, `ar:lem:seed`)

Paper:, end of the proof of
Lemma C.3: by Eichler–Shimura at every plane cusp, the holomorphic and antiholomorphic seeds span
the mixed cuspidal space `𝒞_P(E)`. In the project's adelic boundary model a seed is the class of a
source cocycle of a cohomological cuspidal datum with trivial normal character; the classes of one
datum span its boundary summand. The line span `automorphicLineSpan` is defined in
`TernaryPeriodPolynomials/ArithmeticCohomology/Defs/DecompositionDefs.lean`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- The span of the plane summands of all cohomological cuspidal data with trivial normal
character. -/
def automorphicPlaneSpan (n : ℕ) : Submodule ℂ (StratumH2 n trivialCharacter .plane) :=
  Submodule.span ℂ {ξ | ∃ D : CohomologicalCuspData n, ξ ∈ boundarySummand D.inducingData .plane}

end TernaryPeriodPolynomials.Argument
