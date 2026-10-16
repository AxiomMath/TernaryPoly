module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma54

@[expose] public section


/-! Target: Lemma 5.4 (`mf:lem:cancellation`) of the paper. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma 5.4.** For every symmetric `g ∈ k[x,y,z]`, `k = 𝔽₂`, one has `Π N̄ g = 0`. -/
theorem charTwo_projector_norm_eq_zero (g : Poly2) (hg : g.IsSymmetric) :
    piOperator (TernaryPoly.CharTwoNorm.norm g) = 0 := by
  exact TernaryPeriodPolynomials.Argument.ModFourBeta.lemma_5_4_proof g hg

end TernaryPeriodPolynomials
