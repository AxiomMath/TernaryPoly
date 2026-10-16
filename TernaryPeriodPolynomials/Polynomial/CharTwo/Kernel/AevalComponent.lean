module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.AevalWeighted

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial

/-- **STEP2b(iii) building block.** `aeval g` commutes with extracting a weighted-homogeneous
component, PROVIDED each generator image `g i` is itself `w'`-homogeneous of the matching degree
`w i` (the same hypothesis as `isWeightedHomogeneous_aeval`). No homogeneity assumption on `p`
itself is needed: both sides are linear in `p`, so it suffices to check monomials, where this
reduces to `isWeightedHomogeneous_aeval` plus `weightedHomogeneousComponent_same`/`_ne`. -/
theorem weightedHomogeneousComponent_aeval {R : Type*} [CommSemiring R] {σ τ : Type*}
    {w : σ → ℕ} {w' : τ → ℕ} {g : σ → MvPolynomial τ R}
    (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i)) (p : MvPolynomial σ R) (n : ℕ) :
    weightedHomogeneousComponent w' n (aeval g p) =
      aeval g (weightedHomogeneousComponent w n p) := by
  classical
  have key : ∀ d : σ →₀ ℕ, ∀ r : R,
      weightedHomogeneousComponent w' n (aeval g (monomial d r)) =
        aeval g (weightedHomogeneousComponent w n (monomial d r)) := by
    intro d r
    have hmono : IsWeightedHomogeneous w (monomial d r : MvPolynomial σ R) (Finsupp.weight w d) :=
      isWeightedHomogeneous_monomial w d r rfl
    have haeval_hom :
        IsWeightedHomogeneous w' (aeval g (monomial d r)) (Finsupp.weight w d) :=
      isWeightedHomogeneous_aeval w w' g hg hmono
    by_cases hnk : n = Finsupp.weight w d
    · rw [hnk, haeval_hom.weightedHomogeneousComponent_same,
        hmono.weightedHomogeneousComponent_same]
    · rw [haeval_hom.weightedHomogeneousComponent_ne n hnk,
        hmono.weightedHomogeneousComponent_ne n hnk, map_zero]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun d _ => key d (p.coeff d))

end TernaryPeriodPolynomials.Argument.CharTwoKernel
