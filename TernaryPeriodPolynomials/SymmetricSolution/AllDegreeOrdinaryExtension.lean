module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.OrdinaryExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SymmetricExtension

@[expose] public section


noncomputable section
namespace TernaryPoly

/-- Every positive-degree homogeneous symmetric Todd-zero period polynomial extends to a
homogeneous actual full polynomial fiber system, with no parity or supplied-tower premise. -/
theorem symmetric_all_degree_ordinary_extension {f : TernaryPolynomial} {n : ℕ}
    (hn : 0<n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ F : OrdinaryCovectors.Covector → TernaryPolynomial,
      OrdinaryPolynomialFiberSystem.System F ∧ F ![1,1,1]=f ∧
      ∀ r,(F r).IsHomogeneous n := by
  rcases Nat.even_or_odd n with he | ho
  · exact symmetric_even_ordinary_extension hn he hf hrel hs hJ
  · exact symmetric_odd_ordinary_extension hf ho hrel hs hJ

/-- Positive-degree homogeneous symmetric Todd-zero period polynomials are literal reference
coefficients of genuine ordinary-cycle functionals with the exact determinant-minus-one action. -/
theorem symmetric_all_degree_Todd_zero_ordinary_cycle_extension {f : TernaryPolynomial} {n : ℕ}
    (hn : 0<n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ k z,Φ (OrdinaryIncidenceChains.complex.cyclesAction k z)=
        GoodChainComplex.coefficientAction n (-1) k (Φ z)) ∧
      (Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)).val=f := by
  obtain ⟨F,hF,hvalue,hdegree⟩ := symmetric_all_degree_ordinary_extension hn hf hrel hs hJ
  obtain ⟨Φ,hΦ,hreference⟩ := OrdinaryFiberComparison.exists_equivariant_cycle_map n F hF hdegree
  exact ⟨Φ,hΦ,hreference.trans hvalue⟩

end TernaryPoly
