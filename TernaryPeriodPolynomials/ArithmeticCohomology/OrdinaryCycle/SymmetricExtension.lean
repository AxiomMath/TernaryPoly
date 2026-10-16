module

public import TernaryPeriodPolynomials.SymmetricSolution.OrdinaryExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.Comparison

@[expose] public section


noncomputable section
namespace TernaryPoly

/-- A positive-even symmetric solution in the entire Todd kernel has an actual ordinary-cycle
functional with its exact reference value and determinant-minus-one coefficient action. -/
theorem symmetric_Todd_zero_ordinary_cycle_extension {f : TernaryPolynomial} {n : ℕ}
    (hn : 0<n) (he : Even n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z)=
        GoodChainComplex.coefficientAction n (-1) k (Φ z)) ∧
      (Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)).val=f := by
  obtain ⟨F,hF,hvalue,hdegree⟩ := symmetric_even_ordinary_extension hn he hf hrel hs hJ
  obtain ⟨Φ,hΦ,hreference⟩ := OrdinaryFiberComparison.exists_equivariant_cycle_map n F hF hdegree
  exact ⟨Φ,hΦ,hreference.trans hvalue⟩

end TernaryPoly
