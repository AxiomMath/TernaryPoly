module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.OrdinaryExtensionSeeds
public import TernaryPeriodPolynomials.SymmetricSolution.OrdinaryExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.Comparison

@[expose] public section


noncomputable section
namespace TernaryPoly

/-- Every odd homogeneous symmetric norm solution in the entire Todd kernel extends to the
actual homogeneous full polynomial fiber system, with its literal reference value. -/
theorem symmetric_odd_ordinary_extension {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ F : OrdinaryCovectors.Covector → TernaryPolynomial,
      OrdinaryPolynomialFiberSystem.System F ∧ F ![1,1,1]=f ∧
      ∀ r,(F r).IsHomogeneous n := by
  obtain ⟨P,Q,h⟩ := symmetric_odd_polynomial_seeds hf hn hrel hs hJ
  exact OrdinaryPolynomialFiberSystem.homogeneous_seed_extension h hrel.1 hs hrel.2
    (SymmetricFirstLift.norm_zero hrel.1 hs hrel.2 h.q_swap h.q_odd h.mixedQ) hf

/-- The same odd-degree hypotheses give a genuine equivariant functional on actual ordinary
incidence cycles with exact reference coefficient f and determinant-minus-one action. -/
theorem symmetric_odd_Todd_zero_ordinary_cycle_extension {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ k z,Φ (OrdinaryIncidenceChains.complex.cyclesAction k z)=
        GoodChainComplex.coefficientAction n (-1) k (Φ z)) ∧
      (Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)).val=f := by
  obtain ⟨F,hF,hvalue,hdegree⟩ := symmetric_odd_ordinary_extension hf hn hrel hs hJ
  obtain ⟨Φ,hΦ,hreference⟩ := OrdinaryFiberComparison.exists_equivariant_cycle_map n F hF hdegree
  exact ⟨Φ,hΦ,hreference.trans hvalue⟩

end TernaryPoly
