module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.PolynomialFiberSystem
public import TernaryPeriodPolynomials.SymmetricSolution.FirstJet.Lift
public import TernaryPeriodPolynomials.SymmetricSolution.SeedData

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The universal first-lift certificate supplies the last pure norm of the seed system. -/
theorem symmetric_seed_system {f P Q : TernaryPolynomial}
    (h : SymmetricSeedData f P Q) (hrel : PeriodRelations f) (hs : S f=f) :
    OrdinaryPolynomialFiberSystem.System (OrdinarySeedFibers.seedValue f P Q) :=
  OrdinaryPolynomialFiberSystem.seed_system h hrel.1 hs hrel.2
    (SymmetricFirstLift.norm_zero hrel.1 hs hrel.2 h.q_swap h.q_odd h.mixedQ)

/-- Every positive even symmetric Todd-kernel norm solution extends to an actual
homogeneous26-fiber polynomial system, with all48 signed-permutation equations. -/
theorem symmetric_even_ordinary_extension {f : TernaryPolynomial} {n : ℕ}
    (hn : 0<n) (he : Even n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ F : OrdinaryCovectors.Covector → TernaryPolynomial,
      OrdinaryPolynomialFiberSystem.System F ∧ F ![1,1,1]=f ∧
      ∀ r,(F r).IsHomogeneous n := by
  obtain ⟨P,Q,h⟩ := symmetric_even_polynomial_seeds hn he hf hrel hs hJ
  exact OrdinaryPolynomialFiberSystem.homogeneous_seed_extension h hrel.1 hs hrel.2
    (SymmetricFirstLift.norm_zero hrel.1 hs hrel.2 h.q_swap h.q_odd h.mixedQ) hf

end TernaryPoly
