module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.PolynomialGate
public import TernaryPeriodPolynomials.SymmetricSolution.ScalarGates

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory IntegralGL3Congruence PolynomialGLAction
open SymmetricSpaceAllTopBoundary OrdinaryBoundaryCommonRoot OrdinaryTopBoundaryComparison
open ScalarGates

/-- Every actual positive-degree K-equivariant ordinary polynomial functional has Pairwise
reference value conditional only on the precise positive-polynomial inner-vanishing gate. -/
theorem ordinary_reference_pairwise_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) (n : ℕ) (hn : 0 < n) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : Equivariant n e Φ) : Pairwise (referenceValue n Φ) := by
  have hp := ordinary_functional_pairwise_of_inner_vanishing h n hn e
    (inducedPrincipalOrdinaryFunctional n e Φ hΦ)
    (inducedPrincipalOrdinaryFunctional_fullEquivariant n e Φ hΦ)
  change Pairwise (evaluation n ((inducedPrincipalOrdinaryFunctional n e Φ hΦ).hom identityApartment)).val at hp
  erw [inducedPrincipalOrdinaryFunctional_reference] at hp
  exact hp

/-- The actual ordinary reference statement follows from the one explicit analytic statement. -/
theorem ordinaryReferencePairwise_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) : OrdinaryReferencePairwise := by
  intro n hn e _ Φ hΦ
  exact ordinary_reference_pairwise_of_inner_vanishing h n hn e Φ hΦ

/-- The weaker sector-specific ordinary gate follows from the same analytic obligation. -/
theorem sectorReferencePairwise_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) : SectorReferencePairwise :=
  sectorReferencePairwise_of_ordinary (ordinaryReferencePairwise_of_inner_vanishing h)

/-- Even alternating solutions need only the positive-polynomial analytic statement. -/
theorem even_alternating_pairwise_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) {n : ℕ} {f : TernaryPolynomial}
    (hn : 0 < n) (he : Even n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f = -f) : Pairwise f :=
  ScalarGates.even_alternating_pairwise (sectorReferencePairwise_of_inner_vanishing h)
    hn he hf hrel hs

/-- In the symmetric zero-Todd sector the Todd-zero premise remains explicit and separate
from the positive-polynomial inner-vanishing gate. -/
theorem symmetric_Todd_zero_pairwise_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) {n : ℕ} {f : TernaryPolynomial}
    (hn : 0 < n) (hf : f.IsHomogeneous n) (hrel : PeriodRelations f)
    (hs : S f = f) (hJ : symmetricTodd f = 0) : Pairwise f := by
  obtain ⟨Φ, hΦ, hreference⟩ := symmetric_all_degree_Todd_zero_ordinary_cycle_extension hn hf hrel hs hJ
  have hp := ordinary_reference_pairwise_of_inner_vanishing h n hn (-1) Φ hΦ
  change Pairwise (Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)).val at hp
  rw [hreference] at hp
  exact hp

/-- The exact conclusion follows from the two mathematical statements:
positive-polynomial inner vanishing and complete symmetric scalar vanishing. -/
theorem benchmark_of_inner_vanishing_and_scalar_zero
    (hinner : PositivePolynomialInnerVanishing) (hscalar : ScalarZero)
    (f : MvPolynomial (Fin 3) ℚ)
    (hcyclic : MvPolynomial.bind₁ ![MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 0] f = f)
    (hnorm : f + MvPolynomial.bind₁ ![-MvPolynomial.X 1, MvPolynomial.X 0 - MvPolynomial.X 1, MvPolynomial.X 2] f +
      MvPolynomial.bind₁ ![MvPolynomial.X 1 - MvPolynomial.X 0, -MvPolynomial.X 0, MvPolynomial.X 2] f = 0) :
    ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f = MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) p +
        MvPolynomial.rename (![1, 2] : Fin 2 → Fin 3) q +
        MvPolynomial.rename (![0, 2] : Fin 2 → Fin 3) r :=
  ScalarGates.benchmark_of_two_actual_gates hscalar
    (ordinaryReferencePairwise_of_inner_vanishing hinner) f hcyclic hnorm

end TernaryPoly.OrdinaryBoundaryActualEvaluation
