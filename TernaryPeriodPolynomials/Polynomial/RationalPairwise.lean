module

public import TernaryPeriodPolynomials.SymmetricSolution.EisensteinObstruction
public import TernaryPeriodPolynomials.SymmetricSolution.BernoulliTodd
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.InnerVanishing
public import TernaryPeriodPolynomials.Polynomial.PositiveInnerVanishing

@[expose] public section


/-! The original ternary polynomial theorem. Its scalar input is proved here
from the new Eisenstein obstruction, not imported as an independent assumption.
The ordinary-boundary input is the existing proof in the original library.
-/

noncomputable section
namespace TernaryPeriodPolynomials
open MvPolynomial

/-- The scalar gate is a consequence of the six child/graph inputs. -/
theorem scalar_zero : TernaryPoly.ScalarGates.ScalarZero := by
  intro n f hn hf hrel hs
  have hj := bernoulli_obstruction_vanishes_from_children n hn
    (⟨MvPolynomial.map (algebraMap ℚ ℂ) f, hf.map (algebraMap ℚ ℂ)⟩ :
      GeneralEisenstein.HomogeneousPoly n)
    (mapped_symmetricSolution hf hrel hs)
  have hmap : MvPolynomial.map (algebraMap ℚ ℂ) (TernaryPoly.symmetricTodd f) = 0 :=
    (map_symmetricTodd hf).trans hj
  have hz : TernaryPoly.symmetricTodd f = 0 :=
    MvPolynomial.map_injective (algebraMap ℚ ℂ)
      (FaithfulSMul.algebraMap_injective ℚ ℂ) (hmap.trans (map_zero _).symm)
  simp only [TernaryPoly.symmetricScalar, hz, map_zero, Polynomial.coeff_zero]

/-- Rational polynomial conclusion of the Ilin–Ono paper: a rational polynomial
satisfying the cyclic and three-term relations is a sum of three polynomials in
pairs of variables. -/
theorem ternary_period_polynomial_pairwise (f : MvPolynomial (Fin 3) ℚ)
    (hcyclic : MvPolynomial.bind₁ ![MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 0] f = f)
    (hnorm : f + MvPolynomial.bind₁
        ![-MvPolynomial.X 1, MvPolynomial.X 0 - MvPolynomial.X 1, MvPolynomial.X 2] f +
      MvPolynomial.bind₁
        ![MvPolynomial.X 1 - MvPolynomial.X 0, -MvPolynomial.X 0, MvPolynomial.X 2] f = 0) :
    ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f = MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) p +
        MvPolynomial.rename (![1, 2] : Fin 2 → Fin 3) q +
        MvPolynomial.rename (![0, 2] : Fin 2 → Fin 3) r :=
  TernaryPoly.OrdinaryBoundaryActualEvaluation.benchmark_of_inner_vanishing_and_scalar_zero
    TernaryPoly.SymmetricSpaceAllTopBoundary.positivePolynomialInnerVanishing
    scalar_zero f hcyclic hnorm

end TernaryPeriodPolynomials
