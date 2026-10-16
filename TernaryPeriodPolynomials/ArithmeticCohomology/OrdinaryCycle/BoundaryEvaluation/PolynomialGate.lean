module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiberSplitting

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryFull SymmetricSpaceAllTopBoundary SingularLocalHomology
open SymmetricSpaceBoundaryDuality SingularBoundaryRestriction

/-- Actual boundary local homology as an additive coefficient functor. -/
def actualBoundaryHomologyFunctor (k : ℕ) : Rep.{0} ℚ principalSix ⥤ ModuleCat ℚ :=
  singularLocalCoefficientFunctor boundaryProjection boundaryQuotientCovering ⋙
    homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k

/-- Actual compactified arithmetic local homology as an additive coefficient functor. -/
def actualBordifiedHomologyFunctor (k : ℕ) : Rep.{0} ℚ principalSix ⥤ ModuleCat ℚ :=
  singularLocalCoefficientFunctor bordifiedProjection bordifiedProjection_quotientCovering ⋙
    homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k

instance actualBoundaryHomologyFunctor_additive (k : ℕ) : (actualBoundaryHomologyFunctor k).Additive := by
  unfold actualBoundaryHomologyFunctor
  infer_instance
instance actualBordifiedHomologyFunctor_additive (k : ℕ) : (actualBordifiedHomologyFunctor k).Additive := by
  unfold actualBordifiedHomologyFunctor
  infer_instance

/-- The actual entire-boundary inclusion is an additive coefficient-natural homology transformation. -/
def actualBoundaryHomologyNat (k : ℕ) : actualBoundaryHomologyFunctor k ⟶ actualBordifiedHomologyFunctor k :=
  CategoryTheory.Functor.whiskerRight (actualLocalSpaceCoefficientNat boundaryProjection boundaryQuotientCovering
    bordifiedProjection bordifiedProjection_quotientCovering boundaryInclusion boundaryInclusion_equivariant)
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k)

/-- The single positive-polynomial inner-vanishing gate gives actual boundary surjectivity
for the entire literal 26-fiber coefficient system. -/
theorem coefficient_boundary_surjective_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) (n : ℕ) (hn : 0 < n) (e : ℤ) :
    Function.Surjective (boundaryToGroup (restrictedCoefficients n e) 3).hom := by
  have hp : Function.Surjective (homologyMap (boundaryInclusionMap (polynomialCoefficients n e)) 3).hom :=
    (boundaryToGroup_surjective_iff (polynomialCoefficients n e) 3).mp
      (polynomial_boundary_surjective_of_inner_vanishing h n hn e)
  have hv := natural_surjective_of_finite_splitting
    (actualBoundaryHomologyFunctor 3) (actualBordifiedHomologyFunctor 3)
    (actualBoundaryHomologyNat 3) (polynomialCoefficients n e) (restrictedCoefficients n e)
    (coefficientFiberProjection n e) (coefficientFiberInsertion n e) (coefficientFiber_sum n e) hp
  exact (boundaryToGroup_surjective_iff (restrictedCoefficients n e) 3).mpr hv

/-- Every full-equivariant ordinary functional in positive degree satisfies Pairwise support
conditional only on the explicitly isolated positive-polynomial analytic gate. -/
theorem ordinary_functional_pairwise_of_inner_vanishing
    (h : PositivePolynomialInnerVanishing) (n : ℕ) (hn : 0 < n) (e : ℤ)
    (φ : OrdinaryTopBoundaryComparison.ordinaryFunctionals (restrictedCoefficients n e))
    (hfull : ordinaryFunctionalFullEquivariant n e φ) :
    coefficientPairwise n (φ.hom OrdinaryTopBoundaryComparison.identityApartment) := by
  exact ordinary_functional_boundary_pairwise n e φ hfull
    (coefficient_boundary_surjective_of_inner_vanishing h n hn e
      ((OrdinaryTopBoundaryComparison.groupOrdinaryIso (restrictedCoefficients n e)).inv φ))

end TernaryPoly.OrdinaryBoundaryActualEvaluation
