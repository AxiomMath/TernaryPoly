module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Complete
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootInduction

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory IntegralGL3Congruence ModThreeGoodAction PolynomialGLAction
open OrdinaryTopBoundaryComparison SymmetricSpaceBoundaryIncidenceHomology SymmetricSpaceBoundaryFull
open OrdinaryBoundaryCommonRoot OrdinaryBoundaryCone

/-- The literal ordinary cycle module with its actual full integral action. -/
abbrev fullOrdinaryCyclesRep : Rep.{0} ℚ IntegralGL :=
  Rep.of (OrdinaryFullAction.cycleAction.comp OrdinaryFullAction.integral)

/-- An actual subgroup equivariant polynomial functional is a genuine representation morphism. -/
def subgroupOrdinaryFunctional (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n e k (Φ z)) :
    Rep.res K.subtype fullOrdinaryCyclesRep ⟶ subgroupCoefficients n e :=
  Rep.ofHom ⟨Φ, fun k => LinearMap.ext (fun z => by
    change Φ (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral k.val) z) = _
    rw [OrdinaryFullAction.cycleAction_K]
    exact hΦ k z)⟩

/-- Actual coinduction and the proved 26-covector trivialization extend the whole K-functional. -/
def inducedOrdinaryFunctional (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n e k (Φ z)) :
    fullOrdinaryCyclesRep ⟶ actualCoefficients n e :=
  Rep.resCoindToHom K.subtype fullOrdinaryCyclesRep (subgroupCoefficients n e)
    (subgroupOrdinaryFunctional n e Φ hΦ) ≫ (coinducedIso n e).inv

/-- Identity evaluation of the inverse trivialization retains the distinguished support-three coordinate. -/
theorem fromCoinduced_evaluation (n : ℕ) (e : ℤ) (f : Coinduced n e) :
    evaluation n (fromCoinduced n e f) = f.val 1 := by
  rw [← toCoinduced_one, toCoinduced_fromCoinduced]

/-- The induced full-integral functional has exactly the original K-functional as distinguished coefficient. -/
theorem inducedOrdinaryFunctional_evaluation (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n e k (Φ z)) (z : OrdinaryIncidenceChains.Cycles) :
    evaluation n ((inducedOrdinaryFunctional n e Φ hΦ).hom z) = Φ z := by
  change evaluation n (fromCoinduced n e
    ((Rep.resCoindToHom K.subtype fullOrdinaryCyclesRep (subgroupCoefficients n e)
      (subgroupOrdinaryFunctional n e Φ hΦ)).hom z)) = _
  rw [fromCoinduced_evaluation]
  change Φ (fullOrdinaryCyclesRep.ρ 1 z) = Φ z
  rw [map_one, Module.End.one_apply]

/-- The induced ordinary functional restricted to the literal principal-six ordinary cycle module. -/
def inducedPrincipalOrdinaryFunctional (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n e k (Φ z)) :
    ordinaryFunctionals (restrictedCoefficients n e) :=
  Rep.ofHom ⟨(inducedOrdinaryFunctional n e Φ hΦ).hom.toLinearMap,
    fun g => LinearMap.ext (fun z => by
      have h := Rep.hom_comm_apply (inducedOrdinaryFunctional n e Φ hΦ) g.val z
      change (inducedOrdinaryFunctional n e Φ hΦ).hom
        (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g.val) z) = _ at h
      rw [show g.val = (principalToK g).val from rfl, OrdinaryFullAction.cycleAction_K] at h
      exact h)⟩

/-- Full IntegralGL equivariance is proved by actual coinduction, not imposed on the original K-functional. -/
theorem inducedPrincipalOrdinaryFunctional_fullEquivariant (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n e k (Φ z)) :
    ordinaryFunctionalFullEquivariant n e (inducedPrincipalOrdinaryFunctional n e Φ hΦ) := by
  intro g z
  exact Rep.hom_comm_apply (inducedOrdinaryFunctional n e Φ hΦ) g z

/-- The actual principal-six functional preserves the reference polynomial literally. -/
theorem inducedPrincipalOrdinaryFunctional_reference (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] HomogeneousPoly n)
    (hΦ : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n e k (Φ z)) :
    evaluation n ((inducedPrincipalOrdinaryFunctional n e Φ hΦ).hom identityApartment) =
      Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment) := by
  change evaluation n ((inducedOrdinaryFunctional n e Φ hΦ).hom identityApartment) = _
  rw [inducedOrdinaryFunctional_evaluation, identityApartment_reference]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
