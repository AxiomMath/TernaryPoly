module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Evaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Presentation
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.CoordinateApartment

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFiberComparison
open ModThreeGoodAction OrdinaryCovectors OrdinaryPolynomialFiberSystem
open OrdinaryApartmentEvaluation OrdinaryApartmentPresentation

/-- The same literal coordinate lines in the ambient and ordinary incidence models. -/
theorem ordinary_coordinate (j : Fin 3) :
    OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 j.castSucc)=
      OrdinaryIncidence.goodLine (ReferenceApartmentRelations.coordinateLine j) := by
  apply Subtype.ext
  change (AugmentedFrameComplex.augmentedLine 1 j.castSucc).val=
    (ReferenceApartmentRelations.coordinateLine j).val
  rw [IntegralFrameHeightReduction.columnLine_span]
  rfl

/-- The integral identity frame is exactly the included Good reference apartment. -/
theorem frameCycle_one : frameCycle 1=
    OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment := by
  rw [frameCycle_apartment]
  apply Subtype.ext
  change GoodApartmentCycles.apartmentChain (fun _ => True)
    (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 0))
    (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 1))
    (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 2))=
    OrdinaryCoordinateApartment.inclusion (GoodApartmentCycles.apartmentChain Good
      (ReferenceApartmentRelations.coordinateLine 0) (ReferenceApartmentRelations.coordinateLine 1)
      (ReferenceApartmentRelations.coordinateLine 2))
  rw [OrdinaryCoordinateApartment.include_apartment]
  have h0 : OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 0)=
      OrdinaryIncidence.goodLine (ReferenceApartmentRelations.coordinateLine 0) := ordinary_coordinate 0
  have h1 : OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 1)=
      OrdinaryIncidence.goodLine (ReferenceApartmentRelations.coordinateLine 1) := ordinary_coordinate 1
  have h2 : OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 2)=
      OrdinaryIncidence.goodLine (ReferenceApartmentRelations.coordinateLine 2) := ordinary_coordinate 2
  rw [h0,h1,h2]

/-- The genuine ordinary-cycle map constructed from all literal polynomial fibers. -/
def cycleMap (n : ℕ) (F : Covector → TernaryPolynomial) (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n :=
  (relativeEvaluator (fiberFrameValues n F h hF)).comp presentation.symm.toLinearMap

/-- On every unrestricted integral apartment, the constructed map has its literal fiber value. -/
theorem cycleMap_frame (n : ℕ) (F : Covector → TernaryPolynomial) (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) :
    cycleMap n F h hF (frameCycle g)=frameValue n F hF g := by
  change relativeEvaluator (fiberFrameValues n F h hF)
    (presentation.symm (presentation (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle g))))=_
  rw [LinearEquiv.symm_apply_apply,relativeEvaluator_triangle]
  rfl

/-- The constructed actual cycle functional is equivariant for the genuine K coefficient action. -/
theorem cycleMap_equivariant (n : ℕ) (F : Covector → TernaryPolynomial) (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) (k : K) (z : OrdinaryIncidenceChains.Cycles) :
    cycleMap n F h hF (OrdinaryIncidenceChains.complex.cyclesAction k z)=
      GoodChainComplex.coefficientAction n (-1) k (cycleMap n F h hF z) := by
  have he : (cycleMap n F h hF).comp (OrdinaryIncidenceChains.complex.cyclesAction k)=
      (GoodChainComplex.coefficientAction n (-1) k).comp (cycleMap n F h hF) := by
    apply cycle_functional_ext
    intro g
    simp only [LinearMap.comp_apply,frameCycle_equivariant,cycleMap_frame]
    exact frameValue_equivariant n F hF k g
  exact LinearMap.congr_fun he z

/-- The original fiber is recovered at the literal included reference apartment. -/
theorem cycleMap_reference (n : ℕ) (F : Covector → TernaryPolynomial) (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) :
    (cycleMap n F h hF (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment) :
      TernaryPolynomial)=F ![1,1,1] := by
  rw [←frameCycle_one,cycleMap_frame,frameValue_coe,framePoly_one]

/-- Literal all-fiber equations yield the requested equivariant functional on actual ordinary cycles. -/
theorem exists_equivariant_cycle_map (n : ℕ) (F : Covector → TernaryPolynomial) (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) :
    ∃ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ k z,Φ (OrdinaryIncidenceChains.complex.cyclesAction k z)=
        GoodChainComplex.coefficientAction n (-1) k (Φ z)) ∧
      (Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment) : TernaryPolynomial)=F ![1,1,1] :=
  ⟨cycleMap n F h hF,cycleMap_equivariant n F h hF,cycleMap_reference n F h hF⟩

end TernaryPoly.OrdinaryFiberComparison
