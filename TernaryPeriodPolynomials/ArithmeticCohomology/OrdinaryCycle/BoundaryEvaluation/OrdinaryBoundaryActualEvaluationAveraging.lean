module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.TranslatedEvaluation

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence ModThreeGoodAction
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer EquivariantSingularSmall
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison OrdinaryApartmentPresentation
open OrdinaryBoundaryCone RationalCohomologyDescent

/-- The actual finite-index descent projector on a represented cover-boundary cocycle. -/
def averagedBoundaryCocycle (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1 :=
  cyclesMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 x

/-- Its literal cochain is the normalized trace followed by restriction. -/
theorem averagedBoundaryCocycle_value (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    cocycleValue boundaryChains (restrictedCoefficients n e) 1 (averagedBoundaryCocycle n e x) =
      restrictHom principalSix (fullBoundaryChains.X 1) (actualCoefficients n e)
        (transferHom principalSix (fullBoundaryChains.X 1) (actualCoefficients n e)
          (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x)) := by
  have h := congrArg (fun f => f x)
    (cyclesMap_i (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  exact h

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Full ordinary equivariance cancels both genuine action factors in each transferred frame value. -/
theorem averagedBoundaryCocycle_frame (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1)
    (hx : ordinaryFunctionalFullEquivariant n e
      (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x)))
    (g : IntegralGL) :
    (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
        (averagedBoundaryCocycle n e x))).hom (frameCycle g) =
    (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x)).hom (frameCycle g) := by
  classical
  let φ := boundaryOrdinaryEvaluation (restrictedCoefficients n e)
    ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x)
  rw [boundaryOrdinaryEvaluation_frame, averagedBoundaryCocycle_value]
  change (transferHom principalSix (fullBoundaryChains.X 1) (actualCoefficients n e)
    (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x)).hom
    ((fullBoundaryChains.X 1).ρ g ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain)) = _
  erw [transferHom_apply]
  have hs (q : RightCosets principalSix) :
      (actualCoefficients n e).ρ q.out⁻¹
        ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x).hom
          ((fullBoundaryChains.X 1).ρ q.out
            ((fullBoundaryChains.X 1).ρ g ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain)))) =
      φ.hom (frameCycle g) := by
    have hp := hx q.out (frameCycle g)
    rw [OrdinaryFullAction.frameCycle_equivariant] at hp
    have ha := LinearMap.congr_fun ((fullBoundaryChains.X 1).ρ.map_mul q.out g)
      ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain)
    change (fullBoundaryChains.X 1).ρ (q.out * g) _ =
      (fullBoundaryChains.X 1).ρ q.out ((fullBoundaryChains.X 1).ρ g _) at ha
    rw [← ha, ← boundaryOrdinaryEvaluation_frame, hp,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  trans (Nat.card (RightCosets principalSix) : ℚ)⁻¹ •
    ∑ _ : RightCosets principalSix, φ.hom (frameCycle g)
  · exact congrArg (fun v => (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • v)
      (Finset.sum_congr rfl (fun q _ => hs q))
  have hc : (∑ _ : RightCosets principalSix, φ.hom (frameCycle g)) =
      (Nat.card (RightCosets principalSix) : ℚ) • φ.hom (frameCycle g) := by
    simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    exact (Nat.cast_smul_eq_nsmul ℚ (Fintype.card (RightCosets principalSix)) _).symm
  rw [hc, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.card_pos (α := RightCosets principalSix)).ne'

/-- Averaging fixes the entire actual ordinary functional, by the proved integral apartment span. -/
theorem averagedBoundaryCocycle_ordinary (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1)
    (hx : ordinaryFunctionalFullEquivariant n e
      (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x))) :
    boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
        (averagedBoundaryCocycle n e x)) =
    boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply OrdinaryApartmentPresentation.cycle_functional_ext
  intro g
  exact averagedBoundaryCocycle_frame n e x hx g

/-- The same equality holds on actual cohomology classes; no full-level hypothesis on a preimage is used. -/
theorem averagedBoundaryClass_ordinary (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1)
    (hx : ordinaryFunctionalFullEquivariant n e (boundaryOrdinaryEvaluation (restrictedCoefficients n e) x)) :
    boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      (homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 x) =
    boundaryOrdinaryEvaluation (restrictedCoefficients n e) x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1)).mp inferInstance x
  have h := congrArg (fun f => f z)
    (homologyπ_naturality (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  change homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 z) =
    (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 (averagedBoundaryCocycle n e z) at h
  rw [h]
  exact averagedBoundaryCocycle_ordinary n e z hx

end TernaryPoly.OrdinaryBoundaryActualEvaluation
