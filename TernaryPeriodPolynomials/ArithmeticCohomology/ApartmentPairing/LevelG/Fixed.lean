module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Invariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Descent

@[expose] public section


open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.SymmetricSpaceBoundaryFullTransfer TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary)
open TernaryPoly.SymmetricSpaceBoundaryFull

/-!
# Level G: `H₃(∂X̄_G; 𝓜)` is the space of `GL₃(ℤ)`-invariants (G-3)

Formalized by Claude Sonnet 5.5.

`H3boundaryG` (defined as the image of `H¹(Hom_G(C_*(∂X̄), M))` under dual restriction) is
identified with the fixed points of the geometric action `bAct` of `GL₃(ℤ)` on the neat-level boundary homology
`H₃(∂X̄_Γ(6); 𝓜)` (`mem_H3boundaryG_iff`), using equivariance of boundary Poincaré duality (`BR.PDboundary_equivariant`) and the
description of fixed cohomology classes as restrictions (`fixed_mem_range_restriction`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (n : ℕ) (e : ℤ)

/-- Restriction from the full boundary cochains to the neat-level boundary cochains `Hom(C_*(∂X̄), W)`. -/
def restrBd : fullBoundaryCochains n e ⟶ homCochains boundaryChains (restrictedCoefficients n e) :=
  restriction principalSix fullBoundaryChains (actualCoefficients n e)

theorem PDboundary_resToBoundary (ω : (fullBoundaryCochains n e).homology 1) :
    PDboundary (restrictedCoefficients n e) (resToBoundary n e ω) =
      homologyMap (restrBd n e) 1 ω := by
  unfold PDboundary
  rw [ConcreteCategory.comp_apply]
  have e1 : (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv (resToBoundary n e ω) =
      (homologyMap (boundaryRestriction n e) 1).hom ω :=
    Iso.hom_inv_id_apply _ _
  rw [e1]
  have e2 : homologyMap (restrBd n e) 1 =
      homologyMap (boundaryRestriction n e) 1 ≫ homologyMap (restrictedLocalIso n e).inv 1 := by
    rw [← homologyMap_comp]
    unfold boundaryRestriction restrBd
    simp
    rfl
  rw [e2]
  rfl

/-- Boundary Poincaré duality is injective (it is an isomorphism). -/
theorem PDboundary_injective :
    Function.Injective (PDboundary (restrictedCoefficients n e)).hom := by
  intro a b h
  unfold PDboundary at h
  have h1 := congrArg (OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso
    (restrictedCoefficients n e)).hom.hom h
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h1
  have h2 := congrArg (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
    SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom.hom h1
  simpa using h2

/-- **G-3: `H₃(∂X̄_G; 𝓜)` is exactly the subspace of `GL₃(ℤ)`-invariants of `H₃(∂X̄_Γ(6); 𝓜)`** under the geometric
action `bAct` on the singular boundary chains (rational averaging identifies invariants and
coinvariants).  Proof: `PD_∂` is `G`-equivariant (`PDboundary_equivariant`), restriction `H¹(Hom_G) → H¹(Hom_Γ)` lands in the
conjugation-fixed classes (`restriction_hcAct`) and every fixed class is a restriction (`fixed_mem_range_restriction`). -/
theorem mem_H3boundaryG_iff
    (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    c ∈ H3boundaryG n e ↔
      ∀ g : IntegralGL, homologyMap (bAct (actualCoefficients n e) g) 3 c = c := by
  constructor
  · rintro ⟨ω, rfl⟩ g
    apply PDboundary_injective n e
    rw [BR.PDboundary_equivariant]
    change _ = PDboundary (restrictedCoefficients n e) (resToBoundary n e ω)
    rw [PDboundary_resToBoundary]
    have h : (homologyMap (restrBd n e ≫ hcAct bdryAct
        (GAct.ofRep principalSix (actualCoefficients n e)) g) 1).hom ω =
        (homologyMap (restrBd n e) 1).hom ω := by
      rw [show restrBd n e ≫ hcAct bdryAct
        (GAct.ofRep principalSix (actualCoefficients n e)) g = restrBd n e from restriction_hcAct n e g]
    rw [homologyMap_comp] at h
    exact h
  · intro hc
    have hfix : ∀ g : IntegralGL, homologyMap (hcAct bdryAct
        (GAct.ofRep principalSix (actualCoefficients n e)) g) 1
        (PDboundary (restrictedCoefficients n e) c) = PDboundary (restrictedCoefficients n e) c := by
      intro g
      have := BR.PDboundary_equivariant g (actualCoefficients n e) c
      rw [hc g] at this
      exact this.symm
    obtain ⟨ω, hω⟩ := fixed_mem_range_restriction n e _ hfix
    refine ⟨ω, ?_⟩
    apply PDboundary_injective n e
    rw [PDboundary_resToBoundary]
    exact hω

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
