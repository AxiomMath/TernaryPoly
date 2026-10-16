module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Coinvariants

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
# Level G: the descent projector is the average of the geometric action (G-3a, G-3b, G-3c)

Formalized by Claude Sonnet 5.5.

* G-3a: `boundaryProjector_eq_avg` (the library's projector `boundaryTransfer ≫ boundaryRestriction` on cover-boundary cohomology is the
  `G/Γ(6)`-average of `hcohAct`, read through `restrictedLocalIso`), from `descentProjector_eq_avg` (chain level, right cosets) and
  `descentProjector_homology_avg` (homology, left cosets, via `sum_rightCosets_eq` and `hcAct_of_mem`).
* G-3b: `H3boundaryG_eq_fixed` (`Fixed.lean: mem_H3boundaryG_iff`).
* G-3c: `Coinvariants.corG_boundaryToGroup_bAct` and `avG_eq_avgBd` (`Descent.avG` is the average of `bAct`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (n : ℕ) (e : ℤ)

/-- `Γ(6)` acts trivially on `Γ(6)`-equivariant cochains by the conjugation action. -/
theorem hcAct_of_mem (γ : IntegralGL) (hγ : γ ∈ principalSix) :
    hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) γ = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply rep_hom_ext'
  intro x
  change (conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) γ φ).hom x = φ.hom x
  refine (conjHom_apply _ _ γ φ x).trans ?_
  have h := Rep.hom_comm_apply φ ⟨γ, hγ⟩ ((bdryAct.act m).ρ γ⁻¹ x)
  change (actualCoefficients n e).ρ γ (φ.hom ((fullBoundaryChains.X m).ρ γ⁻¹ x)) = φ.hom x
  refine Eq.trans h.symm ?_
  change φ.hom ((fullBoundaryChains.X m).ρ γ ((fullBoundaryChains.X m).ρ γ⁻¹ x)) = φ.hom x
  congr 1
  exact LinearMap.congr_fun (show (fullBoundaryChains.X m).ρ γ * (fullBoundaryChains.X m).ρ γ⁻¹ = 1 by
    rw [← map_mul, mul_inv_cancel, map_one]) x

/-- The descent projector is the average of the conjugation actions over the right cosets (chain level). -/
theorem descentProjector_eq_avg :
    descentProjector principalSix fullBoundaryChains (actualCoefficients n e) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • ∑ r : RightCosets principalSix,
        hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹ := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  refine (descentProjector_f_apply n e m φ).trans ?_
  erw [HomologicalComplex.smul_f_apply, cochain_sum_f]
  erw [ModuleCat.hom_smul, ModuleCat.hom_sum]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

/-- **(G-3a, homology form)** The descent projector on `H¹(Hom_Γ(C_*(∂X̃), W))` is the average of the conjugation action
over the left cosets `G/Γ(6)`. -/
theorem descentProjector_homology_avg
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1) :
    (homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1).hom x =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • ∑ q : IntegralGL ⧸ principalSix,
        (hcohAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) q.out 1).hom x := by
  erw [descentProjector_eq_avg n e, homologyMap_smul', homologyMap_sum']
  simp only [ModuleCat.hom_smul, ModuleCat.hom_sum]
  change (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • (∑ r : RightCosets principalSix,
      (homologyMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹) 1).hom) x = _
  rw [LinearMap.sum_apply]
  congr 1
  have hT : ∀ a b : IntegralGL, b * a⁻¹ ∈ principalSix →
      (homologyMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) a⁻¹) 1).hom x =
      (homologyMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) b⁻¹) 1).hom x := by
    intro a b hab
    have hb : b⁻¹ = a⁻¹ * (b * a⁻¹)⁻¹ := by group
    rw [hb, hcAct_mul, hcAct_of_mem n e _ (Subgroup.inv_mem _ hab), Category.id_comp]
  have := sum_rightCosets_eq (fun a => (homologyMap (hcAct bdryAct
    (GAct.ofRep principalSix (actualCoefficients n e)) a⁻¹) 1).hom x) hT
  simp only [inv_inv] at this
  exact this

/-- **(G-3a)** The projector of the original library on cover-boundary cohomology is the average of the conjugation action over
`G/Γ(6)`, read through the identification `restrictedLocalIso` of the cover-boundary cochains with `Hom_Γ(C_*(∂X̃), W)`. -/
theorem boundaryProjector_eq_avg (x : (coverBoundaryCochains n e).homology 1) :
    (homologyMap (boundaryProjector n e) 1).hom x =
      (homologyMap (restrictedLocalIso n e).hom 1).hom
        ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹ • ∑ q : IntegralGL ⧸ principalSix,
          (hcohAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) q.out 1).hom
            ((homologyMap (restrictedLocalIso n e).inv 1).hom x)) := by
  have hproj : boundaryProjector n e = (restrictedLocalIso n e).inv ≫
      descentProjector principalSix fullBoundaryChains (actualCoefficients n e) ≫ (restrictedLocalIso n e).hom := rfl
  rw [hproj]
  change (homologyMap ((restrictedLocalIso n e).inv ≫ descentProjector principalSix fullBoundaryChains
    (actualCoefficients n e) ≫ (restrictedLocalIso n e).hom) 1).hom x = _
  rw [homologyMap_comp, homologyMap_comp]
  change (homologyMap (restrictedLocalIso n e).hom 1).hom ((homologyMap (descentProjector principalSix
    fullBoundaryChains (actualCoefficients n e)) 1).hom ((homologyMap (restrictedLocalIso n e).inv 1).hom x)) = _
  refine congrArg (homologyMap (restrictedLocalIso n e).hom 1).hom ?_
  rw [← natCard_rightCosets]
  exact descentProjector_homology_avg n e _

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary) in
/-- **(G-3c')** The descent map `avG` of `Descent.lean` is the average of the geometric action `bAct` over `G/Γ(6)`. -/
theorem avG_eq_avgBd (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    (avG n e c).1 = avgBd (actualCoefficients n e) c := by
  apply PDboundary_injective n e
  change PDboundary (restrictedCoefficients n e) (resToBoundary n e _) = _
  rw [PDboundary_resToBoundary]
  have hRHS : PDboundary (restrictedCoefficients n e) (avgBd (actualCoefficients n e) c) =
      (Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹ • ∑ q : IntegralGL ⧸ principalSix,
        (hcohAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) q.out 1).hom
          (PDboundary (restrictedCoefficients n e) c) := by
    unfold avgBd
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    change (PDboundary (restrictedCoefficients n e)).hom _ = _
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    exact BR.PDboundary_equivariant q.out (actualCoefficients n e) c
  rw [hRHS, ← natCard_rightCosets, ← descentProjector_homology_avg n e]
  change (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 ≫
    homologyMap (restrBd n e) 1) _ = _
  rw [← homologyMap_comp]
  rfl

/-- **(G-3b)** `H₃(∂X̄_G; 𝓜)` is, as a set, the space of `bAct`-invariant classes. -/
theorem H3boundaryG_eq_fixed :
    ((H3boundaryG n e : Submodule ℚ _) : Set ((SingularLocalHomology.boundaryLocalChains
        (restrictedCoefficients n e)).homology 3)) =
      {c | ∀ g : IntegralGL, homologyMap (bAct (actualCoefficients n e) g) 3 c = c} :=
  Set.ext fun c => mem_H3boundaryG_iff n e c

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
