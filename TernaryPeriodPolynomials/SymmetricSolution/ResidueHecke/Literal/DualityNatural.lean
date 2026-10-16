module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.DualityG
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.Assemble

@[expose] public section


/-!
# The `G`-level Borel-Serre duality for an arbitrary coefficient module, natural in the module

Formalized by Claude Sonnet 5.5.
Paper: Lemma 4.5 (`lem:residue-period`).

`DualityG.lean` constructs `H3_G_equiv n : H₃(GL₃(ℤ), ℛ_n ⊗ det⁻¹) ≃ Hom_G(St, ℛ_n ⊗ det⁻¹)` for the residue module.  Here the same
construction (`kEquivGeneric` at `N = Γ(6)`) is made for every `GL₃(ℤ)`-module `M` satisfying the cap reindexing compatibility
`CapEpsStatement` (all of them, by `DualityEquivariance.capEps`), and it is proved natural in `M`:
for `f : M ⟶ M'`, the functional of `H₃(f) x` is `f` composed with the functional of `x` (`H3GGen_natural`).  The ingredients are the
coefficient naturality of the neat duality (`TernaryPeriodPolynomials.Argument.CoefficientNaturality.groupOrdinaryIso_natural`) and the naturality of corestriction and
of the averaging operator.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Literal

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.AppendixBResidue

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- On the image of corestriction the generic duality is the averaged neat-level duality. -/
theorem kEquivGeneric_corN (M : Rep.{0} ℚ IntegralGL) (h : NeatDualityEquivariantGen principalSix
      (MulEquiv.refl ↥principalSix) stG M) (z : groupHomology (Rep.res principalSix.subtype M) 3) :
    ((kEquivGeneric (N := principalSix) (e := MulEquiv.refl ↥principalSix) (σ := stG) (M := M)
        (fun n => stG_principal n) h) (corN principalSix M 3 z)).val =
      avg stG M.ρ principalSix (psiGen principalSix (MulEquiv.refl ↥principalSix) M z) := by
  rw [← psiGen_avgN h]
  unfold kEquivGeneric
  simp only [LinearEquiv.trans_apply]
  have h1 : ∀ (e : (LinearMap.range (avgN principalSix M 3)) ≃ₗ[ℚ] groupHomology M 3)
      (he : ∀ w, e w = corN principalSix M 3 w.1),
      e.symm (corN principalSix M 3 z) = ⟨avgN principalSix M 3 z, z, rfl⟩ := by
    intro e he
    rw [LinearEquiv.symm_apply_eq, he]
    exact (corN_avgN_gen z).symm
  rw [h1 _ (fun _ => rfl)]
  rfl

/-- Corestriction is natural in the coefficient module. -/
theorem corN_natural {M M' : Rep.{0} ℚ IntegralGL} (f : M ⟶ M')
    (z : groupHomology (Rep.res principalSix.subtype M) 3) :
    corN principalSix M' 3
        ((groupHomology.map (MonoidHom.id principalSix) ((Rep.resFunctor principalSix.subtype).map f) 3).hom z) =
      (groupHomology.map (MonoidHom.id IntegralGL) f 3).hom (corN principalSix M 3 z) := by
  have h1 := groupHomology.map_comp (MonoidHom.id principalSix) principalSix.subtype
    ((Rep.resFunctor principalSix.subtype).map f) (𝟙 (Rep.res principalSix.subtype M')) 3
  have h2 := groupHomology.map_comp principalSix.subtype (MonoidHom.id IntegralGL)
    (𝟙 (Rep.res principalSix.subtype M)) f 3
  have h3 : groupHomology.map (principalSix.subtype.comp (MonoidHom.id principalSix))
      ((Rep.resFunctor principalSix.subtype).map f ≫ (Rep.resFunctor (MonoidHom.id principalSix)).map
        (𝟙 (Rep.res principalSix.subtype M'))) 3 =
      groupHomology.map ((MonoidHom.id IntegralGL).comp principalSix.subtype)
        (𝟙 (Rep.res principalSix.subtype M) ≫ (Rep.resFunctor principalSix.subtype).map f) 3 := by
    apply groupHomology.map_congr rfl
    rfl
  have h4 := congrArg (fun m => m.hom z) (h1.symm.trans (h3.trans h2))
  exact h4

/-- The neat-level duality (forgetting equivariance) is natural in the coefficient module. -/
theorem psiGen_natural {M M' : Rep.{0} ℚ IntegralGL} (f : M ⟶ M')
    (y : groupHomology (Rep.res principalSix.subtype M) 3) :
    psiGen principalSix (MulEquiv.refl ↥principalSix) M'
        ((groupHomology.map (MonoidHom.id principalSix) ((Rep.resFunctor principalSix.subtype).map f) 3).hom y) =
      f.hom.toLinearMap ∘ₗ psiGen principalSix (MulEquiv.refl ↥principalSix) M y := by
  have e1 := thetaGen_refl_apply M'
    ((groupHomology.map (MonoidHom.id principalSix) ((Rep.resFunctor principalSix.subtype).map f) 3).hom y)
  have e2 := thetaGen_refl_apply M y
  have e3 := TernaryPeriodPolynomials.Argument.CoefficientNaturality.groupOrdinaryIso_natural
    ((Rep.resFunctor principalSix.subtype).map f) y
  apply LinearMap.ext
  intro c
  change (((thetaGen principalSix (MulEquiv.refl ↥principalSix) M').hom.hom
      ((groupHomology.map (MonoidHom.id principalSix) ((Rep.resFunctor principalSix.subtype).map f) 3).hom y)).hom c) =
    f.hom (((thetaGen principalSix (MulEquiv.refl ↥principalSix) M).hom.hom y).hom c)
  rw [e1, e2, e3]
  rfl

/-- Averaging is natural in the coefficient module. -/
theorem avg_natural {M M' : Rep.{0} ℚ IntegralGL} (f : M ⟶ M')
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) :
    avg stG M'.ρ principalSix (f.hom.toLinearMap ∘ₗ Φ) = f.hom.toLinearMap ∘ₗ avg stG M.ρ principalSix Φ := by
  rw [avg_eq_sum, avg_eq_sum]
  ext z
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, actL_apply, TernaryPeriodPolynomials.Argument.GroupHomology.term, LinearMap.comp_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact (Rep.hom_comm_apply f _ _).symm

/-- **The `G`-level Borel-Serre duality** `H₃(GL₃(ℤ), M) ≃ Hom_G(St, M)` for any `GL₃(ℤ)`-module `M` satisfying the cap
reindexing compatibility (`CapEpsStatement`, true for every `M` by `DualityEquivariance.capEps`). -/
def H3GGen (M : Rep.{0} ℚ IntegralGL) (hM : ∀ k : IntegralGL, CapEpsStatement k M) :
    groupHomology M 3 ≃ₗ[ℚ] homKGen stG M :=
  kEquivGeneric (N := principalSix) (e := MulEquiv.refl ↥principalSix) (σ := stG) (M := M)
    (fun n => stG_principal n) (neatDualityEquivariantGen_of_capEps M hM)

/-- **Coefficient naturality of the `G`-level duality**: the functional of the pushforward `H₃(f) x` is `f` composed with the
functional of `x`. -/
theorem H3GGen_natural {M M' : Rep.{0} ℚ IntegralGL} (hM : ∀ k : IntegralGL, CapEpsStatement k M)
    (hM' : ∀ k : IntegralGL, CapEpsStatement k M') (f : M ⟶ M') (x : groupHomology M 3) :
    (H3GGen M' hM' ((groupHomology.map (MonoidHom.id IntegralGL) f 3).hom x)).val =
      f.hom.toLinearMap ∘ₗ (H3GGen M hM x).val := by
  obtain ⟨z, rfl⟩ := corN_surjective (N := principalSix) (A := M) (n := 3) (card_ne_zero_gen principalSix) x
  rw [← corN_natural f z]
  unfold H3GGen
  rw [kEquivGeneric_corN M' (neatDualityEquivariantGen_of_capEps M' hM'),
    kEquivGeneric_corN M (neatDualityEquivariantGen_of_capEps M hM), psiGen_natural, avg_natural]

end TernaryPeriodPolynomials.Argument.Lemma45Literal
