module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.BoundaryFrobenius
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.AvgTower
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.DualityG

@[expose] public section


/-!
# Passage to an intermediate finite-index subgroup (Lemma 3.3)

Formalized by Claude Sonnet 5.5.

For any subgroup `H` with `Γ(6) ≤ H ≤ G = GL₃(ℤ)` and any `G`-module `M`, `thetaH` is the Borel-Serre duality
`H₃(H, Res_H M) ≃ Hom_H(St, Res_H M)` (the generic `kEquivGeneric` at `N = Γ(6)`-in-`H`; its `H`-equivariance `neatDualityH` is
deduced from the `G`-level equivariance by the conjugation compatibility `liftN_cAct`).  `thetaH_corN`: on a corestriction it is the
`H/Γ(6)`-average of the neat-level functional.  `corH_corN`: transitivity of corestriction.  `thetaG_corH`: the `G`-level duality of
`Cor_H^G Cor_{Γ(6)}^H y` is the `G/Γ(6)`-average of the same neat-level functional.  `thetaG_corH_mackey`: for every class `u` of
`H₃(H, Res_H M)`, `Θ^G (Cor_H^G u) = [G:H]⁻¹ ∑_{r∈G/H} r · Θ^H(u) · r⁻¹` (Mackey formula; `AvgTower.avg_tower` factors the
average over `G/Γ(6)` through `G/H` and `H/Γ(6)`).  `thetaH_eq_thetaG`: when the neat-level functional is `G`-equivariant the two dualities
give the same functional, so the evaluator `F_z(ℓ)` is unchanged by the passage.  `levelH_diagram`: the diagram
`eq:apartment-boundary-diagram` descends to every such `H`: the `G`-level top class of `ω` is the corestriction of an `H`-level top class
with the same functional and the same boundary pairing.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryCovectors TernaryPoly.OrdinaryBoundaryCommonRoot
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.OrdinaryApartmentPresentation
  TernaryPoly.OrdinaryBoundaryActualEvaluation
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.AppendixBResidue

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Intermediate

variable (H : Subgroup IntegralGL) (hH : principalSix ≤ H) (M : Rep.{0} ℚ IntegralGL)

/-- `Γ(6)` inside the intermediate subgroup `H`. -/
abbrev NH : Subgroup ↥H := principalSix.subgroupOf H

instance : (NH H).Normal := Subgroup.normal_subgroupOf

instance : (NH H).FiniteIndex := inferInstance

/-- The identification of `Γ(6)`-in-`H` with `Γ(6)`. -/
def eH : NH H ≃* ↥principalSix := Subgroup.subgroupOfEquivOfLe hH

/-- The action of `H` on the Steinberg module. -/
abbrev stH : Representation ℚ ↥H OrdinaryIncidenceChains.Cycles := stG.comp H.subtype

/-- `M` restricted to `H`. -/
abbrev MH : Rep.{0} ℚ ↥H := Rep.res H.subtype M

theorem stH_principal (n : NH H) : stH H n = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (eH H hH n) :=
  stG_principal (eH H hH n)

/-- Transport of neat-level homology from `Γ(6)`-in-`H` to `Γ(6)`. -/
def liftN : groupHomology (Rep.res (NH H).subtype (MH H M)) 3 ≅ groupHomology (Rep.res principalSix.subtype M) 3 :=
  groupHomology.mapIso (eH H hH) (LinearEquiv.refl ℚ M) (fun _ => rfl) 3

theorem liftN_cAct (g : ↥H) (x : groupHomology (Rep.res (NH H).subtype (MH H M)) 3) :
    (liftN H hH M).hom.hom (cAct (NH H) (MH H M) 3 g x) =
      cAct principalSix M 3 g.1 ((liftN H hH M).hom.hom x) := by
  have h : groupHomology.map (conjN (NH H) g) (conjRep (NH H) (MH H M) g) 3 ≫ (liftN H hH M).hom =
      (liftN H hH M).hom ≫ groupHomology.map (conjN principalSix g.1) (conjRep principalSix M g.1) 3 := by
    unfold liftN
    erw [← groupHomology.map_comp, ← groupHomology.map_comp]
    refine groupHomology.map_congr ?_ ?_ 3
    · ext y
      rfl
    · ext y
      rfl
  exact congrArg (fun f => f.hom x) h

theorem psiGen_H (x : groupHomology (Rep.res (NH H).subtype (MH H M)) 3) :
    psiGen (NH H) (eH H hH) (MH H M) x =
      psiGen principalSix (MulEquiv.refl principalSix) M ((liftN H hH M).hom.hom x) := by
  apply LinearMap.ext
  intro σ
  have e1 := thetaGen_refl_apply M ((liftN H hH M).hom.hom x)
  change (((thetaGen (NH H) (eH H hH) (MH H M)).hom.hom x).hom σ) =
    (((thetaGen principalSix (MulEquiv.refl principalSix) M).hom.hom ((liftN H hH M).hom.hom x)).hom σ)
  rw [e1]
  rfl

theorem neatDualityH (hM : ∀ k : IntegralGL, CapEpsStatement k M) :
    NeatDualityEquivariantGen (NH H) (eH H hH) (stH H) (MH H M) := by
  intro g x
  have hG := neatDualityEquivariantGen_of_capEps M hM g.1 ((liftN H hH M).hom.hom x)
  rw [psiGen_H H hH M, psiGen_H H hH M, liftN_cAct]
  exact hG

/-- **The duality `Θ^H` for an intermediate subgroup** `Γ(6) ≤ H ≤ G`: `H₃(H, Res_H M) ≃ Hom_H(St, Res_H M)`. -/
def thetaH (hM : ∀ k : IntegralGL, CapEpsStatement k M) :
    groupHomology (MH H M) 3 ≃ₗ[ℚ] homKGen (stH H) (MH H M) :=
  kEquivGeneric (N := NH H) (e := eH H hH) (σ := stH H) (M := MH H M) (stH_principal H hH) (neatDualityH H hH M hM)

/-- On the image of corestriction `Θ^H` is the `H/Γ(6)`-average of the neat-level functional. -/
theorem thetaH_corN (hM : ∀ k : IntegralGL, CapEpsStatement k M)
    (y : groupHomology (Rep.res (NH H).subtype (MH H M)) 3) :
    ((thetaH H hH M hM (corN (NH H) (MH H M) 3 y)).val) =
      avg (stH H) (MH H M).ρ (NH H) (psiGen (NH H) (eH H hH) (MH H M) y) := by
  have h := neatDualityH H hH M hM
  rw [← psiGen_avgN h]
  unfold thetaH kEquivGeneric
  simp only [LinearEquiv.trans_apply]
  have h1 : ∀ (e : (LinearMap.range (avgN (NH H) (MH H M) 3)) ≃ₗ[ℚ] groupHomology (MH H M) 3)
      (he : ∀ w, e w = corN (NH H) (MH H M) 3 w.1),
      e.symm (corN (NH H) (MH H M) 3 y) = ⟨avgN (NH H) (MH H M) 3 y, y, rfl⟩ := by
    intro e he
    rw [LinearEquiv.symm_apply_eq, he]
    exact (corN_avgN_gen y).symm
  rw [h1 _ (fun _ => rfl)]
  rfl

/-- The corestriction `Cor_H^G : H₃(H, Res_H M) → H₃(G, M)`. -/
abbrev corH : groupHomology (MH H M) 3 →ₗ[ℚ] groupHomology M 3 :=
  (groupHomology.map H.subtype (𝟙 (MH H M)) 3).hom

/-- Transitivity of corestriction: `Cor_H^G ∘ Cor_{Γ(6)}^H = Cor_{Γ(6)}^G`, up to the identification `liftN`. -/
theorem corH_corN (y : groupHomology (Rep.res (NH H).subtype (MH H M)) 3) :
    corH H M (corN (NH H) (MH H M) 3 y) = corN principalSix M 3 ((liftN H hH M).hom.hom y) := by
  have h : (liftN H hH M).hom ≫ groupHomology.map principalSix.subtype (𝟙 (Rep.res principalSix.subtype M)) 3 =
      groupHomology.map (NH H).subtype (𝟙 (Rep.res (NH H).subtype (MH H M))) 3 ≫
        groupHomology.map H.subtype (𝟙 (MH H M)) 3 := by
    unfold liftN
    erw [← groupHomology.map_comp, ← groupHomology.map_comp]
    refine groupHomology.map_congr ?_ ?_ 3
    · ext y
      rfl
    · ext y
      rfl
  exact (congrArg (fun f => f.hom y) h).symm

/-- **`Θ^G ∘ Cor_H^G` on a class coming from the neat level, in general**: the `G/Γ(6)`-average of the neat-level functional. -/
theorem thetaG_corH (hM : ∀ k : IntegralGL, CapEpsStatement k M)
    (y : groupHomology (Rep.res (NH H).subtype (MH H M)) 3) :
    ((thetaG M (corH H M (corN (NH H) (MH H M) 3 y)) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M)) =
      avg stG M.ρ principalSix (psiGen (NH H) (eH H hH) (MH H M) y) := by
  rw [corH_corN H hH M, thetaG_corN, psiGen_avgN (neatDualityEquivariantGen_of_capEps M hM), psiGen_H H hH M]

/-- **Passage to a finite-index subgroup** `Γ(6) ≤ H ≤ G`: if the neat-level functional of `y` is `G`-equivariant, then the
`H`-level duality of `Cor_{Γ(6)}^H y` and the `G`-level duality of `Cor_H^G Cor_{Γ(6)}^H y` are the same functional. -/
theorem thetaH_eq_thetaG (hM : ∀ k : IntegralGL, CapEpsStatement k M)
    (y : groupHomology (Rep.res (NH H).subtype (MH H M)) 3)
    (hy : IsEquivOn stG M.ρ ⊤ (psiGen principalSix (MulEquiv.refl principalSix) M ((liftN H hH M).hom.hom y))) :
    ((thetaH H hH M hM (corN (NH H) (MH H M) 3 y)).val) =
      ((thetaG M (corH H M (corN (NH H) (MH H M) 3 y)) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M)) := by
  rw [thetaH_corN, thetaG_corH H hH M hM, psiGen_H H hH M]
  have hHm : (Nat.card (↥H ⧸ NH H) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hGm : (Nat.card (IntegralGL ⧸ principalSix) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  rw [avg_of_isEquiv_natCard (N := NH H) (σ := stH H) (ρ := (MH H M).ρ) (fun h _ z => hy h.1 trivial z) hHm,
    avg_of_isEquiv_natCard (N := principalSix) hy hGm]

/-- **Lemma 3.3 for an intermediate finite-index subgroup `Γ(6) ≤ H ≤ G`** (the clause "compatible with passage to a finite-index
subgroup").  Every level-`G` boundary class `ω ∈ H¹(∂X̄_G; M)` has an `H`-level top class
`z_H = Cor_{Γ(6)}^H (j_* PD⁻¹ res ω) ∈ H₃(H, Res_H M)` such that (i) `Cor_H^G z_H = j^G_* PD⁻¹ ω` (the `G`-level class is the
corestriction of the `H`-level class), (ii) the `H`-level and `G`-level Steinberg functionals coincide, `Θ^H z_H = Θ^G (Cor_H^G z_H)`,
and (iii) the `H`-level identity-apartment value is the boundary pairing, `F^H_{z_H}(ℓ) = ⟨ω, ∂a⟩`. -/
theorem levelH_diagram (n : ℕ) (e : ℤ) (ω : (fullBoundaryCochains n e).homology 1) :
    ∃ zH : groupHomology (MH H (actualCoefficients n e)) 3,
      corH H (actualCoefficients n e) zH = fullBoundaryClassToG n e ω ∧
      (thetaH H hH (actualCoefficients n e)
          (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (actualCoefficients n e)) zH).val =
        (thetaG (actualCoefficients n e) (fullBoundaryClassToG n e ω) :
          OrdinaryIncidenceChains.Cycles →ₗ[ℚ] actualCoefficients n e) ∧
      (thetaH H hH (actualCoefficients n e)
          (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (actualCoefficients n e)) zH).val
          identityApartment = fullBoundaryPairing n e ω := by
  set M := actualCoefficients n e with hMdef
  set y' := fullBoundaryClassToGroup n e ω with hy'
  let y : groupHomology (Rep.res (NH H).subtype (MH H M)) 3 := (liftN H hH M).inv.hom y'
  have hly : (liftN H hH M).hom.hom y = y' := by
    change ((liftN H hH M).inv ≫ (liftN H hH M).hom).hom y' = y'
    rw [Iso.inv_hom_id]; rfl
  have hcor : corH H M (corN (NH H) (MH H M) 3 y) = fullBoundaryClassToG n e ω := by
    rw [corH_corN H hH M, hly]
    rfl
  have heq : IsEquivOn stG M.ρ ⊤ (psiGen principalSix (MulEquiv.refl principalSix) M
      ((liftN H hH M).hom.hom y)) := by
    rw [hly]; exact fullClass_isEquivOn n e ω
  have hfun := thetaH_eq_thetaG H hH M
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k M) y heq
  refine ⟨corN (NH H) (MH H M) 3 y, hcor, ?_, ?_⟩
  · rw [hfun, hcor]
  · rw [hfun, hcor]
    have := levelG_diagram n e ω
    rw [topEvaluationG_apply] at this
    exact this

theorem psiGen_equivOn_N6 (y : groupHomology (Rep.res (NH H).subtype (MH H M)) 3) :
    IsEquivOn stG M.ρ principalSix (psiGen (NH H) (eH H hH) (MH H M) y) := by
  rw [psiGen_H H hH M]
  exact toLinG_isEquivOn principalSix (MulEquiv.refl ↥principalSix) stG M (fun n => stG_principal n) _

/-- **Mackey formula for the passage to an intermediate subgroup** (arbitrary classes): for every `u ∈ H₃(H, Res_H M)`,
`Θ^G (Cor_H^G u) = [G:H]⁻¹ ∑_{r ∈ G/H} r · Θ^H(u) · r⁻¹`, the transfer-average of the `H`-level functional. -/
theorem thetaG_corH_mackey [H.FiniteIndex] (hM : ∀ k : IntegralGL, CapEpsStatement k M) (u : groupHomology (MH H M) 3) :
    ((thetaG M (corH H M u) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M)) =
      ((Nat.card (IntegralGL ⧸ H) : ℚ)⁻¹) •
        ∑ r : IntegralGL ⧸ H, GroupHomology.actL stG M.ρ r.out (thetaH H hH M hM u).val := by
  obtain ⟨y, rfl⟩ := corN_surjective (A := MH H M) (n := 3) (card_ne_zero_gen (NH H)) u
  rw [thetaG_corH H hH M hM, thetaH_corN H hH M hM]
  rw [avg_tower stG M.ρ principalSix H hH (psiGen_equivOn_N6 H hH M y), Nat.card_eq_fintype_card]

end Intermediate

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
