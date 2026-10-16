module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.TransferChain

@[expose] public section


/-!
# The chain-level coset-sum transfer equals `resQ` on `H₃(∂X̄_H; 𝓜)`

Formalized by Claude Sonnet 5.5.

`transfer_eq_resQ`: for `Γ(6) ≤ H' ≤ H` of finite index, the homology map in degree three of the literal chain-level transfer
`transferCx H H' (Ybd V₀)` (`[y]_H ↦ ∑_{r∈H'\H} [r y]_{H'}`) is `resQ V₀`, the restriction map of `Naturality.TowerRes` (defined there as `[H:H']`
times the quotient of the `H`-average).  The comparison uses `apply_avgR_sum` (`Φ ∘ avg_{H/Γ(6)} = [H:H']⁻¹ ∑_{H'\H} Φ ∘ ρ(r)` for the `H'`-invariant map
`Φ = qBdH H'`).
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open Representation

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section ResQ

variable {H' H : Subgroup IntegralGL} (V₀ : Rep.{0} ℚ IntegralGL) [(H'.subgroupOf H).FiniteIndex]
  (hH' : principalSix ≤ H') (hle : H' ≤ H)

theorem sum_f_hom {C D : ChainComplex (ModuleCat.{0} ℚ) ℕ} {ι : Type*} (s : Finset ι) (f : ι → (C ⟶ D)) (i : ℕ) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i :=
  Functor.map_sum (HomologicalComplex.eval _ _ i) f s

theorem GY_ibdC_assoc (g : IntegralGL) {W : ChainComplex (ModuleCat.{0} ℚ) ℕ} (X : CxN principalSix (Ybd V₀) ⟶ W) :
    (ibdC V₀).hom ≫ GY principalSix (Ybd V₀) g ≫ X = bAct V₀ g ≫ (ibdC V₀).hom ≫ X := by
  rw [bAct_eq, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

/-- The comparison chain map `Γ(6)`-in-`H` coinvariants `→` `(H')`-coinvariants given by the action of `g`. -/
def trR (g : IntegralGL) : CxN (NH H) (YH H V₀) ⟶ CxK (YH H' V₀) :=
  (trCx H V₀ (hH'.trans hle)).hom ≫ GY principalSix (Ybd V₀) g ≫ (trCx H' V₀ hH').inv ≫ QY (NH H') (YH H' V₀)

omit [(H'.subgroupOf H).FiniteIndex] in
theorem trR_ibd (g : IntegralGL) :
    (ibdH H (hH'.trans hle) V₀).hom ≫ trR V₀ hH' hle g =
      bAct V₀ g ≫ (ibdH H' hH' V₀).hom ≫ QY (NH H') (YH H' V₀) := by
  unfold trR
  rw [ibdH_hom, ibdH_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact GY_ibdC_assoc V₀ g _

theorem QY_transfer :
    QY (NH H) (YH H V₀) ≫ transferCx H H' (Ybd V₀) =
      ∑ r : RCos (H'.subgroupOf H), trR V₀ hH' hle (r.out : ↥H).1 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  apply LinearMap.ext
  intro v
  rw [HomologicalComplex.comp_f, sum_f_hom]
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum]
  refine Eq.trans (transferCx_mk H H' (Ybd V₀) n v) ?_
  refine Eq.trans ?_ (LinearMap.sum_apply _ _ _).symm
  refine Finset.sum_congr rfl fun r _ => ?_
  rfl

theorem transfer_apply_qBdH (c : Bd V₀) :
    (homologyMap (transferCx H H' (Ybd V₀)) 3).hom ((qBdH H (hH'.trans hle) V₀).hom c) =
      ∑ r : RCos (H'.subgroupOf H), (qBdH H' hH' V₀).hom (repBd V₀ H (r.out : ↥H) c) := by
  have h1 : homologyMap (QY (NH H) (YH H V₀)) 3 ≫ homologyMap (transferCx H H' (Ybd V₀)) 3 =
      ∑ r : RCos (H'.subgroupOf H), homologyMap (trR V₀ hH' hle (r.out : ↥H).1) 3 := by
    rw [← homologyMap_comp, QY_transfer V₀ hH' hle, homologyMap_sum']
  have h1' : (homologyMap (transferCx H H' (Ybd V₀)) 3).hom ∘ₗ (homologyMap (QY (NH H) (YH H V₀)) 3).hom =
      ∑ r : RCos (H'.subgroupOf H), (homologyMap (trR V₀ hH' hle (r.out : ↥H).1) 3).hom := by
    have := congrArg ModuleCat.Hom.hom h1
    rw [ModuleCat.hom_comp, ModuleCat.hom_sum] at this
    exact this
  have h2 := LinearMap.congr_fun h1' ((jBdH H (hH'.trans hle) V₀).hom c)
  rw [LinearMap.sum_apply] at h2
  refine h2.trans (Finset.sum_congr rfl fun r _ => ?_)
  have h3 := congrArg (fun f => homologyMap f 3) (trR_ibd V₀ hH' hle (r.out : ↥H).1)
  simp only [homologyMap_comp] at h3
  have h4 := ConcreteCategory.congr_hom h3 c
  exact h4

/-- **The literal chain-level coset-sum transfer is `resQ`**: for `Γ(6) ≤ H' ≤ H` the homology map of
`transferCx H H' (Ybd V₀)` in degree three is the restriction `resQ` (`[H:H']` times the quotient of the `H`-average). -/
theorem transfer_eq_resQ :
    (homologyMap (transferCx H H' (Ybd V₀)) 3).hom = resQ V₀ hH' hle := by
  apply LinearMap.ext
  intro q
  obtain ⟨c, rfl⟩ := qBdH_surjective H (hH'.trans hle) V₀ q
  rw [resQ_qBdH, transfer_apply_qBdH V₀ hH' hle]
  have hNS : NH H ≤ H'.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hH' (Subgroup.mem_subgroupOf.mp hx))
  have h := apply_avgR_sum (NH H) (H'.subgroupOf H) (repBd V₀ H) hNS (fun n hn => repBd_NH V₀ H ⟨n, hn⟩)
    (qBdH H' hH' V₀).hom (fun s hs b => qBdH_bAct H' hH' V₀ ⟨s.1, Subgroup.mem_subgroupOf.mp hs⟩ b) c
  rw [relIndex_eq_card]
  have hc : (Fintype.card (↥H ⧸ H'.subgroupOf H) : ℚ) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  rw [avgBdH_eq]
  rw [h, smul_smul, mul_inv_cancel₀ hc, one_smul]

end ResQ

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
