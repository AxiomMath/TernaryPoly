module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelTower
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.AbsCoinv
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.CosetSumAbs

@[expose] public section


/-!
# Passage to a finite-index subgroup: coset-sum form of the `PD_∂` square and the restriction (transfer) direction

Formalized by Claude Sonnet 5.5.

`avgR_tower_sum`: for `N ≤ M ≤ Γ` and an `M`-invariant vector `v`, `avg_{Γ/N} v = [Γ:M]⁻¹ ∑_{r∈Γ/M} r·v`.  `PDQH_corQ_sum`: for
`Γ(6) ≤ H' ≤ H`, `PD_∂^H(cor q) = [H:H']⁻¹ ∑_{r∈H/H'} r · PD_∂^{H'} q`.

`resQ : H₃(∂X̄_H) → H₃(∂X̄_{H'})` is the restriction (transfer) `[H:H']·(H'-quotient ∘ H-average)`.  Squares: `corQ_resQ`
(`cor ∘ res = [H:H']`), `jQH_resQ` (`Cor_{H'}^H j^{H'}_*(res q) = [H:H'] j^H_* q`), `PDQH_resQ` (`PD^{H'}(res q) = [H:H'] PD^H q`),
`levelH_res_diagram` (`F^{H'}_{j^{H'}(res q)}(ℓ) = [H:H'] F^H_{j^H q}(ℓ)`).
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Tower2

variable {Γ : Type*} [Group Γ] (N M : Subgroup Γ) [N.Normal] [N.FiniteIndex] [M.FiniteIndex]
  {B : Type*} [AddCommGroup B] [Module ℚ B] (ρ : Representation ℚ Γ B)

omit [N.Normal] in
/-- **Coset-sum form of the average over `Γ/N` of an `M`-invariant vector**: `avg_{Γ/N} v = [Γ:M]⁻¹ ∑_{r∈Γ/M} r · v`. -/
theorem avgR_tower_sum (hNM : N ≤ M) (hN : ∀ n ∈ N, ρ n = 1) (v : B) (hv : ∀ m ∈ M, ρ m v = v) :
    avgR N ρ v = ((Fintype.card (Γ ⧸ M) : ℚ)⁻¹) • ∑ r : Γ ⧸ M, ρ r.out v := by
  have : (N.subgroupOf M).FiniteIndex := inferInstance
  have hcard : Fintype.card (Γ ⧸ N) = Fintype.card (Γ ⧸ M) * Fintype.card (↥M ⧸ N.subgroupOf M) := by
    have := card_quot_mul M N (N.subgroupOf M) (fun k => Subgroup.mem_subgroupOf) hNM
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have hG : (Fintype.card (Γ ⧸ M) : ℚ) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hH : (Fintype.card (↥M ⧸ N.subgroupOf M) : ℚ) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hsum : ∑ q : Γ ⧸ N, ρ q.out v =
      ∑ r : Γ ⧸ M, ∑ k' : ↥M ⧸ N.subgroupOf M, ρ (r.out * ((k'.out : ↥M) : Γ)) v := by
    rw [← Finset.sum_product']
    refine (Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNM).symm (fun q => ρ q.out v)).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨r, k'⟩ := p
    have he : (Subgroup.quotientEquivProdOfLE hNM).symm (r, k') =
        (QuotientGroup.mk (r.out * ((k'.out : ↥M) : Γ)) : Γ ⧸ N) := by
      conv_lhs => rw [← QuotientGroup.out_eq' k']
      rfl
    rw [he, rho_eq_of_mk_eq hN (QuotientGroup.out_eq' _)]
  have hterm : ∀ (r : Γ ⧸ M) (k' : ↥M ⧸ N.subgroupOf M), ρ (r.out * ((k'.out : ↥M) : Γ)) v = ρ r.out v := fun r k' => by
    rw [map_mul, Module.End.mul_apply, hv _ k'.out.2]
  unfold avgR
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [hsum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, ← Finset.smul_sum, smul_smul]
  rw [hcard]
  congr 1
  push_cast
  field_simp

end Tower2

section PD

variable {H' H : Subgroup IntegralGL} (V₀ : Rep.{0} ℚ IntegralGL)

/-- **The `PD_∂` square for the corestriction `H' ≤ H`, coset-sum form**: `PD_∂^H(cor q) = [H:H']⁻¹ ∑_{r∈H/H'} r · PD_∂^{H'} q`. -/
theorem PDQH_corQ_sum [(H'.subgroupOf H).FiniteIndex] (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H' V₀) :
    PDQH H (hH'.trans hle) V₀ (corQ V₀ hH' hle q) =
      ((Fintype.card (↥H ⧸ H'.subgroupOf H) : ℚ)⁻¹) • ∑ r : ↥H ⧸ H'.subgroupOf H,
        hcL V₀ r.out.1 (PDQH H' hH' V₀ q) := by
  rw [PDQH_corQ]
  have hNM : NH H ≤ H'.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hH' (Subgroup.mem_subgroupOf.mp hx))
  exact avgR_tower_sum (NH H) (H'.subgroupOf H) (repHc V₀ H) hNM (fun n hn => repHc_NH V₀ H ⟨n, hn⟩) _
    (fun m hm => PDQH_invariant H' hH' V₀ q ⟨m.1, Subgroup.mem_subgroupOf.mp hm⟩)

/-- The relative index `[H:H']` is finite when `Γ(6) ≤ H' ≤ H`. -/
theorem finiteIndex_subgroupOf_six (hH' : principalSix ≤ H') (_hle : H' ≤ H) : (H'.subgroupOf H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (fun _ hx => Subgroup.mem_subgroupOf.mpr (hH' (Subgroup.mem_subgroupOf.mp hx)) :
    NH H ≤ H'.subgroupOf H)

theorem qBdH_avgBdH (hH : principalSix ≤ H) (c : Bd V₀) :
    (qBdH H hH V₀).hom (avgBdH H V₀ c) = (qBdH H hH V₀).hom c := by
  have h : (qBdH H hH V₀).hom (avgBdH H V₀ c - c) = 0 := by
    rw [qBdH_ker, map_sub, avgBdH_comp V₀ (le_refl H), sub_self]
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- **The restriction (transfer) map `H₃(∂X̄_H) → H₃(∂X̄_{H'})`** for `Γ(6) ≤ H' ≤ H`: `[H:H']` times the quotient to the `H'`-coinvariants
of the `H`-average.  On rational coinvariants this is the transfer `[x]_H ↦ [∑_{r∈H'\H} r x]_{H'}` (an `H`-invariant `x` goes to
`[H:H']·[x]_{H'}`). -/
def resQ (hH' : principalSix ≤ H') (hle : H' ≤ H) : QbdH H V₀ →ₗ[ℚ] QbdH H' V₀ :=
  (H'.relIndex H : ℚ) • descendLin (qBdH H (hH'.trans hle) V₀).hom (qBdH_surjective H (hH'.trans hle) V₀)
    ((qBdH H' hH' V₀).hom ∘ₗ avgBdH H V₀) (fun c hc => by
      rw [LinearMap.comp_apply, (qBdH_ker H (hH'.trans hle) V₀ c).mp hc, map_zero])

theorem resQ_qBdH (hH' : principalSix ≤ H') (hle : H' ≤ H) (c : Bd V₀) :
    resQ V₀ hH' hle ((qBdH H (hH'.trans hle) V₀).hom c) =
      (H'.relIndex H : ℚ) • (qBdH H' hH' V₀).hom (avgBdH H V₀ c) := by
  unfold resQ
  rw [LinearMap.smul_apply, descendLin_apply]
  rfl

/-- `cor ∘ res = [H:H']`. -/
theorem corQ_resQ (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H V₀) :
    corQ V₀ hH' hle (resQ V₀ hH' hle q) = (H'.relIndex H : ℚ) • q := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H (hH'.trans hle) V₀ q
  rw [resQ_qBdH, map_smul, corQ_qBdH, qBdH_avgBdH]

/-- **The `j` square for restriction**: `Cor_{H'}^H j^{H'}_*(res q) = [H:H'] · j^H_* q`. -/
theorem jQH_resQ (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H V₀) :
    corHH V₀ hle (jQH H' hH' V₀ (resQ V₀ hH' hle q)) = (H'.relIndex H : ℚ) • jQH H (hH'.trans hle) V₀ q := by
  rw [← jQH_corQ, corQ_resQ, map_smul]

/-- **The `PD_∂` square for restriction**: `PD_∂^{H'}(res q) = [H:H'] · PD_∂^H q` (an `H`-invariant class is `H'`-invariant). -/
theorem PDQH_resQ (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H V₀) :
    PDQH H' hH' V₀ (resQ V₀ hH' hle q) = (H'.relIndex H : ℚ) • PDQH H (hH'.trans hle) V₀ q := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H (hH'.trans hle) V₀ q
  rw [resQ_qBdH, map_smul, PDQH_qBdH, PDQH_qBdH]
  unfold pd0
  rw [LinearMap.comp_apply, LinearMap.comp_apply, PD_avgBdH]
  congr 1
  refine avgR_of_invariant (fun h => ?_)
  have := PDQH_invariant H (hH'.trans hle) V₀ ((qBdH H (hH'.trans hle) V₀).hom c) ⟨h.1, hle h.2⟩
  rw [PDQH_qBdH] at this
  exact this


theorem relIndex_eq_card [(H'.subgroupOf H).FiniteIndex] :
    (H'.relIndex H : ℚ) = (Fintype.card (↥H ⧸ H'.subgroupOf H) : ℚ) := by
  rw [← Nat.card_eq_fintype_card]
  rfl

/-- **The evaluator square for restriction**: `F^{H'}_{j^{H'}_*(res q)}(ℓ) = [H:H'] · F^H_{j^H_* q}(ℓ)`. -/
theorem levelH_res_diagram (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H V₀) :
    ((thetaH H' hH' V₀ (capAll V₀) (jQH H' hH' V₀ (resQ V₀ hH' hle q))).val :
        OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V₀) OrdinaryTopBoundaryComparison.identityApartment =
      (H'.relIndex H : ℚ) • ((thetaH H (hH'.trans hle) V₀ (capAll V₀) (jQH H (hH'.trans hle) V₀ q)).val :
        OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V₀) OrdinaryTopBoundaryComparison.identityApartment := by
  rw [levelH_diagram_geom H' hH' V₀ (resQ V₀ hH' hle q), levelH_diagram_geom H (hH'.trans hle) V₀ q, PDQH_resQ,
    map_smul]

end PD

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
