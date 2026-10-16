module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelMaps

@[expose] public section


/-!
# Passage to a finite-index subgroup: the tower `Γ(6) ≤ H' ≤ H` of equivariant quotients

Formalized by Claude Sonnet 5.5.

`corQ : H₃(∂X̄_{H'}) → H₃(∂X̄_H)` is induced by the identity of the neat-level boundary homology (`corQ_qBdH`, so the composite square
`B_{Γ(6)} → B_{H'} → B_H = B_{Γ(6)} → B_H` commutes by construction).  `jQH_corQ`: `j^H_* ∘ corQ = Cor_{H'}^H ∘ j^{H'}_*`
(`corNH_eq_map`: `Cor_{Γ(6)}^H` is `groupHomology.map` of the inclusion; `corHH_corNH'`: transitivity).  `PDQH_corQ`:
`PD_∂^H ∘ corQ = avg_{H/Γ(6)} ∘ PD_∂^{H'}` (the `H'`-invariant dual class is averaged to an `H`-invariant one; `avgHc_comp`).
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open Representation
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Tower

variable {H' H : Subgroup IntegralGL} (V₀ : Rep.{0} ℚ IntegralGL)

theorem avgBdH_bdL (h : ↥H) (c : Bd V₀) : avgBdH H V₀ (bdL V₀ h.1 c) = avgBdH H V₀ c :=
  LinearMap.congr_fun (rho_right (fun n hn => repBd_NH V₀ H ⟨n, hn⟩) h) c

theorem avgBdH_apply (c : Bd V₀) :
    avgBdH H V₀ c = ((Fintype.card (↥H ⧸ NH H) : ℚ)⁻¹) • ∑ x : ↥H ⧸ NH H, bdL V₀ x.out.1 c := by
  unfold avgBdH
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

theorem avgBdH_comp (hle : H' ≤ H) (c : Bd V₀) : avgBdH H V₀ (avgBdH H' V₀ c) = avgBdH H V₀ c := by
  rw [avgBdH_apply (H := H') V₀ c]
  simp only [map_smul, map_sum]
  have : ∀ x : ↥H' ⧸ NH H', avgBdH H V₀ (bdL V₀ x.out.1 c) = avgBdH H V₀ c :=
    fun x => avgBdH_bdL V₀ ⟨x.out.1, hle x.out.2⟩ c
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (card_ne_zero_NH H'), one_smul]

/-- The map `Cor_{Γ(6)}^H` as `groupHomology.map` of the inclusion `Γ(6) ↪ H`. -/
def corNH' (hH : principalSix ≤ H) : groupHomology (Rep.res principalSix.subtype V₀) 3 →ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  (groupHomology.map (Subgroup.inclusion hH) (𝟙 (Rep.res principalSix.subtype V₀)) 3).hom

theorem corNH_eq_map (hH : principalSix ≤ H) : corNH H hH V₀ = corNH' V₀ hH := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (liftN H hH V₀).hom).2 x
  have h1 : (liftN H hH V₀).inv.hom ((liftN H hH V₀).hom.hom y) = y := by
    change ((liftN H hH V₀).hom ≫ (liftN H hH V₀).inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have h : (liftN H hH V₀).hom ≫ groupHomology.map (Subgroup.inclusion hH) (𝟙 (Rep.res principalSix.subtype V₀)) 3 =
      groupHomology.map (NH H).subtype (𝟙 (Rep.res (NH H).subtype (MH H V₀))) 3 := by
    unfold liftN
    erw [← groupHomology.map_comp]
    refine groupHomology.map_congr ?_ ?_ 3
    · ext y
      rfl
    · ext y
      rfl
  change corN (NH H) (MH H V₀) 3 ((liftN H hH V₀).inv.hom ((liftN H hH V₀).hom.hom y)) = _
  rw [h1]
  exact (congrArg (fun f => f.hom y) h).symm

/-- Corestriction `Cor_{H'}^H : H₃(H', Res V₀) → H₃(H, Res V₀)`. -/
def corHH (hle : H' ≤ H) : groupHomology (MH H' V₀) 3 →ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  (groupHomology.map (Subgroup.inclusion hle) (𝟙 (MH H' V₀)) 3).hom

theorem corHH_corNH' (hH' : principalSix ≤ H') (hle : H' ≤ H) (x : groupHomology (Rep.res principalSix.subtype V₀) 3) :
    corHH V₀ hle (corNH' V₀ hH' x) = corNH' V₀ (hH'.trans hle) x := by
  have h : groupHomology.map (A := Rep.res principalSix.subtype V₀) (B := MH H' V₀)
        (Subgroup.inclusion hH') (𝟙 (Rep.res principalSix.subtype V₀)) 3 ≫
        groupHomology.map (A := MH H' V₀) (B := MH H V₀) (Subgroup.inclusion hle) (𝟙 (MH H' V₀)) 3 =
      groupHomology.map (A := Rep.res principalSix.subtype V₀) (B := MH H V₀)
        (Subgroup.inclusion (hH'.trans hle)) (𝟙 (Rep.res principalSix.subtype V₀)) 3 := by
    erw [← groupHomology.map_comp]
    refine groupHomology.map_congr ?_ ?_ 3
    · ext y
      rfl
    · ext y
      rfl
  exact congrArg (fun f => f.hom x) h

theorem avgR_apply'' {Γ : Type} [Group Γ] (N : Subgroup Γ) [N.Normal] [N.FiniteIndex] {B : Type}
    [AddCommGroup B] [Module ℚ B] (ρ : Representation ℚ Γ B) (v : B) :
    avgR N ρ v = ((Fintype.card (Γ ⧸ N) : ℚ)⁻¹) • ∑ q : Γ ⧸ N, ρ q.out v := by
  unfold avgR
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]

theorem avgHc_comp (hle : H' ≤ H) (ω : Hc V₀) :
    avgR (NH H) (repHc V₀ H) (avgR (NH H') (repHc V₀ H') ω) = avgR (NH H) (repHc V₀ H) ω := by
  have hr : ∀ h' : ↥H', avgR (NH H) (repHc V₀ H) (repHc V₀ H' h' ω) = avgR (NH H) (repHc V₀ H) ω := fun h' =>
    LinearMap.congr_fun (rho_right (fun n hn => repHc_NH V₀ H ⟨n, hn⟩) (⟨h'.1, hle h'.2⟩ : ↥H)) ω
  rw [avgR_apply'' (NH H') (repHc V₀ H') ω]
  simp only [map_smul, map_sum]
  have : ∀ x : ↥H' ⧸ NH H', avgR (NH H) (repHc V₀ H) (repHc V₀ H' x.out ω) = avgR (NH H) (repHc V₀ H) ω :=
    fun x => hr x.out
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (card_ne_zero_NH H'), one_smul]

/-- The corestriction map between the equivariant quotients `H₃(∂X̄_{H'}) → H₃(∂X̄_H)` (`H' ≤ H`), induced by the identity of
the neat-level boundary homology. -/
def corQ (hH' : principalSix ≤ H') (hle : H' ≤ H) : QbdH H' V₀ →ₗ[ℚ] QbdH H V₀ :=
  descendLin (qBdH H' hH' V₀).hom (qBdH_surjective H' hH' V₀) (qBdH H (hH'.trans hle) V₀).hom (fun c hc => by
    rw [(qBdH_ker H (hH'.trans hle) V₀ c).mpr (by
      rw [← avgBdH_comp V₀ hle c, (qBdH_ker H' hH' V₀ c).mp hc, map_zero])])

theorem corQ_qBdH (hH' : principalSix ≤ H') (hle : H' ≤ H) (c : Bd V₀) :
    corQ V₀ hH' hle ((qBdH H' hH' V₀).hom c) = (qBdH H (hH'.trans hle) V₀).hom c :=
  descendLin_apply _ _ _ _ c

/-- **The square `j^H_* ∘ cor = Cor_{H'}^H ∘ j^{H'}_*`** (no scalar). -/
theorem jQH_corQ (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H' V₀) :
    jQH H (hH'.trans hle) V₀ (corQ V₀ hH' hle q) = corHH V₀ hle (jQH H' hH' V₀ q) := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H' hH' V₀ q
  rw [corQ_qBdH, jQH_qBdH, jQH_qBdH]
  unfold jH0
  rw [LinearMap.comp_apply, LinearMap.comp_apply, corNH_eq_map, corNH_eq_map, corHH_corNH' V₀ hH' hle]

/-- **The square for `PD_∂`**: going up from `H'` to `H` averages the `H'`-invariant dual class over `H/Γ(6)`. -/
theorem PDQH_corQ (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H' V₀) :
    PDQH H (hH'.trans hle) V₀ (corQ V₀ hH' hle q) = avgR (NH H) (repHc V₀ H) (PDQH H' hH' V₀ q) := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H' hH' V₀ q
  rw [corQ_qBdH, PDQH_qBdH, PDQH_qBdH]
  unfold pd0
  rw [LinearMap.comp_apply, LinearMap.comp_apply, avgHc_comp V₀ hle]

end Tower

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
