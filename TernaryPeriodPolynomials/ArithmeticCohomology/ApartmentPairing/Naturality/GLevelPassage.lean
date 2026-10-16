module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KPDSquare
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelTower
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.FiniteIndex

@[expose] public section


/-!
# Passage from an intermediate level `H` to level `G`: the equivariant quotients, `j` and `PD_∂`

Formalized by Claude Sonnet 5.5.

`corQG : H₃((𝓜 ⊗ Sing ∂X̃)_H) → H₃((𝓜 ⊗ Sing ∂X̃)_G)` is induced by the identity of the neat-level boundary homology, so
`B_{Γ(6)} → B_H → B_G` equals `B_{Γ(6)} → B_G` by construction (`corQG_qBdH`) and the composite with `corQ` is `corQG` (`corQG_corQ`).
`jQ_corQG`: `j^G_* ∘ corQG = Cor_H^G ∘ j^H_*` (no scalar).  `PDQ_corQG`: the neat-level restriction of `PD_∂^G (corQG q)` is the
`G/Γ(6)`-average `[G:Γ(6)]⁻¹ ∑_x x · PD_∂^H q` of the `H`-invariant class `PD_∂^H q`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.PolynomialGLAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section G

variable {H : Subgroup IntegralGL} (V₀ : Rep.{0} ℚ IntegralGL)

theorem avgBd_avgBdH (c : Bd V₀) : avgBd V₀ (avgBdH H V₀ c) = avgBd V₀ c := by
  rw [avgBdH_apply]
  simp only [map_smul, map_sum, avgBd_bdL, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (card_ne_zero_NH H), one_smul]

/-- **Passage from the `H`-level quotient to the `G`-level one**: `H₃((𝓜 ⊗ Sing ∂X̃)_H) → H₃((𝓜 ⊗ Sing ∂X̃)_G)`, induced by the identity of the
neat-level boundary homology (the composite `B_{Γ(6)} → B_H → B_G` is `B_{Γ(6)} → B_G` by construction, `corQG_qBdH`). -/
def corQG (hH : principalSix ≤ H) : QbdH H V₀ →ₗ[ℚ] Qbd V₀ :=
  descendLin (qBdH H hH V₀).hom (qBdH_surjective H hH V₀) (qBd V₀).hom (fun c hc => by
    rw [qBd_ker, ← avgBd_avgBdH (H := H) V₀ c, (qBdH_ker H hH V₀ c).mp hc, map_zero])

theorem corQG_qBdH (hH : principalSix ≤ H) (c : Bd V₀) :
    corQG V₀ hH ((qBdH H hH V₀).hom c) = (qBd V₀).hom c :=
  descendLin_apply _ _ _ _ c

/-- The composite `B_{H'} → B_H → B_G` is `B_{H'} → B_G` (for `Γ(6) ≤ H' ≤ H`). -/
theorem corQG_corQ {H' : Subgroup IntegralGL} (hH' : principalSix ≤ H') (hle : H' ≤ H) (q : QbdH H' V₀) :
    corQG V₀ (hH'.trans hle) (corQ V₀ hH' hle q) = corQG V₀ hH' q := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H' hH' V₀ q
  rw [corQ_qBdH, corQG_qBdH, corQG_qBdH]

theorem corH_jH0 (hH : principalSix ≤ H) (c : Bd V₀) :
    corH H V₀ (jH0 H hH V₀ c) =
      corN principalSix V₀ 3 ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c) := by
  unfold jH0 corNH
  rw [LinearMap.comp_apply, LinearMap.comp_apply, corH_corN H hH V₀]
  set x := (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c with hx
  have hy : (liftN H hH V₀).hom.hom ((liftN H hH V₀).inv.hom x) = x := by
    change ((liftN H hH V₀).inv ≫ (liftN H hH V₀).hom).hom x = x
    rw [Iso.inv_hom_id]; rfl
  rw [hy]

/-- **The `j` square from `H` to `G`** for the actual coefficients `M_{n,e}`: `j^G_* ∘ (B_H → B_G) = Cor_H^G ∘ j^H_*` (no scalar). -/
theorem jQ_corQG (n : ℕ) (e : ℤ) (hH : principalSix ≤ H) (q : QbdH H (actualCoefficients n e)) :
    jQ n e (corQG (actualCoefficients n e) hH q) = corH H (actualCoefficients n e) (jQH H hH (actualCoefficients n e) q) := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H hH (actualCoefficients n e) q
  rw [corQG_qBdH, jQ_qBd, jQH_qBdH, corH_jH0]
  rfl

theorem PD_avgBd (c : Bd V₀) :
    (PDboundary (Rep.res principalSix.subtype V₀)).hom (avgBd V₀ c) =
      ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) • ∑ x : IntegralGL ⧸ principalSix,
        hcL V₀ x.out ((PDboundary (Rep.res principalSix.subtype V₀)).hom c) := by
  unfold avgBd
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact BR.PDboundary_equivariant q.out V₀ c

/-- **The `PD_∂` square from `H` to `G`**: the neat-level restriction of the `G`-level dual of `(B_H → B_G) q` is the `G/Γ(6)`-average of the
`H`-invariant dual class `PD_∂^H q`, `[G:Γ(6)]⁻¹ ∑_{x ∈ G/Γ(6)} x · PD_∂^H q`. -/
theorem PDQ_corQG (n : ℕ) (e : ℤ) (hH : principalSix ≤ H) (q : QbdH H (actualCoefficients n e)) :
    (homologyMap (restrBd n e) 1).hom (PDQ n e (corQG (actualCoefficients n e) hH q)) =
      ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) • ∑ x : IntegralGL ⧸ principalSix,
        hcL (actualCoefficients n e) x.out (PDQH H hH (actualCoefficients n e) q) := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H hH (actualCoefficients n e) q
  rw [corQG_qBdH, PDQH_qBdH]
  have hy : resToBoundary n e (PDQ n e ((qBd (actualCoefficients n e)).hom c)) = avgBd (actualCoefficients n e) c := by
    have h := PDG_symm_apply n e (PDQ n e ((qBd (actualCoefficients n e)).hom c))
    rw [← h]
    have e1 : PDQ n e ((qBd (actualCoefficients n e)).hom c) =
        (PDG n e) ((coinvIso n e).symm ((qBd (actualCoefficients n e)).hom c)) := rfl
    rw [e1, LinearEquiv.symm_apply_apply, coinvIso_symm_qBd]
  have h2 : (homologyMap (restrBd n e) 1).hom (PDQ n e ((qBd (actualCoefficients n e)).hom c)) =
      (PDboundary (restrictedCoefficients n e)).hom (avgBd (actualCoefficients n e) c) := by
    rw [← hy]
    exact (PDboundary_resToBoundary n e _).symm
  rw [h2, ← avgBd_avgBdH (H := H), PD_avgBd, PD_avgBdH]

end G

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
