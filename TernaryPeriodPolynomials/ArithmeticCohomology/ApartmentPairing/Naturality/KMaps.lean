module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KShapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Natural

@[expose] public section


/-!
# O1/O3: the `K`-level diagram with the paper's objects, and the squares with the boundary Shapiro isomorphism

Formalized by Claude Sonnet 5.5.

`H3_K_equiv_eq_thetaH`: the library's `K`-level duality is the generic `thetaH` at `H = K` (`psi_eq_psiGen`, `stK_eq_stH`).
`levelK_diagram_geom`: `F^K_{j^K_*q}(ℓ) = ⟨PD_∂^K q, ∂a⟩` for `q ∈ H₃((E ⊗ Sing ∂X̃)_K)` (the descended `jQH`, `PDQH` of `HLevelMaps`).
`jQ_shapiroBdH`: `j^G_* ∘ Sh_∂ = Cor_K^G ι_* ∘ j^K_*` (no scalar; `Cor_K^G ι_*` is Mathlib's Shapiro inverse).
`evaluator_shapiroBdH`, `pairing_shapiroBdH`: the top evaluators and the bottom arrows differ by exactly `[G:K]⁻¹`, derived in Lean from
`frobenius_thetaG_cor` (Mackey bookkeeping with the `G/Γ(6)`- versus `K/Γ(6)`-averages) and the two level diagrams.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.PolynomialGLAction
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPoly.SingularBoundaryRestriction TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem eH_K_eq_sixEquiv : (eH K principalSix_le_K : NH K ≃* principalSix) = sixEquiv :=
  MulEquiv.ext (fun _ => rfl)

theorem psi_eq_psiGen (n : ℕ) (t : Fin 2) (y : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    psi n t y = psiGen (NH K) (eH K principalSix_le_K) (MH K (Vnt n t)) y := by
  have h := eH_K_eq_sixEquiv
  rw [h]
  rfl

theorem stK_eq_stH : (stK : Representation ℚ ↥K OrdinaryIncidenceChains.Cycles) = stH K := by
  apply MonoidHom.ext
  intro k
  apply LinearMap.ext
  intro z
  exact (OrdinaryFullAction.cycleAction_K k z).symm

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- The library's `K`-level duality `H3_K_equiv` is the generic intermediate-level duality `thetaH` for `H = K`. -/
theorem H3_K_equiv_eq_thetaH (n : ℕ) (t : Fin 2) (w : groupHomology (EK n t) 3) :
    ((H3_K_equiv n t w).val : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) =
      ((thetaH K principalSix_le_K (Vnt n t) (capAll (Vnt n t)) w).val :
        OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ↥(MH K (Vnt n t))) := by
  obtain ⟨y, rfl⟩ := corN_surjective (A := EK n t) (n := 3) card_ne_zero w
  have hK := neatDualityEquivariant_of_capEps n t
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (Rep.of (coeff n t)))
  rw [H3_K_equiv_corN, psi_avgN hK]
  have e2 := thetaH_corN K principalSix_le_K (Vnt n t) (capAll (Vnt n t)) y
  refine Eq.trans ?_ e2.symm
  rw [psi_eq_psiGen, stK_eq_stH]
  rfl

theorem mapSix_eq_liftN (n : ℕ) (t : Fin 2) (y : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    (mapSix n t).hom.hom y = (liftN K principalSix_le_K (Vnt n t)).hom.hom y := by
  have h : (mapSix n t).hom = (liftN K principalSix_le_K (Vnt n t)).hom := by
    unfold mapSix liftN
    exact groupHomology.map_congr (congrArg (fun e : NH K ≃* principalSix => (e : NH K →* principalSix))
      eH_K_eq_sixEquiv.symm) rfl 3
  exact congrArg (fun f => f.hom y) h

theorem pushN_eq (n : ℕ) (t : Fin 2) (y : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    pushN n t y = (groupHomology.map (MonoidHom.id principalSix) (iotaN n t) 3).hom
      ((liftN K principalSix_le_K (Vnt n t)).hom.hom y) := by
  unfold pushN
  rw [LinearMap.comp_apply, mapSix_eq_liftN]

/-- **The square `Cor_K^G ι_* ∘ j^K_* = j^G_* ∘ Sh_∂`** (Mathlib's Shapiro inverse intertwines `j`; no scalar). -/
theorem jQ_shapiroBdH (n : ℕ) (t : Fin 2) (q : QbdH K (Vnt n t)) :
    jQ n (expT t) ((shapiroBdH n t).hom q) =
      (groupHomology.map K.subtype (iotaK n t) 3).hom (jQH K principalSix_le_K (Vnt n t) q) := by
  obtain ⟨c, rfl⟩ := qBdH_surjective K principalSix_le_K (Vnt n t) q
  rw [shapiroBdH_qBdH, jQ_qBd, jQH_qBdH]
  unfold jH0 corNH
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  set x := (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype (Vnt n t)) 3).hom c with hx
  have hy : (liftN K principalSix_le_K (Vnt n t)).hom.hom ((liftN K principalSix_le_K (Vnt n t)).inv.hom x) = x := by
    change ((liftN K principalSix_le_K (Vnt n t)).inv ≫ (liftN K principalSix_le_K (Vnt n t)).hom).hom x = x
    rw [Iso.inv_hom_id]; rfl
  have hcp := cor_pushN n t ((liftN K principalSix_le_K (Vnt n t)).inv.hom x)
  have hp := congrArg (corN principalSix (MG n t) 3) (pushN_eq n t ((liftN K principalSix_le_K (Vnt n t)).inv.hom x))
  rw [hy] at hp
  refine Eq.trans ?_ (hp.symm.trans hcp)
  have hnat := ConcreteCategory.congr_hom
    (TernaryPeriodPolynomials.Argument.Lemma33.Normalized.boundaryToGroup_natural (iotaN n t)) c
  change (corN principalSix (MG n t) 3) ((SymmetricSpaceBoundaryDuality.boundaryToGroup _ 3).hom (neatIota n t c)) = _
  rw [show (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype (MG n t)) 3).hom (neatIota n t c) =
    (groupHomology.map (MonoidHom.id principalSix) (iotaN n t) 3).hom x from hnat]

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **Lemma 3.3 at level `K`** with the actual `K`-level objects: for `q ∈ H₃((E ⊗ Sing ∂X̃)_K)`, the value of the `K`-level Steinberg
functional of `j^K_* q` on the identity apartment is the flat pairing of `PD_∂^K q` (no scalar). -/
theorem levelK_diagram_geom (n : ℕ) (t : Fin 2) (q : QbdH K (Vnt n t)) :
    (H3_K_equiv n t (jQH K principalSix_le_K (Vnt n t) q)).val OrdinaryTopBoundaryComparison.identityApartment =
      flatBoundaryPairing (Rep.res principalSix.subtype (Vnt n t)) (PDQH K principalSix_le_K (Vnt n t) q) := by
  rw [H3_K_equiv_eq_thetaH]
  exact levelH_diagram_geom K principalSix_le_K (Vnt n t) q

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **The top evaluators under the boundary Shapiro isomorphism: the ledger `[G:K]⁻¹`.**  For `q ∈ H₃(∂X̄_K; E)`,
`evaluation(F^G_{j^G_*(Sh_∂ q)}(ℓ)) = [G:K]⁻¹ · F^K_{j^K_* q}(ℓ)`: the scalar is derived from `frobenius_thetaG_cor` and the square
`jQ_shapiroBdH` (`Sh_∂` is induced by the identity-coset inclusion, `j^G_*∘Sh_∂ = Cor_K^G ι_* ∘ j^K_*`, and `Θ^G`, `Θ^K` are
normalised by the averages over `G/Γ(6)` and `K/Γ(6)`). -/
theorem evaluator_shapiroBdH (n : ℕ) (t : Fin 2) (q : QbdH K (Vnt n t)) :
    evaluation n (topEvaluationG (MG n t) (jQ n (expT t) ((shapiroBdH n t).hom q))) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ •
        (H3_K_equiv n t (jQH K principalSix_le_K (Vnt n t) q)).val OrdinaryTopBoundaryComparison.identityApartment := by
  rw [jQ_shapiroBdH]
  have h := frobenius_thetaG_cor n t (jQH K principalSix_le_K (Vnt n t) q)
  have h2 := congrArg (fun f => (f.val : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) OrdinaryTopBoundaryComparison.identityApartment) h
  exact h2

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **Pairing ledger**: the `G`-level bottom arrow of the boundary Shapiro image equals `[G:K]⁻¹` times the `K`-level bottom arrow,
`evaluation ⟨PD_∂^G (Sh_∂ q), ∂a⟩_M = [G:K]⁻¹ ⟨PD_∂^K q, ∂a⟩_E` (derived from the two actual level diagrams). -/
theorem pairing_shapiroBdH (n : ℕ) (t : Fin 2) (q : QbdH K (Vnt n t)) :
    evaluation n (fullBoundaryPairing n (expT t) (PDQ n (expT t) ((shapiroBdH n t).hom q))) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ •
        flatBoundaryPairing (Rep.res principalSix.subtype (Vnt n t)) (PDQH K principalSix_le_K (Vnt n t) q) := by
  rw [← levelG_diagram_Q, evaluator_shapiroBdH, levelK_diagram_geom]

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
