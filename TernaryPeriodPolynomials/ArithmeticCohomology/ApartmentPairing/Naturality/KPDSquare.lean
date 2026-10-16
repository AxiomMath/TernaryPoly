module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KTransported

@[expose] public section


/-!
# Lemma 3.3, induction clause: the Poincaré duality square and the three squares together

Formalized by Claude Sonnet 5.5.

`PDQ_shapiroBdH`: for `q` with `PD_∂^K q = res ω`, `PD_∂^G (Sh_∂ q) = [G:K]⁻¹ · frob ω`.  The scalar is derived: the neat-level
boundary class `∑_{s∈G/K} (rep s)⁻¹ · ι_* c` of `frob ω` (`resToBoundary_frob`) is `G`-invariant, hence equal to its own `G`-average,
which is `[G:K]` times the `G`-average of `ι_* c` (`avgBd_bdL`), and `[G:K]` is the number of nonzero covectors (`index_K_eq_card`).
`induction_squares` collects the descent, `j` and `PD_∂` squares for a `K`-level class.
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

/-- The `G`-average is invariant under the geometric action on neat-level boundary homology. -/
theorem avgBd_bdL (V₀ : Rep.{0} ℚ IntegralGL) (g : IntegralGL) (x : Bd V₀) :
    avgBd V₀ (bdL V₀ g x) = avgBd V₀ x := by
  have h : (qBd V₀).hom (bdL V₀ g x - x) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact qBd_bAct V₀ g x
  have h2 := (qBd_ker V₀ _).mp h
  rw [map_sub, sub_eq_zero] at h2
  exact h2

/-- **The Poincaré duality square for the boundary Shapiro isomorphism** (O3, `PD_∂`): if `c` is the Poincaré dual of the neat restriction of a
`K`-level class `ω`, then `PD_∂^G (Sh_∂ (qBdH c)) = [G:K]⁻¹ · frob ω`.  The scalar is derived: `r = ∑_{s∈G/K} (rep s)⁻¹ · ι_* c` is
`G`-invariant (`resToBoundary_frob`), so its `G`-average is `r` on one side and `[G:K] · avg(ι_* c)` on the other. -/
theorem PDQ_shapiroBdH_of_PD (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) (c : Bd (Vnt n t))
    (hc : (PDboundary (Rep.res principalSix.subtype (Vnt n t))).hom c = resK n t ω) :
    PDQ n (expT t) ((shapiroBdH n t).hom ((qBdH K principalSix_le_K (Vnt n t)).hom c)) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • (frobH1 n t).hom ω := by
  apply resToBoundary_injective n (expT t)
  rw [shapiroBdH_qBdH, map_smul]
  have hy : ∀ y : Qbd (actualCoefficients n (expT t)),
      resToBoundary n (expT t) (PDQ n (expT t) y) = ((coinvIso n (expT t)).symm y).1 := by
    intro y
    have h := PDG_symm_apply n (expT t) (PDQ n (expT t) y)
    rw [← h]
    have e : PDQ n (expT t) y = (PDG n (expT t)) ((coinvIso n (expT t)).symm y) := rfl
    rw [e, LinearEquiv.symm_apply_apply]
  change _ = ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • resToBoundary n (expT t) ((frobH1 n t).hom ω)
  rw [hy, coinvIso_symm_qBd]
  change avgBd (MG n t) (neatIota n t c) = _
  have hr := resToBoundary_frob n t ω c hc
  have hfix : avgBd (MG n t) (resToBoundary n (expT t) ((frobH1 n t).hom ω)) =
      resToBoundary n (expT t) ((frobH1 n t).hom ω) :=
    avgBd_of_fixed (MG n t) _ ((mem_H3boundaryG_iff n (expT t) _).mp ⟨_, rfl⟩)
  rw [hr, map_sum] at hfix
  rw [hr]
  simp only [avgBd_bdL, Finset.sum_const, Finset.card_univ] at hfix
  rw [← index_K_eq_card] at hfix
  rw [← hfix, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ index_K_ne_zero, one_smul]

/-- **`PD_∂` square for every `q` with `PD_∂^K q = res ω`**: `PD_∂^G (Sh_∂ q) = [G:K]⁻¹ · frob ω`. -/
theorem PDQ_shapiroBdH (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) (q : QbdH K (Vnt n t))
    (hq : PDQH K principalSix_le_K (Vnt n t) q = resK n t ω) :
    PDQ n (expT t) ((shapiroBdH n t).hom q) = ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • (frobH1 n t).hom ω := by
  obtain ⟨c, hc⟩ := PD_surj (Vnt n t) (resK n t ω)
  have h0 : PDQH K principalSix_le_K (Vnt n t) ((qBdH K principalSix_le_K (Vnt n t)).hom c) = resK n t ω := by
    rw [PDQH_qBdH]
    unfold pd0
    rw [LinearMap.comp_apply, hc]
    exact avgR_of_invariant (fun h => resK_invariant n t ω h)
  rw [PDQH_injective K principalSix_le_K (Vnt n t) (hq.trans h0.symm)]
  exact PDQ_shapiroBdH_of_PD n t ω c hc

/-- **The three squares of the induction clause, together** (O1+O3): for every `K`-level boundary class `ω` there is `q` in the literal
quotient `H₃((E ⊗ Sing ∂X̃)_K)` with `PD_∂^K q = res ω`, `j^K_* q = fullBoundaryClassToK ω`, and `PD_∂^G(Sh_∂ q) = [G:K]⁻¹ frob ω`;
moreover `F^G_{j^G_* Sh_∂ q}(ℓ) = [G:K]⁻¹ F^K_{j^K_* q}(ℓ)` (`evaluator_shapiroBdH`). -/
theorem induction_squares (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) :
    ∃ q : QbdH K (Vnt n t), PDQH K principalSix_le_K (Vnt n t) q = resK n t ω ∧
      jQH K principalSix_le_K (Vnt n t) q = fullBoundaryClassToK n t ω ∧
      PDQ n (expT t) ((shapiroBdH n t).hom q) = ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • (frobH1 n t).hom ω := by
  obtain ⟨q, h1, h2⟩ := fullBoundaryClassToK_descended n t ω
  exact ⟨q, h1, h2, PDQ_shapiroBdH n t ω q h1⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
