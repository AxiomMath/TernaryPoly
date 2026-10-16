module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KDescended

@[expose] public section


/-!
# Lemma 3.3, induction clause: the transported map equals the map descended from the neat-level objects

Formalized by Claude Sonnet 5.5.

`fullBoundaryClassToK` is defined by transport along the Frobenius isomorphism and `shapiroG`.  Here it is identified with the literal
`K`-level objects of `HLevelMaps`: for every `K`-level class `ω ∈ H¹(Hom_K(Res C_*(∂X̃), E_{n,t}))` there is `q ∈ H₃((E ⊗ Sing ∂X̃)_K)`
with `PD_∂^K q = res ω` and `j^K_* q = fullBoundaryClassToK ω` (`fullBoundaryClassToK_descended`), and the second equation holds for
every `q` with `PD_∂^K q = res ω` (`jQH_eq_fullBoundaryClassToK`; `PDQH_injective`).

Scalars: the restriction of the Frobenius partner is the sum of `[G:K]` translates (`resToBoundary_frob`), `[G:K]` is the number of
nonzero covectors (`index_K_eq_card`, orbit-stabilizer for the distinguished covector), and this cancels the factor `[G:K]⁻¹` of
`shapiroG_cor`.
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

/-- The orbit map `G/K → NonzeroCovector`, `gK ↦ g⁻¹·ℓ` (`rowMove` is a right action). -/
def cosetRow : (IntegralGL ⧸ K) → NonzeroCovector :=
  Quotient.lift (fun g : IntegralGL => rowMove g⁻¹ distinguished) (by
    intro a b hab
    have h : (a⁻¹ * b)⁻¹ ∈ K := K.inv_mem (QuotientGroup.leftRel_apply.mp hab)
    have h2 := (mem_K_iff_rowMove _).mp h
    show rowMove a⁻¹ distinguished = rowMove b⁻¹ distinguished
    have : rowMove b⁻¹ distinguished = rowMove a⁻¹ (rowMove (a⁻¹ * b)⁻¹ distinguished) := by
      rw [← rowMove_mul]; congr 1; group
    rw [this, h2])

theorem cosetRow_bijective : Function.Bijective cosetRow := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    change rowMove a⁻¹ distinguished = rowMove b⁻¹ distinguished at hxy
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    rw [mem_K_iff_rowMove, rowMove_mul, hxy, ← rowMove_mul]
    simp
  · intro r
    exact ⟨QuotientGroup.mk (representative r)⁻¹, by
      change rowMove (representative r)⁻¹⁻¹ distinguished = r
      rw [inv_inv, rowMove_distinguished, representative_row]⟩

/-- **The index `[G:K]` is the number of nonzero covectors**: `G/K` is the orbit of the distinguished covector. -/
theorem index_K_eq_card : Nat.card (IntegralGL ⧸ K) = Fintype.card NonzeroCovector := by
  rw [Nat.card_congr (Equiv.ofBijective cosetRow cosetRow_bijective), Nat.card_eq_fintype_card]

/-- Restriction of a `K`-level boundary class to the neat cover is fixed by the conjugation action of `K`. -/
theorem resKc_hcAct (n : ℕ) (t : Fin 2) (g : IntegralGL) (hg : g ∈ K) :
    resKc n t ≫ hcAct bdryAct (GAct.ofRep principalSix (Vnt n t)) g = resKc n t := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply rep_hom_ext'
  intro x
  let φ' : (resC fullBoundaryChains).X m ⟶ EK n t := φ
  change (conjHom (bdryAct.act m) (GAct.ofRep principalSix (Vnt n t)) g (φR n t φ')).hom x = (φR n t φ').hom x
  refine (conjHom_apply (bdryAct.act m) (GAct.ofRep principalSix (Vnt n t)) g (φR n t φ') x).trans ?_
  have h := Rep.hom_comm_apply φ' ⟨g, hg⟩ ((fullBoundaryChains.X m).ρ g⁻¹ x)
  change (Vnt n t).ρ g (φ'.hom ((fullBoundaryChains.X m).ρ g⁻¹ x)) = φ'.hom x
  have h' : (EK n t).ρ ⟨g, hg⟩ (φ'.hom ((fullBoundaryChains.X m).ρ g⁻¹ x)) =
      φ'.hom ((fullBoundaryChains.X m).ρ g ((fullBoundaryChains.X m).ρ g⁻¹ x)) := h.symm
  change (EK n t).ρ ⟨g, hg⟩ _ = _
  rw [h']
  congr 1
  exact LinearMap.congr_fun (show (fullBoundaryChains.X m).ρ g * (fullBoundaryChains.X m).ρ g⁻¹ = 1 by
    rw [← map_mul, mul_inv_cancel, map_one]) x

/-- Boundary Poincaré duality is surjective (it is an isomorphism). -/
theorem PD_surj (V₀ : Rep.{0} ℚ IntegralGL) (x : Hc V₀) :
    ∃ c : Bd V₀, (PDboundary (Rep.res principalSix.subtype V₀)).hom c = x := by
  refine ⟨(SymmetricSpaceBoundaryManifold.boundaryH1CapIso (Rep.res principalSix.subtype V₀)
    SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom.hom
    ((OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso (Rep.res principalSix.subtype V₀)).hom.hom x), ?_⟩
  unfold PDboundary
  rw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]
  exact Iso.hom_inv_id_apply _ _

/-- The restriction of a `K`-level class is invariant under the geometric action of `K` on neat-level boundary cohomology. -/
theorem resK_invariant (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) (h : ↥K) :
    repHc (Vnt n t) K h (resK n t ω) = resK n t ω := by
  have e : homologyMap (resKc n t) 1 ≫ homologyMap (hcAct bdryAct (GAct.ofRep principalSix (Vnt n t)) h.1) 1 =
      homologyMap (resKc n t) 1 := by
    rw [← homologyMap_comp, resKc_hcAct n t h.1 h.2]
  exact ConcreteCategory.congr_hom e ω

open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (PDboundary_natural boundaryToGroup_natural) in
/-- **The neat-level boundary class of the Frobenius partner**: if `c` is the Poincaré dual of the neat restriction of a `K`-level class
`ω`, then `PD_∂⁻¹ res (frob ω) = ∑_{s ∈ G/K} (rep s)⁻¹ · ι_* c`. -/
theorem resToBoundary_frob (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) (c : Bd (Vnt n t))
    (hc : (PDboundary (Rep.res principalSix.subtype (Vnt n t))).hom c = resK n t ω) :
    resToBoundary n (expT t) ((frobH1 n t).hom ω) =
      ∑ s : NonzeroCovector, bdL (MG n t) (representative s)⁻¹ (neatIota n t c) := by
  apply PDboundary_injective n (expT t)
  rw [PDboundary_resToBoundary, restr_frob_class, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 := BR.PDboundary_equivariant (representative s)⁻¹ (MG n t) (neatIota n t c)
  have h2 : (PDboundary (Rep.res principalSix.subtype (MG n t))).hom (neatIota n t c) =
      iotaHc n t ((PDboundary (Rep.res principalSix.subtype (Vnt n t))).hom c) :=
    ConcreteCategory.congr_hom (PDboundary_natural (iotaN n t)) c
  rw [hc] at h2
  change _ = (PDboundary (Rep.res principalSix.subtype (MG n t))).hom (homologyMap (bAct (MG n t) (representative s)⁻¹) 3 _)
  rw [h1, h2]
  rfl

/-- The transported map unfolded: `Sh_G ∘ Cor_{Γ(6)}^G ∘ j_* ∘ PD_∂⁻¹ ∘ res ∘ frob`. -/
theorem fullBoundaryClassToK_apply (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) :
    fullBoundaryClassToK n t ω = shapiroG n t ((corG n (expT t)).hom
      ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n (expT t)) 3).hom
        (resToBoundary n (expT t) ((frobH1 n t).hom ω)))) := rfl

open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (PDboundary_natural boundaryToGroup_natural) in
/-- **The transported map equals the descended one** (O1, K level): for every `K`-level boundary class `ω ∈ H¹(Hom_K(Res C_*(∂X̃), E))`
there is a class `q` of the literal quotient `H₃((E ⊗ Sing ∂X̃)_K)` (coinvariants of the neat-level boundary chains by `K/Γ(6)`) with
`PD_∂^K q = res ω` (the neat-level restriction of `ω`) and `j^K_* q = fullBoundaryClassToK ω`, where `j^K_*` and `PD^K_∂` are the maps
descended from the neat-level `Cor_{Γ(6)}^K ∘ j_*` and the neat-level cap duality.  The scalar `[G:K]` of the Frobenius sum
(`restr_frob_class`) cancels against `shapiroG_cor` via `index_K_eq_card`. -/
theorem fullBoundaryClassToK_descended (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) :
    ∃ q : QbdH K (Vnt n t), PDQH K principalSix_le_K (Vnt n t) q = resK n t ω ∧
      jQH K principalSix_le_K (Vnt n t) q = fullBoundaryClassToK n t ω := by
  obtain ⟨c, hc⟩ := PD_surj (Vnt n t) (resK n t ω)
  refine ⟨(qBdH K principalSix_le_K (Vnt n t)).hom c, ?_, ?_⟩
  · rw [PDQH_qBdH]
    unfold pd0
    rw [LinearMap.comp_apply, hc]
    exact avgR_of_invariant (fun h => resK_invariant n t ω h) 
  · rw [jQH_qBdH, fullBoundaryClassToK_apply, resToBoundary_frob n t ω c hc]
    have hI : (corG n (expT t)).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup
        (restrictedCoefficients n (expT t)) 3).hom (neatIota n t c)) =
        (groupHomology.map K.subtype (iotaK n t) 3).hom (jH0 K principalSix_le_K (Vnt n t) c) := by
      have := jQ_shapiroBdH n t ((qBdH K principalSix_le_K (Vnt n t)).hom c)
      rw [shapiroBdH_qBdH, jQ_qBd, jQH_qBdH] at this
      exact this
    have hs : ∀ s : NonzeroCovector, (corG n (expT t)).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup
        (restrictedCoefficients n (expT t)) 3).hom (bdL (MG n t) (representative s)⁻¹ (neatIota n t c))) =
        (corG n (expT t)).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup
        (restrictedCoefficients n (expT t)) 3).hom (neatIota n t c)) := fun s => by
      have e1 := ConcreteCategory.congr_hom (boundaryToGroup_equivariant (MG n t) (representative s)⁻¹) (neatIota n t c)
      change (corN principalSix (MG n t) 3) ((SymmetricSpaceBoundaryDuality.boundaryToGroup
        (Rep.res principalSix.subtype (MG n t)) 3).hom (homologyMap (bAct (MG n t) (representative s)⁻¹) 3 (neatIota n t c))) = _
      rw [show (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype (MG n t)) 3).hom
        (homologyMap (bAct (MG n t) (representative s)⁻¹) 3 (neatIota n t c)) =
          cAct principalSix (MG n t) 3 (representative s)⁻¹ ((SymmetricSpaceBoundaryDuality.boundaryToGroup
            (Rep.res principalSix.subtype (MG n t)) 3).hom (neatIota n t c)) from e1, corN_cAct]
      rfl
    rw [map_sum, map_sum]
    simp only [hs, Finset.sum_const, Finset.card_univ, hI]
    rw [map_nsmul, shapiroG_cor, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← index_K_eq_card, 
      mul_inv_cancel₀ index_K_ne_zero, one_smul]

/-- Boundary Poincaré duality is injective, for every coefficient module. -/
theorem PD_inj (V₀ : Rep.{0} ℚ IntegralGL) :
    Function.Injective (PDboundary (Rep.res principalSix.subtype V₀)).hom := by
  intro a b h
  unfold PDboundary at h
  have h1 := congrArg (OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso
    (Rep.res principalSix.subtype V₀)).hom.hom h
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h1
  have h2 := congrArg (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (Rep.res principalSix.subtype V₀)
    SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom.hom h1
  simpa using h2

/-- **`PD_∂^H` is injective on the literal quotient `H₃((𝓜 ⊗ Sing ∂X̃)_H)`** (Poincaré duality on the coinvariants). -/
theorem PDQH_injective (H : Subgroup IntegralGL) (hH : principalSix ≤ H) (V₀ : Rep.{0} ℚ IntegralGL) :
    Function.Injective (PDQH H hH V₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨c, rfl⟩ := qBdH_surjective H hH V₀ q
  rw [PDQH_qBdH] at hq
  refine (qBdH_ker H hH V₀ c).mpr (PD_inj V₀ ?_)
  rw [PD_avgBdH]
  exact hq.trans (map_zero _).symm

/-- **The descended maps determine the transported one** (O1, K level): every `q` with `PD_∂^K q = res ω` satisfies
`j^K_* q = fullBoundaryClassToK ω`. -/
theorem jQH_eq_fullBoundaryClassToK (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) (q : QbdH K (Vnt n t))
    (hq : PDQH K principalSix_le_K (Vnt n t) q = resK n t ω) :
    jQH K principalSix_le_K (Vnt n t) q = fullBoundaryClassToK n t ω := by
  obtain ⟨q', h1, h2⟩ := fullBoundaryClassToK_descended n t ω
  rw [PDQH_injective K principalSix_le_K (Vnt n t) (hq.trans h1.symm)]
  exact h2

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
