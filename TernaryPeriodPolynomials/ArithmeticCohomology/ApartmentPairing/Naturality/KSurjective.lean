module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.GLevelPassage

@[expose] public section


/-!
# Lemma 3.3, induction clause: `res` hits every `K`-invariant neat-level class

Formalized by Claude Sonnet 5.5.

`resK_surjective_invariants`: if `y ∈ H¹(∂X̄_{Γ(6)}; E_{n,t})` is fixed by the geometric action of `K`, then `y` is the restriction of a
class of the `K`-level cohomology `H¹(Hom_K(Res C_*(∂X̃), E_{n,t}))`.  Proof: `∑_{s∈G/K} (rep s)⁻¹ · ι_* y` is `G`-invariant
(`Tsum_invariant`: `g · ι_* y` depends only on the coset `gK`), hence a `G`-level restriction (`fixed_mem_range_restriction`, rational
averaging); pulling back along the Frobenius isomorphism gives a `K`-level class whose restriction has the same `Tsum`
(`restr_frob_class`), and evaluation at the distinguished covector (`evN`, `chain_ev_iota`) recovers the restriction (`evHc_Tsum`).
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
open TernaryPeriodPolynomials.Argument.CoefficientNaturality (coefHomPost)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Evaluation at the distinguished covector as a morphism of `Γ(6)`-representations `Res M ⟶ Res E`. -/
def evN (n : ℕ) (t : Fin 2) : Rep.res principalSix.subtype (MG n t) ⟶ Rep.res principalSix.subtype (Vnt n t) :=
  Rep.ofHom ⟨evaluation n, fun γ => LinearMap.ext fun F =>
    evaluation_action n (expT t) γ.1 (principalSix_le_K γ.2) F⟩

theorem chain_ev_iota (n : ℕ) (t : Fin 2) (g : IntegralGL) :
    coefHomPost boundaryChains (iotaN n t) ≫ hcAct bdryAct (GAct.ofRep principalSix (MG n t)) g ≫
        coefHomPost boundaryChains (evN n t) =
      if g ∈ K then hcAct bdryAct (GAct.ofRep principalSix (Vnt n t)) g else 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  apply rep_hom_ext'
  intro x
  have key : (evN n t).hom ((conjHom (bdryAct.act m) (GAct.ofRep principalSix (MG n t)) g (ψ ≫ iotaN n t)).hom x) =
      if g ∈ K then (conjHom (bdryAct.act m) (GAct.ofRep principalSix (Vnt n t)) g ψ).hom x else 0 := by
    rw [conjHom_apply]
    change evaluation n (coefficientAction n (expT t) g ((iotaK n t).hom (ψ.hom ((bdryAct.act m).ρ g⁻¹ x)))) = _
    rw [iotaK_apply, evaluation_iotaK]
    by_cases hg : g ∈ K
    · rw [ite_eq_left hg, ite_eq_left hg]; rfl
    · rw [ite_eq_right hg, ite_eq_right hg]
  by_cases hg : g ∈ K
  · rw [ite_eq_left hg]
    exact (key.trans (ite_eq_left hg))
  · rw [ite_eq_right hg]
    exact key.trans (ite_eq_right hg)

/-- The map on neat-level boundary cohomology induced by evaluation at the distinguished covector. -/
def evHc (n : ℕ) (t : Fin 2) : Hc (MG n t) →ₗ[ℚ] Hc (Vnt n t) :=
  (homologyMap (coefHomPost boundaryChains (evN n t)) 1).hom

theorem hcL_mul (V₀ : Rep.{0} ℚ IntegralGL) (g h : IntegralGL) (x : Hc V₀) :
    hcL V₀ (g * h) x = hcL V₀ g (hcL V₀ h x) := by
  change (homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) (g * h)) 1).hom x = _
  rw [hcAct_mul, homologyMap_comp]
  rfl

theorem evHc_hcL_iotaHc (n : ℕ) (t : Fin 2) (g : IntegralGL) (z : Hc (Vnt n t)) :
    evHc n t (hcL (MG n t) g (iotaHc n t z)) = if g ∈ K then hcL (Vnt n t) g z else 0 := by
  have h := ConcreteCategory.congr_hom (congrArg (fun f => homologyMap f 1) (chain_ev_iota n t g)) z
  simp only [homologyMap_comp] at h
  by_cases hg : g ∈ K
  · rw [ite_eq_left hg] at h ⊢
    exact h
  · rw [ite_eq_right hg] at h ⊢
    refine h.trans ?_
    rw [homologyMap_zero]
    rfl

theorem hcL_iotaHc_K (n : ℕ) (t : Fin 2) (k : IntegralGL) (hk : k ∈ K) (z : Hc (Vnt n t)) :
    hcL (MG n t) k (iotaHc n t z) = iotaHc n t (hcL (Vnt n t) k z) := by
  have e : coefHomPost boundaryChains (iotaN n t) ≫ hcAct bdryAct (GAct.ofRep principalSix (MG n t)) k =
      hcAct bdryAct (GAct.ofRep principalSix (Vnt n t)) k ≫ coefHomPost boundaryChains (iotaN n t) := by
    apply HomologicalComplex.hom_ext
    intro m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ψ
    apply rep_hom_ext'
    intro x
    change (MG n t).ρ k ((iotaK n t).hom (ψ.hom ((bdryAct.act m).ρ k⁻¹ x))) =
      (iotaK n t).hom ((Vnt n t).ρ k (ψ.hom ((bdryAct.act m).ρ k⁻¹ x)))
    exact (Rep.hom_comm_apply (iotaK n t) ⟨k, hk⟩ _).symm
  have h := ConcreteCategory.congr_hom (congrArg (fun f => homologyMap f 1) e) z
  simp only [homologyMap_comp] at h
  exact h

/-- The sum of the translates `(rep s)⁻¹ · ι_* z` over the cosets `G/K`. -/
def Tsum (n : ℕ) (t : Fin 2) (z : Hc (Vnt n t)) : Hc (MG n t) :=
  ∑ s : NonzeroCovector, hcL (MG n t) (representative s)⁻¹ (iotaHc n t z)

theorem evHc_Tsum (n : ℕ) (t : Fin 2) (z : Hc (Vnt n t)) (hz : ∀ h : ↥K, hcL (Vnt n t) h.1 z = z) :
    evHc n t (Tsum n t z) = z := by
  unfold Tsum
  rw [map_sum]
  simp only [evHc_hcL_iotaHc]
  have : ∀ s : NonzeroCovector, (if (representative s)⁻¹ ∈ K then hcL (Vnt n t) (representative s)⁻¹ z else 0) =
      if s = distinguished then z else 0 := fun s => by
    by_cases hs : s = distinguished
    · subst hs
      have hk : (representative distinguished)⁻¹ ∈ K := K.inv_mem ((representative_mem_K_iff _).mpr rfl)
      rw [ite_eq_left hk, ite_eq_left rfl]
      exact hz ⟨_, hk⟩
    · have hk : (representative s)⁻¹ ∉ K := fun h =>
        hs ((representative_mem_K_iff s).mp (by simpa using K.inv_mem h))
      rw [ite_eq_right hk, ite_eq_right hs]
  simp only [this]
  simp

theorem rowMove_rep (s : NonzeroCovector) : rowMove (representative s) distinguished = s := by
  rw [rowMove_distinguished, representative_row]

/-- The translate `W g := g · ι_* z` depends only on the coset `gK` when `z` is `K`-invariant. -/
theorem W_mul_K (n : ℕ) (t : Fin 2) (z : Hc (Vnt n t)) (hz : ∀ h : ↥K, hcL (Vnt n t) h.1 z = z)
    (g k : IntegralGL) (hk : k ∈ K) :
    hcL (MG n t) (g * k) (iotaHc n t z) = hcL (MG n t) g (iotaHc n t z) := by
  rw [hcL_mul, hcL_iotaHc_K n t k hk, hz ⟨k, hk⟩]

theorem Tsum_invariant (n : ℕ) (t : Fin 2) (z : Hc (Vnt n t)) (hz : ∀ h : ↥K, hcL (Vnt n t) h.1 z = z)
    (g : IntegralGL) : hcL (MG n t) g (Tsum n t z) = Tsum n t z := by
  unfold Tsum
  rw [map_sum]
  have hterm : ∀ s : NonzeroCovector,
      hcL (MG n t) g (hcL (MG n t) (representative s)⁻¹ (iotaHc n t z)) =
        hcL (MG n t) (representative (rowMove g⁻¹ s))⁻¹ (iotaHc n t z) := fun s => by
    rw [← hcL_mul]
    have hmem : (g * (representative s)⁻¹)⁻¹ * (representative (rowMove g⁻¹ s))⁻¹ ∈ K := by
      rw [mem_K_iff_rowMove]
      have e1 : (g * (representative s)⁻¹)⁻¹ * (representative (rowMove g⁻¹ s))⁻¹ =
          representative s * g⁻¹ * (representative (rowMove g⁻¹ s))⁻¹ := by group
      rw [e1, rowMove_mul, rowMove_mul, rowMove_rep, (rowMove_rep_inv_iff _ _).mpr rfl]
    have := W_mul_K n t z hz (g * (representative s)⁻¹)
      ((g * (representative s)⁻¹)⁻¹ * (representative (rowMove g⁻¹ s))⁻¹) hmem
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp only [hterm]
  let e : NonzeroCovector ≃ NonzeroCovector :=
    { toFun := fun s => rowMove g⁻¹ s
      invFun := fun s => rowMove g s
      left_inv := fun s => by simp [← rowMove_mul]
      right_inv := fun s => by simp [← rowMove_mul] }
  exact Equiv.sum_comp e (fun s => hcL (MG n t) (representative s)⁻¹ (iotaHc n t z))

/-- **The restriction `resK` hits every `K`-invariant neat class**: the `K/Γ(6)`-invariants of the neat-level boundary cohomology are
exactly the image of the `K`-level cohomology `H¹(Hom_K(Res C_*(∂X̃), E))` (rational averaging, via the Frobenius isomorphism and the
`G`-level descent). -/
theorem resK_surjective_invariants (n : ℕ) (t : Fin 2) (y : Hc (Vnt n t))
    (hy : ∀ h : ↥K, repHc (Vnt n t) K h y = y) :
    ∃ ω : (cochainsK n t).homology 1, resK n t ω = y := by
  have hy' : ∀ h : ↥K, hcL (Vnt n t) h.1 y = y := hy
  obtain ⟨ωG, hωG⟩ := fixed_mem_range_restriction n (expT t) (Tsum n t y) (Tsum_invariant n t y hy')
  refine ⟨(frobH1 n t).inv.hom ωG, ?_⟩
  have h1 := restr_frob_class n t ((frobH1 n t).inv.hom ωG)
  have h2 : (frobH1 n t).hom.hom ((frobH1 n t).inv.hom ωG) = ωG := by
    change ((frobH1 n t).inv ≫ (frobH1 n t).hom).hom ωG = ωG
    rw [Iso.inv_hom_id]; rfl
  rw [h2] at h1
  have h3 : Tsum n t (resK n t ((frobH1 n t).inv.hom ωG)) = Tsum n t y := by
    unfold Tsum
    rw [← h1]
    exact hωG
  have h4 := congrArg (evHc n t) h3
  rw [evHc_Tsum n t _ (fun h => resK_invariant n t _ h), evHc_Tsum n t y hy'] at h4
  exact h4

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
