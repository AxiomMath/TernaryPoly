module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Over
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Transport
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Corr

@[expose] public section


/-!
# The line transport `Θ` and the identification of the orbit components of the induced class

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section IdentGen

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

omit [NeZero M] in
theorem eO_eq_qj {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (Δ S : Subgroup G) (o : orbitRel.Quotient ↥S (G ⧸ Δ))
    (x : G ⧸ Δ) (hx : x = Quotient.out o) :
    (jL S x ∘ₗ qL S x : ((G ⧸ Δ) → E) →ₗ[ℂ] ((G ⧸ Δ) → E)) = eO Δ S o := by
  subst hx; rfl

omit [NeZero M] in
/-- The pull-back identity: the pull-back of `c₀|_{Γ'}` along `μ` is the Mackey coordinate of the transport of `c₀`. -/
theorem LineOver.pullback_eq (c₀ : groupCohomology.H2 (Rep.of ρM)) :
    EdgeNat.h2Map D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i'.rep hp)) (Rep.of ρM) c₀) =
    EdgeNat.h2Map (stabToAt (Δ6 M) (lineSub D.i) D.u) (Rep.of (ρ.comp (stabAt (Δ6 M) (lineSub D.i) D.u).subtype))
      (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u)) LinearMap.id (stabToAt_hT ρ (Δ6 M) (lineSub D.i) D.u)
      (EdgeNat.h2Map (kappa (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u))
        (Rep.of (ρ.comp (Δ6 M).subtype)) (Rep.of (ρ.comp (stabAt (Δ6 M) (lineSub D.i) D.u).subtype))
        (ρ D.u) (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u))
        (transportΔ M ρ ρM hρ c₀)) := by
  have eT : transportΔ M ρ ρM hρ c₀ =
      EdgeNat.h2Map (eΔ M) (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype)) LinearMap.id (eΔ_hT M ρ ρM hρ) c₀ := rfl
  have e1 := h2Map_comp (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u))
    (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype))
    (Rep.of (ρ.comp (stabAt (Δ6 M) (lineSub D.i) D.u).subtype)) LinearMap.id
    (eΔ_hT M ρ ρM hρ) (ρ D.u)
    (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u)) c₀
  have e2 := h2Map_comp ((eΔ M).comp (kappa (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u)))
    (stabToAt (Δ6 M) (lineSub D.i) D.u) (Rep.of ρM)
    (Rep.of (ρ.comp (stabAt (Δ6 M) (lineSub D.i) D.u).subtype))
    (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
    ((ρ D.u).comp LinearMap.id)
    (compHT (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u))
      (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype))
      (Rep.of (ρ.comp (stabAt (Δ6 M) (lineSub D.i) D.u).subtype)) LinearMap.id
      (eΔ_hT M ρ ρM hρ) (ρ D.u)
      (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (lineSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (lineSub D.i) D.u)))
    LinearMap.id (stabToAt_hT ρ (Δ6 M) (lineSub D.i) D.u) c₀
  have e3 := h2Map_comp (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i'.rep hp)) D.mu (Rep.of ρM)
    (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u)) LinearMap.id (fun _ _ => rfl) (ρ (D.u : ↥(gammaN 6)))
    (D.hTgen ρ ρM hρ) c₀
  have hL : EdgeNat.h2Map D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i'.rep hp)) (Rep.of ρM) c₀) = _ := e3
  refine hL.trans (Eq.trans ?_ (by rw [eT, e1, e2]))
  refine h2Map_congr ?_ _ _ _ _ ?_ c₀
  · ext s; rfl
  · ext w; rfl

omit [NeZero M] in
/-- **The `e_O`-component of the restriction to `S_i` of an induced class is `Θ` of the restriction of the level-`M` class** (coefficients `ρ`, `ρM`). -/
theorem LineOver.comp_eq (c₀ : groupCohomology.H2 (Rep.of ρM)) (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀) :
    h2E (Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)))) (eO (Δ6 M) (lineSub D.i) D.o)
      (fun k v => eO_equivariant ρ (Δ6 M) (lineSub D.i) D.o k v)
      (twoCohomologyRestriction (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M))) cV) =
    D.thetaGen ρ ρM hρ (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i'.rep hp)) (Rep.of ρM) c₀) := by
  unfold LineOver.thetaGen
  rw [← Theta_eq_orbit_component ρ (Δ6 M) (lineSub D.i) D.u (lineW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    cV (transportΔ M ρ ρM hρ c₀) hcV _ (D.pullback_eq ρ ρM hρ c₀)]
  rw [← h2Hom_comp, h2Hom_eq_h2Map]
  unfold h2E
  refine h2Map_congr rfl _ _ _ _ ?_ _
  exact (eO_eq_qj (Δ6 M) (lineSub D.i) D.o (D.u : ↥(gammaN 6) ⧸ Δ6 M) D.hu).symm

end IdentGen

section Flags

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i')

/-- **Flags, forward**: the conjugate by `μ` of the flag group of `S_i` at `F₀`, intersected with the Mackey stabilizer at `u''`, lies in a flag group of the face `i'` of `Γ(M)`. -/
theorem LineOver.flag_forward (F₀ : GL (Fin 2) ℚ) (u'' : ↥(lineSub D.i)) :
    ∃ F'' : GL (Fin 2) ℚ, ∀ k : ↥(stabAt (StabS (Δ6 M) (lineSub D.i) D.u) (lineFlagS D.i F₀) u''),
      D.mu (kappa (StabS (Δ6 M) (lineSub D.i) D.u) (stabAt (StabS (Δ6 M) (lineSub D.i) D.u) (lineFlagS D.i F₀) u'') u''
        (stabAt_hu _ _ u'') k) ∈ lineFlagStab M i'.rep F'' := by
  set q' : SL(3, ℤ) := D.i.rep * (u''.1.1 : SL(3, ℤ))⁻¹ * D.i.rep⁻¹ with hq'def
  have hq' : q' ∈ lineBorel := by
    have hu : D.i.rep * (u''.1.1 : SL(3, ℤ)) * D.i.rep⁻¹ ∈ lineBorel := conj_mem_lineBorel_of_mem_lineSub D.i u''.2
    have := lineBorel.inv_mem hu
    simpa [hq'def, mul_assoc] using this
  set cg2 := castGL (botRight q'⁻¹) (botRight q') (botRight_q_inv q' hq').2 (botRight_q_inv q' hq').1 with hcg2
  set cg1 := castGL (botRight D.q⁻¹) (botRight D.q) (botRight_q_inv D.q D.hq).2 (botRight_q_inv D.q D.hq).1 with hcg1
  refine ⟨cg1⁻¹ * (cg2⁻¹ * F₀), fun k => ?_⟩
  -- the elements
  have hk0 : (⟨k.1.1.1, k.1.2⟩ : ↥(gammaNQAt 6 D.i.rep)) ∈ lineFlagStab 6 D.i.rep F₀ := k.2.1
  set sS : ↥(lineSub D.i) := u''⁻¹ * k.1 * u'' with hsS
  have hsS_mem : (sS.1.1 : SL(3, ℤ)) ∈ gammaNQAt 6 D.i.rep := sS.2
  have hsS_eq : (sS.1.1 : SL(3, ℤ)) = (u''.1.1 : SL(3, ℤ))⁻¹ * k.1.1.1 * (u''.1.1 : SL(3, ℤ)) := rfl
  have hrel2 : D.i.rep = q' * D.i.rep * (u''.1.1 : SL(3, ℤ)) := by rw [hq'def]; group
  have step2 : (⟨sS.1.1, hsS_mem⟩ : ↥(gammaNQAt 6 D.i.rep)) ∈ lineFlagStab 6 D.i.rep (cg2⁻¹ * F₀) := by
    refine (lineFlagStab_iff_chain 6 6 D.i.rep D.i.rep q' (u''.1.1 : SL(3, ℤ)) hq' hrel2 sS.1.1 hsS_mem k.1.1.1 k.1.2
      (by rw [hsS_eq]; group) (cg2⁻¹ * F₀)).mpr ?_
    rw [← hcg2, mul_inv_cancel_left]
    exact hk0
  have hp : (D.u : SL(3, ℤ))⁻¹ * sS.1.1 * (D.u : SL(3, ℤ)) ∈ gammaNQAt M i'.rep :=
    (D.mu (kappa (StabS (Δ6 M) (lineSub D.i) D.u) (stabAt (StabS (Δ6 M) (lineSub D.i) D.u) (lineFlagS D.i F₀) u'') u''
        (stabAt_hu _ _ u'') k)).2
  have step1 := (lineFlagStab_iff_chain 6 M D.i.rep i'.rep D.q (D.u : SL(3, ℤ)) D.hq D.hrep _ hp sS.1.1 hsS_mem (by group)
    (cg1⁻¹ * (cg2⁻¹ * F₀))).mpr (by rw [← hcg1, mul_inv_cancel_left]; exact step2)
  exact step1

end Flags

section Back

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i')

omit [NeZero M] in
theorem LineOver.mu_injective : Function.Injective D.mu := by
  intro a b hab
  have h1 := congrArg (fun x : ↥(gammaNQAt M i'.rep) => (x : SL(3, ℤ))) hab
  change (D.u : SL(3, ℤ))⁻¹ * D.sval a * (D.u : SL(3, ℤ)) = (D.u : SL(3, ℤ))⁻¹ * D.sval b * (D.u : SL(3, ℤ)) at h1
  have h2 : D.sval a = D.sval b := by
    calc D.sval a = (D.u : SL(3, ℤ)) * ((D.u : SL(3, ℤ))⁻¹ * D.sval a * (D.u : SL(3, ℤ))) * (D.u : SL(3, ℤ))⁻¹ := by group
      _ = (D.u : SL(3, ℤ)) * ((D.u : SL(3, ℤ))⁻¹ * D.sval b * (D.u : SL(3, ℤ))) * (D.u : SL(3, ℤ))⁻¹ := by rw [h1]
      _ = D.sval b := by group
  exact Subtype.ext (Subtype.ext (Subtype.ext h2))

omit [NeZero M] in
theorem LineOver.back_mem_gammaN (h6 : 6 ∣ M) (p : ↥(gammaNQAt M i'.rep)) :
    (D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹ ∈ gammaN 6 :=
  (gammaN 6).mul_mem ((gammaN 6).mul_mem D.u.2 (gammaN_mono h6 (gammaNQAt_le_gammaN M i'.rep p.2))) ((gammaN 6).inv_mem D.u.2)

omit [NeZero M] in
theorem LineOver.back_mem_Q (h6 : 6 ∣ M) (p : ↥(gammaNQAt M i'.rep)) :
    (D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹ ∈ gammaNQAt 6 D.i.rep := by
  show D.i.rep * ((D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹) * D.i.rep⁻¹ ∈ gammaNQ 6
  have hX : i'.rep * (p : SL(3, ℤ)) * i'.rep⁻¹ ∈ gammaNQ M := p.2
  have hrep := D.hrep
  generalize (p : SL(3, ℤ)) = pS at hX ⊢
  have h1 := conj_mem_gammaNQ M (lineBorel.inv_mem D.hq) hX
  have e : D.i.rep * ((D.u : SL(3, ℤ)) * pS * (D.u : SL(3, ℤ))⁻¹) * D.i.rep⁻¹ =
      D.q⁻¹ * (i'.rep * pS * i'.rep⁻¹) * D.q⁻¹⁻¹ := by rw [hrep]; group
  rw [e]
  exact ⟨gammaN_mono h6 h1.1, h1.2⟩

/-- The inverse of `μ`: `p ↦ u' p u'⁻¹` (for `6 ∣ M`). -/
def LineOver.back (h6 : 6 ∣ M) (p : ↥(gammaNQAt M i'.rep)) : StabS (Δ6 M) (lineSub D.i) D.u :=
  ⟨⟨⟨(D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹, D.back_mem_gammaN h6 p⟩, D.back_mem_Q h6 p⟩, by
    refine (mem_stabilizer_quot_iff (Δ6 M) (lineSub D.i) D.u _).mpr ?_
    show (D.u : SL(3, ℤ))⁻¹ * ((D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹) * (D.u : SL(3, ℤ)) ∈ gammaN M
    have e : (D.u : SL(3, ℤ))⁻¹ * ((D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹) * (D.u : SL(3, ℤ)) = p := by group
    rw [e]; exact gammaNQAt_le_gammaN M i'.rep p.2⟩

omit [NeZero M] in
theorem LineOver.mu_back (h6 : 6 ∣ M) (p : ↥(gammaNQAt M i'.rep)) : D.mu (D.back h6 p) = p := by
  apply Subtype.ext
  change (D.u : SL(3, ℤ))⁻¹ * ((D.u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹) * (D.u : SL(3, ℤ)) = p
  group

end Back

section MixedGen

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

/-- **Forward mixedness**: if `ε` vanishes on every flag group of the face `i'` of `Γ(M)`, then `Θ(ε)` (transported to the line group of `Γ(6)`) vanishes on every flag group of `i`. -/
theorem LineOver.thetaGen_flag_zero (ε : groupCohomology.H2 (lineW i' ρM))
    (hε : ∀ F'' : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab M i'.rep F'').subtype (lineW i' ρM) ε = 0)
    (F₀ : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (lineFlagStab 6 D.i.rep F₀).subtype (Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M))))
      (toK D.i (Rep.of (permRep ρ (Δ6 M))) (D.thetaGen ρ ρM hρ ε)) = 0 := by
  rw [toK_res_flag_iff]
  refine res_Theta_eq_zero ρ (Δ6 M) (lineSub D.i) D.u (lineW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    (lineFlagS D.i F₀) ε (fun u'' => ?_)
  obtain ⟨F'', hF''⟩ := D.flag_forward F₀ u''
  exact ⟨lineFlagStab M i'.rep F'', hε F'', hF''⟩

end MixedGen

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
