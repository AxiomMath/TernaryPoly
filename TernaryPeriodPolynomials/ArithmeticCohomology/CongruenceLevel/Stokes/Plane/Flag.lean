module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Theta
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Corr

@[expose] public section


/-!
# Forward mixedness for the plane faces (plane analogue of `FlagCorr`, `LineTransport` flags, `LineTheta` flags)

Formalized by Claude Sonnet 5.5.

`PlaneOver.thetaGen_flag_zero`: if `ε` vanishes on every flag group of the plane face `j'` of `Γ(M)`, then the transport `Θ(ε)` vanishes on every flag group `planeFlagS` of the plane face `j` of `Γ(6)`.
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

section ChainP

variable (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂] (h₁ h₂ q u : SL(3, ℤ))

/-- The integral matrix `topLeft q` of a lower-right block has an integral inverse. -/
theorem topLeft_q_inv (hq : q ∈ planeBorel) :
    topLeft q * topLeft q⁻¹ = 1 ∧ topLeft q⁻¹ * topLeft q = 1 := topLeft_inv_mul q hq

theorem faceFlagStab_iff_chain (hq : q ∈ planeBorel) (hrel : h₂ = q * h₁ * u) (p : SL(3, ℤ))
    (hp : p ∈ gammaNPAt N₂ h₂) (s : SL(3, ℤ)) (hs : s ∈ gammaNPAt N₁ h₁) (hps : s = u * p * u⁻¹) (F : GL (Fin 2) ℚ) :
    (⟨p, hp⟩ : gammaNPAt N₂ h₂) ∈ faceFlagStab N₂ h₂ F ↔
      (⟨s, hs⟩ : gammaNPAt N₁ h₁) ∈ faceFlagStab N₁ h₁
        (castGL (topLeft q⁻¹) (topLeft q) (topLeft_q_inv q hq).2 (topLeft_q_inv q hq).1 * F) := by
  rw [mem_faceFlagStab_iff, mem_faceFlagStab_iff]
  have hX : h₁ * s * h₁⁻¹ ∈ planeBorel := mem_planeBorel_of_mem_planeStab hs.2
  have e : h₂ * p * h₂⁻¹ = q * (h₁ * s * h₁⁻¹) * q⁻¹ := by
    rw [hrel, hps]; group
  rw [e, topLeft_conj q _ hq hX]
  rw [cond_conj F (topLeft q) (topLeft q⁻¹) (topLeft (h₁ * s * h₁⁻¹)) (topLeft_q_inv q hq).1 (topLeft_q_inv q hq).2]

end ChainP

section ToKFlag

variable (i : PlaneFaces 6)
variable (σ : Rep ℂ ↥(gammaN 6))

/-- The flag stabilizer of the frame `F` in `S_i`. -/
def planeFlagS (F : GL (Fin 2) ℚ) : Subgroup ↥(planeSub i) := (faceFlagStab 6 (planeFaceRepr i) F).comap (planeSubEquiv i).toMonoidHom

/-- The isomorphism `faceFlagStab 6 (planeFaceRepr i) F ≅ planeFlagS i F` induced by `K_i ≅ S_i`. -/
def flagPhiP (F : GL (Fin 2) ℚ) : ↥(faceFlagStab 6 (planeFaceRepr i) F) →* ↥(planeFlagS i F) :=
  (((planeSubEquiv i).symm.toMonoidHom).comp (faceFlagStab 6 (planeFaceRepr i) F).subtype).codRestrict _ (fun k => by
    show planeSubEquiv i ((planeSubEquiv i).symm k.1) ∈ faceFlagStab 6 (planeFaceRepr i) F
    simp only [MulEquiv.apply_symm_apply]; exact k.2)

theorem flagPhiPP_bijective (F : GL (Fin 2) ℚ) : Function.Bijective (flagPhiP i F) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : ↥(planeFlagS i F) => ((x : ↥(planeSub i))) ) hab
    exact (planeSubEquiv i).symm.injective this
  · intro s
    refine ⟨⟨planeSubEquiv i s.1, s.2⟩, ?_⟩
    apply Subtype.ext
    exact (planeSubEquiv i).symm_apply_apply s.1

theorem flagPhiPP_hT (F : GL (Fin 2) ℚ) (g : ↥(faceFlagStab 6 (planeFaceRepr i) F)) (v : σ) :
    (Rep.res (planeFlagS i F).subtype (Rep.res (planeSub i).subtype σ)).ρ (flagPhiP i F g) v =
      (Rep.res (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ)).ρ g v := rfl

theorem toKP_res_flag_eq (F : GL (Fin 2) ℚ) (y : groupCohomology.H2 (Rep.res (planeSub i).subtype σ)) :
    twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ) (toKP i σ y) =
      EdgeNat.h2Map (flagPhiP i F) (Rep.res (planeFlagS i F).subtype (Rep.res (planeSub i).subtype σ))
        (Rep.res (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ)) LinearMap.id (fun g v => flagPhiPP_hT i σ F g v)
        (twoCohomologyRestriction (planeFlagS i F).subtype (Rep.res (planeSub i).subtype σ) y) := by
  have e1 := h2Map_comp (planeSubEquiv i).symm.toMonoidHom (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeSub i).subtype σ)
    (Rep.res (planeIncl i) σ) (Rep.res (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ)) LinearMap.id
    (fun g v => toKP_hT i σ g v) LinearMap.id (fun _ _ => rfl) y
  have e2 := h2Map_comp (planeFlagS i F).subtype (flagPhiP i F) (Rep.res (planeSub i).subtype σ)
    (Rep.res (planeFlagS i F).subtype (Rep.res (planeSub i).subtype σ))
    (Rep.res (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ)) LinearMap.id (fun _ _ => rfl) LinearMap.id
    (fun g v => flagPhiPP_hT i σ F g v) y
  rw [twoCohomologyRestriction_eq_h2Map, twoCohomologyRestriction_eq_h2Map]
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine h2Map_congr ?_ _ _ _ _ rfl y
  ext k; rfl

theorem toKP_res_flag_iff (F : GL (Fin 2) ℚ) (y : groupCohomology.H2 (Rep.res (planeSub i).subtype σ)) :
    twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ) (toKP i σ y) = 0 ↔
      twoCohomologyRestriction (planeFlagS i F).subtype (Rep.res (planeSub i).subtype σ) y = 0 := by
  rw [toKP_res_flag_eq]
  have hid : Function.Bijective (LinearMap.id : σ →ₗ[ℂ] σ) := Function.bijective_id
  constructor
  · intro h
    refine (EdgeNat.h2Map_injective (flagPhiP i F) (Rep.res (planeFlagS i F).subtype (Rep.res (planeSub i).subtype σ))
      (Rep.res (faceFlagStab 6 (planeFaceRepr i) F).subtype (Rep.res (planeIncl i) σ)) LinearMap.id (fun g v => flagPhiPP_hT i σ F g v)
      (flagPhiPP_bijective i F) hid) ?_
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

end ToKFlag


section FlagsP

variable {M : ℕ} [NeZero M] {i' : PlaneFaces M} (D : PlaneOver M i')

/-- **FlagsP, forward**: the conjugate by `μ` of the flag group of `S_i` at `F₀`, intersected with the Mackey stabilizer at `u''`, lies in a flag group of the face `i'` of `Γ(M)`. -/
theorem PlaneOver.flag_forward (F₀ : GL (Fin 2) ℚ) (u'' : ↥(planeSub D.i)) :
    ∃ F'' : GL (Fin 2) ℚ, ∀ k : ↥(stabAt (StabS (Δ6 M) (planeSub D.i) D.u) (planeFlagS D.i F₀) u''),
      D.mu (kappa (StabS (Δ6 M) (planeSub D.i) D.u) (stabAt (StabS (Δ6 M) (planeSub D.i) D.u) (planeFlagS D.i F₀) u'') u''
        (stabAt_hu _ _ u'') k) ∈ faceFlagStab M (planeFaceRepr i') F'' := by
  set q' : SL(3, ℤ) := (planeFaceRepr D.i) * (u''.1.1 : SL(3, ℤ))⁻¹ * (planeFaceRepr D.i)⁻¹ with hq'def
  have hq' : q' ∈ planeBorel := by
    have hu : (planeFaceRepr D.i) * (u''.1.1 : SL(3, ℤ)) * (planeFaceRepr D.i)⁻¹ ∈ planeBorel := conj_mem_planeBorel_of_mem_planeSub D.i u''.2
    have := planeBorel.inv_mem hu
    simpa [hq'def, mul_assoc] using this
  set cg2 := castGL (topLeft q'⁻¹) (topLeft q') (topLeft_q_inv q' hq').2 (topLeft_q_inv q' hq').1 with hcg2
  set cg1 := castGL (topLeft D.q⁻¹) (topLeft D.q) (topLeft_q_inv D.q D.hq).2 (topLeft_q_inv D.q D.hq).1 with hcg1
  refine ⟨cg1⁻¹ * (cg2⁻¹ * F₀), fun k => ?_⟩
  -- the elements
  have hk0 : (⟨k.1.1.1, k.1.2⟩ : ↥(gammaNPAt 6 (planeFaceRepr D.i))) ∈ faceFlagStab 6 (planeFaceRepr D.i) F₀ := k.2.1
  set sS : ↥(planeSub D.i) := u''⁻¹ * k.1 * u'' with hsS
  have hsS_mem : (sS.1.1 : SL(3, ℤ)) ∈ gammaNPAt 6 (planeFaceRepr D.i) := sS.2
  have hsS_eq : (sS.1.1 : SL(3, ℤ)) = (u''.1.1 : SL(3, ℤ))⁻¹ * k.1.1.1 * (u''.1.1 : SL(3, ℤ)) := rfl
  have hrel2 : (planeFaceRepr D.i) = q' * (planeFaceRepr D.i) * (u''.1.1 : SL(3, ℤ)) := by rw [hq'def]; group
  have step2 : (⟨sS.1.1, hsS_mem⟩ : ↥(gammaNPAt 6 (planeFaceRepr D.i))) ∈ faceFlagStab 6 (planeFaceRepr D.i) (cg2⁻¹ * F₀) := by
    refine (faceFlagStab_iff_chain 6 6 (planeFaceRepr D.i) (planeFaceRepr D.i) q' (u''.1.1 : SL(3, ℤ)) hq' hrel2 sS.1.1 hsS_mem k.1.1.1 k.1.2
      (by rw [hsS_eq]; group) (cg2⁻¹ * F₀)).mpr ?_
    rw [← hcg2, mul_inv_cancel_left]
    exact hk0
  have hp : (D.u : SL(3, ℤ))⁻¹ * sS.1.1 * (D.u : SL(3, ℤ)) ∈ gammaNPAt M (planeFaceRepr i') :=
    (D.mu (kappa (StabS (Δ6 M) (planeSub D.i) D.u) (stabAt (StabS (Δ6 M) (planeSub D.i) D.u) (planeFlagS D.i F₀) u'') u''
        (stabAt_hu _ _ u'') k)).2
  have step1 := (faceFlagStab_iff_chain 6 M (planeFaceRepr D.i) (planeFaceRepr i') D.q (D.u : SL(3, ℤ)) D.hq D.hrep _ hp sS.1.1 hsS_mem (by group)
    (cg1⁻¹ * (cg2⁻¹ * F₀))).mpr (by rw [← hcg1, mul_inv_cancel_left]; exact step2)
  exact step1

end FlagsP

section MixedGenP

variable {M : ℕ} [NeZero M] {i' : PlaneFaces M} (D : PlaneOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

/-- **Forward mixedness**: if `ε` vanishes on every flag group of the face `i'` of `Γ(M)`, then `Θ(ε)` (transported to the line group of `Γ(6)`) vanishes on every flag group of `i`. -/
theorem PlaneOver.thetaGen_flag_zero (ε : groupCohomology.H2 (planeW i' ρM))
    (hε : ∀ F'' : GL (Fin 2) ℚ, twoCohomologyRestriction (faceFlagStab M (planeFaceRepr i') F'').subtype (planeW i' ρM) ε = 0)
    (F₀ : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr D.i) F₀).subtype (Rep.res (planeIncl D.i) (Rep.of (permRep ρ (Δ6 M))))
      (toKP D.i (Rep.of (permRep ρ (Δ6 M))) (D.thetaGen ρ ρM hρ ε)) = 0 := by
  rw [toKP_res_flag_iff]
  refine res_Theta_eq_zero ρ (Δ6 M) (planeSub D.i) D.u (planeW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    (planeFlagS D.i F₀) ε (fun u'' => ?_)
  obtain ⟨F'', hF''⟩ := D.flag_forward F₀ u''
  exact ⟨faceFlagStab M (planeFaceRepr i') F'', hε F'', hF''⟩

end MixedGenP

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
