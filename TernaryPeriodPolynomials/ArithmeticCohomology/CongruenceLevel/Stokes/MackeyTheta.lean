module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeInst

@[expose] public section


/-!
# The transport `Θ` of a class on a group `Γ'` to the `e_O`-component of the restriction to `S` of an induced class

Formalized by Claude Sonnet 5.5.

Let `G ⊇ S, Δ`, `ρ` a representation of `G` on `E`, `u ∈ G` and `Stab = Stab_S(uΔ)`.  For a group `Γ'` with a representation `W`, a homomorphism `μ : Stab → Γ'` and a comparison `T : W → E`
(`T(μ(s) w) = ρ(s) T(w)`), `Theta` is the composite `H²(Γ', W) → H²(Stab, E) ≅ H²(S, Fun(S/Stab, E)) → H²(S, Res_S Fun(G/Δ, E))` (pull-back, inverse Shapiro, extension by zero).
`coord_Theta`: its Shapiro coordinate is the pull-back; `Theta_eq_orbit_component`: if `ε` pulls back to the Mackey coordinate of an induced class `c_V` then `Theta ε` is the orbit component
`jRep (qRep (res_S c_V))`.
-/

open CategoryTheory
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

section Theta

open MulAction

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G) (u : G)

/-- The stabilizer in `S` of the coset `uΔ`. -/
abbrev StabS : Subgroup ↥S := stabilizer ↥S (u : G ⧸ Δ)

/-- The representation of `Stab_S(uΔ)` on `E` by restriction of `ρ`. -/
abbrev rhoStab : Representation ℂ (StabS Δ S u) E := (ρ.comp S.subtype).comp (StabS Δ S u).subtype

/-- The inverse Shapiro isomorphism `H²(Stab, E) ≅ H²(S, Fun(S/Stab, E))`. -/
def shapiroEquiv : groupCohomology.H2 (Rep.of (rhoStab ρ Δ S u)) ≃ₗ[ℂ]
    groupCohomology.H2 (Rep.of (permRep (ρ.comp S.subtype) (StabS Δ S u))) :=
  (LinearEquiv.ofBijective (PhiH (ρ.comp S.subtype) (StabS Δ S u)) (PhiH_bijective (ρ.comp S.subtype) (StabS Δ S u))).symm

theorem PhiH_shapiroEquiv (c : groupCohomology.H2 (Rep.of (rhoStab ρ Δ S u))) :
    PhiH (ρ.comp S.subtype) (StabS Δ S u) (shapiroEquiv ρ Δ S u c) = c :=
  (LinearEquiv.ofBijective (PhiH (ρ.comp S.subtype) (StabS Δ S u)) (PhiH_bijective (ρ.comp S.subtype) (StabS Δ S u))).apply_symm_apply c

variable {Γ' : Type} [Group Γ'] (W : Rep ℂ Γ') (μ : StabS Δ S u →* Γ') (T : W →ₗ[ℂ] E)
  (hT : ∀ (s : StabS Δ S u) (w : W), T (W.ρ (μ s) w) = ρ ((s : ↥S) : G) (T w))

/-- **The transport `Θ`**: pull-back to `Stab_S(uΔ)`, inverse Shapiro, extension by zero from the orbit of `uΔ`. -/
def Theta : groupCohomology.H2 W →ₗ[ℂ] groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ Δ))) :=
  (h2Hom (jRep ρ S (u : G ⧸ Δ))).comp ((shapiroEquiv ρ Δ S u).toLinearMap.comp
    (EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT))

theorem coord_Theta (ε : groupCohomology.H2 W) :
    PhiH (ρ.comp S.subtype) (StabS Δ S u) (h2Hom (qRep ρ S (u : G ⧸ Δ)) (Theta ρ Δ S u W μ T hT ε)) =
      EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT ε := by
  unfold Theta
  simp only [LinearMap.comp_apply]
  rw [← h2Hom_comp, jRep_qRep, h2Hom_id]
  exact PhiH_shapiroEquiv ρ Δ S u _

theorem Theta_eq_orbit_component (cV : groupCohomology.H2 (Rep.of (permRep ρ Δ)))
    (c₀ : groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype))) (hcV : PhiH ρ Δ cV = c₀) (ε : groupCohomology.H2 W)
    (hε : EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT ε =
      EdgeNat.h2Map (stabToAt Δ S u) (Rep.of (ρ.comp (stabAt Δ S u).subtype))
        (Rep.of (rhoStab ρ Δ S u)) LinearMap.id (stabToAt_hT ρ Δ S u)
        (EdgeNat.h2Map (kappa Δ (stabAt Δ S u) u (stabAt_hu Δ S u)) (Rep.of (ρ.comp Δ.subtype))
          (Rep.of (ρ.comp (stabAt Δ S u).subtype)) (ρ u) (kappa_hT ρ Δ (stabAt Δ S u) u (stabAt_hu Δ S u)) c₀)) :
    h2Hom (jRep ρ S (u : G ⧸ Δ)) (h2Hom (qRep ρ S (u : G ⧸ Δ))
      (twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV)) = Theta ρ Δ S u W μ T hT ε := by
  have key : h2Hom (qRep ρ S (u : G ⧸ Δ)) (twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV) =
      shapiroEquiv ρ Δ S u (EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT ε) := by
    apply PhiH_injective (ρ.comp S.subtype) (StabS Δ S u)
    rw [PhiH_shapiroEquiv, hε, phi_qRep, ind_coord ρ Δ c₀ cV hcV (stabAt Δ S u) u (stabAt_hu Δ S u)]
  unfold Theta
  simp only [LinearMap.comp_apply]
  rw [key]
  rfl

end Theta

section Mixed

open MulAction

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G) (u : G)
  {Γ' : Type} [Group Γ'] (W : Rep ℂ Γ') (μ : StabS Δ S u →* Γ') (T : W →ₗ[ℂ] E)
  (hT : ∀ (s : StabS Δ S u) (w : W), T (W.ρ (μ s) w) = ρ ((s : ↥S) : G) (T w))

instance finiteStabQuot [Finite (G ⧸ Δ)] : Finite (↥S ⧸ StabS Δ S u) :=
  Finite.of_equiv _ (orbitEquivQuotientStabilizer ↥S (u : G ⧸ Δ))

/-- **Forward mixedness**: `res_F Θ(ε) = 0` for a subgroup `F ≤ S` as soon as, for every `u'' ∈ S`, the conjugated group `F ∩ u''·Stab·u''⁻¹` is carried by `μ` into a subgroup `F'` of `Γ'` on which `ε` restricts to zero. -/
theorem res_Theta_eq_zero [Finite (G ⧸ Δ)] (F : Subgroup ↥S) (ε : groupCohomology.H2 W)
    (hF : ∀ u'' : ↥S, ∃ F' : Subgroup Γ', twoCohomologyRestriction F'.subtype W ε = 0 ∧
      ∀ k : ↥(stabAt (StabS Δ S u) F u''), μ (kappa (StabS Δ S u) (stabAt (StabS Δ S u) F u'') u''
        (stabAt_hu (StabS Δ S u) F u'') k) ∈ F') :
    twoCohomologyRestriction F.subtype (Rep.res S.subtype (Rep.of (permRep ρ Δ))) (Theta ρ Δ S u W μ T hT ε) = 0 := by
  have : Fintype (MulAction.orbitRel.Quotient ↥F (↥S ⧸ StabS Δ S u)) := Fintype.ofFinite _
  set c := EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT ε with hc
  set z := shapiroEquiv ρ Δ S u c with hz
  have hzc : PhiH (ρ.comp S.subtype) (StabS Δ S u) z = c := PhiH_shapiroEquiv ρ Δ S u c
  have h0 : twoCohomologyRestriction F.subtype (Rep.of (permRep (ρ.comp S.subtype) (StabS Δ S u))) z = 0 := by
    refine res_eq_zero_of_coords (ρ.comp S.subtype) (StabS Δ S u) F z (fun u'' => ?_)
    rw [ind_coord (ρ.comp S.subtype) (StabS Δ S u) c z hzc (stabAt (StabS Δ S u) F u'') u'' (stabAt_hu _ _ _)]
    obtain ⟨F', hres, hmem⟩ := hF u''
    set K := stabAt (StabS Δ S u) F u'' with hK
    let κ := kappa (StabS Δ S u) K u'' (stabAt_hu (StabS Δ S u) F u'')
    have hκ := kappa_hT (ρ.comp S.subtype) (StabS Δ S u) K u'' (stabAt_hu (StabS Δ S u) F u'')
    let ν : ↥K →* ↥F' := (μ.comp κ).codRestrict F' (fun k => hmem k)
    have hμκ : μ.comp κ = F'.subtype.comp ν := by ext k; rfl
    have e1 := h2Map_comp μ κ W (Rep.of (rhoStab ρ Δ S u)) (Rep.of ((ρ.comp S.subtype).comp K.subtype))
      T hT ((ρ.comp S.subtype) u'') hκ ε
    rw [hc, e1]
    have hT₂ : ∀ (g : ↥K) (v : Rep.res F'.subtype W),
        (((ρ.comp S.subtype) u'').comp T) ((Rep.res F'.subtype W).ρ (ν g) v) =
          (Rep.of ((ρ.comp S.subtype).comp K.subtype)).ρ g ((((ρ.comp S.subtype) u'').comp T) v) := by
      intro g v
      change ((ρ.comp S.subtype) u'') (T (W.ρ (F'.subtype (ν g)) v)) = _
      have : F'.subtype (ν g) = μ (κ g) := rfl
      rw [this, hT]
      exact hκ g (T v)
    have e2 := h2Map_comp_zero F'.subtype ν W (Rep.res F'.subtype W) (Rep.of ((ρ.comp S.subtype).comp K.subtype))
      LinearMap.id (fun _ _ => rfl) (((ρ.comp S.subtype) u'').comp T) hT₂ ε hres
    refine (h2Map_congr hμκ W _ (compHT μ κ W (Rep.of (rhoStab ρ Δ S u)) (Rep.of ((ρ.comp S.subtype).comp K.subtype))
      T hT ((ρ.comp S.subtype) u'') hκ) (compHT F'.subtype ν W (Rep.res F'.subtype W)
      (Rep.of ((ρ.comp S.subtype).comp K.subtype)) LinearMap.id (fun _ _ => rfl) (((ρ.comp S.subtype) u'').comp T) hT₂)
      (by ext w; rfl) ε).trans e2
  exact res_h2Hom_zero F.subtype (jRep ρ S (u : G ⧸ Δ)) z h0

/-- **Converse mixedness**: if `res_F Θ(ε) = 0` then the pull-back of `ε` to `F ∩ Stab` (along `μ` restricted to `F ∩ Stab`) vanishes. -/
theorem Theta_res_zero_imp [Finite (G ⧸ Δ)] (F : Subgroup ↥S) (ε : groupCohomology.H2 W)
    (h : twoCohomologyRestriction F.subtype (Rep.res S.subtype (Rep.of (permRep ρ Δ))) (Theta ρ Δ S u W μ T hT ε) = 0) :
    EdgeNat.h2Map (kappa (StabS Δ S u) (stabAt (StabS Δ S u) F 1) 1 (stabAt_hu (StabS Δ S u) F 1))
      (Rep.of (rhoStab ρ Δ S u)) (Rep.of ((ρ.comp S.subtype).comp (stabAt (StabS Δ S u) F 1).subtype))
      ((ρ.comp S.subtype) 1)
      (kappa_hT (ρ.comp S.subtype) (StabS Δ S u) (stabAt (StabS Δ S u) F 1) 1 (stabAt_hu (StabS Δ S u) F 1))
      (EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT ε) = 0 := by
  set c := EdgeNat.h2Map μ W (Rep.of (rhoStab ρ Δ S u)) T hT ε with hc
  set z := shapiroEquiv ρ Δ S u c with hz
  have hzc : PhiH (ρ.comp S.subtype) (StabS Δ S u) z = c := PhiH_shapiroEquiv ρ Δ S u c
  have h1 : twoCohomologyRestriction F.subtype (Rep.of (permRep (ρ.comp S.subtype) (StabS Δ S u)))
      (h2Hom (qRep ρ S (u : G ⧸ Δ)) (Theta ρ Δ S u W μ T hT ε)) = 0 :=
    res_h2Hom_zero F.subtype (qRep ρ S (u : G ⧸ Δ)) _ h
  have h2 : h2Hom (qRep ρ S (u : G ⧸ Δ)) (Theta ρ Δ S u W μ T hT ε) = z := by
    unfold Theta
    simp only [LinearMap.comp_apply]
    rw [← h2Hom_comp, jRep_qRep, h2Hom_id]
    rfl
  rw [h2] at h1
  set K₁ := stabAt (StabS Δ S u) F 1 with hK₁
  have hle : K₁ ≤ F := fun g hg => hg.1
  have hsub : K₁.subtype = F.subtype.comp (Subgroup.inclusion hle) := rfl
  have h3 : twoCohomologyRestriction K₁.subtype (Rep.of (permRep (ρ.comp S.subtype) (StabS Δ S u))) z = 0 := by
    rw [hsub, FacePairing.twoCohomologyRestriction_comp, h1, map_zero]
  have h4 := ind_coord (ρ.comp S.subtype) (StabS Δ S u) c z hzc K₁ 1 (stabAt_hu (StabS Δ S u) F 1)
  rw [h3, map_zero] at h4
  exact h4.symm

end Mixed

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
