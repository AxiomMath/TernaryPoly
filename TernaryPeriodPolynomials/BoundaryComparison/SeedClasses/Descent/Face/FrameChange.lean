module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Conjugation
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.LocallyInner
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RestrictionComposition

@[expose] public section


/-!
# Change of frame within a plane: the mixed cuspidal group does not depend on the conjugator

Paper: Lemma C.3 (`ar:lem:seed`).

* `EdgeNat.restriction_h2Map`, `EdgeNat.restriction_h2Map_eq_zero_iff`: restriction to subgroups (or
  along any homomorphisms related by `α ∘ ι₂ = ι₁ ∘ κ`) commutes with the transport `h2Map` of `H²`,
  and for bijective `κ`, `T` the vanishing of the restriction of a transported class is equivalent to
  the vanishing of the restriction of the class.
* `faceLocallyInner_eq_iInf`: a class vanishing on every flag stabilizer vanishes on the radical.
* `map_faceCuspidalInH2_frame`: for `q ∈ P(ℚ) ∩ SL₃(ℤ)` (`planeBorel`), the cusps `h⁻¹Ph` and
  `(qh)⁻¹P(qh)` have the same plane group (`gammaNPAt_mul_left`); the (identity) transport of `H²`
  maps the group of classes with edge in `𝒞_{h⁻¹Ph}(E)` onto that of `(qh)⁻¹P(qh)`. The frame
  `h` enters the Levi, the radical and the splitting of the cusp (so `q` acts on them by the block of
  `q`, and translations in `q` change the splitting), but not the locally inner classes, which are
  defined by the flag stabilizers (`faceFlagStab_mul_left`).

Together with `FaceConjugation.map_faceCuspidalInH2_conj` (the change `h ↦ hγ`) this shows that
`𝒞_{P'}(E) ⊂ H²(Γ_{P'}, E)` is independent of the integral conjugator `h' = q h γ` of the face.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace EdgeNat

variable {E₁ E₂ : Type} [Group E₁] [Group E₂] (α : E₂ →* E₁)
  (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ →ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (α g) v) = ρ₂.ρ g (T v))
  {K₁ K₂ : Type} [Group K₁] [Group K₂] (ι₁ : K₁ →* E₁) (ι₂ : K₂ →* E₂) (κ : K₂ →* K₁)
  (hκ : ∀ k, α (ι₂ k) = ι₁ (κ k))

include hκ hT in
theorem hT_res (k : K₂) (v : Rep.res ι₁ ρ₁) :
    T ((Rep.res ι₁ ρ₁).ρ (κ k) v) = (Rep.res ι₂ ρ₂).ρ k (T v) := by
  have := hT (ι₂ k) v
  rw [hκ] at this
  exact this

include hκ hT in
/-- **Restriction commutes with the transport of `H²`.** -/
theorem restriction_h2Map (y : groupCohomology.H2 ρ₁) :
    twoCohomologyRestriction ι₂ ρ₂ (h2Map α ρ₁ ρ₂ T hT y) =
      h2Map κ (Rep.res ι₁ ρ₁) (Rep.res ι₂ ρ₂) T (hT_res α ρ₁ ρ₂ T hT ι₁ ι₂ κ hκ)
        (twoCohomologyRestriction ι₁ ρ₁ y) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective ρ₁ y
  rw [h2Map_π, twoCohomologyRestriction_apply, twoCohomologyRestriction_apply, h2Map_π]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro a b
  change T (z.1 (α (ι₂ a), α (ι₂ b))) = T (z.1 (ι₁ (κ a), ι₁ (κ b)))
  rw [hκ, hκ]

include hκ hT in
/-- If `κ` and `T` are bijective, restriction of a transported class vanishes iff the restriction of
the original class does. -/
theorem restriction_h2Map_eq_zero_iff (hκb : Function.Bijective κ) (hTb : Function.Bijective T)
    (y : groupCohomology.H2 ρ₁) :
    twoCohomologyRestriction ι₂ ρ₂ (h2Map α ρ₁ ρ₂ T hT y) = 0 ↔
      twoCohomologyRestriction ι₁ ρ₁ y = 0 := by
  rw [restriction_h2Map α ρ₁ ρ₂ T hT ι₁ ι₂ κ hκ]
  have hinj := h2Map_injective κ (Rep.res ι₁ ρ₁) (Rep.res ι₂ ρ₂) T
    (hT_res α ρ₁ ρ₂ T hT ι₁ ι₂ κ hκ) hκb hTb
  rw [← map_zero (h2Map κ (Rep.res ι₁ ρ₁) (Rep.res ι₂ ρ₂) T
    (hT_res α ρ₁ ρ₂ T hT ι₁ ι₂ κ hκ))]
  exact hinj.eq_iff

end EdgeNat


section FrameChange

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- The radical lies in every flag stabilizer. -/
def faceInlFlag (F : GL (Fin 2) ℚ) : RadicalLattice →* faceFlagStab N h F :=
  (faceExt N h).inl.codRestrict _ (fun r => by
    have : (faceExt N h).rightHom ((faceExt N h).inl r) = 1 := by
      have hk : (faceExt N h).inl r ∈ (faceExt N h).rightHom.ker := by
        rw [← (faceExt N h).range_inl_eq_ker_rightHom]; exact ⟨r, rfl⟩
      exact hk
    show (faceExt N h).rightHom ((faceExt N h).inl r) ∈ leviCuspStab (CongruenceSubgroup.Gamma N) F
    rw [this]; exact one_mem _)

/-- The locally inner classes are the classes vanishing on every flag stabilizer (vanishing on the
radical is automatic). -/
theorem faceLocallyInner_eq_iInf :
    faceLocallyInner N h n = ⨅ F : GL (Fin 2) ℚ, LinearMap.ker
      (twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n)) := by
  apply le_antisymm
  · exact inf_le_right
  · intro y hy
    refine ⟨?_, hy⟩
    have h1 : twoCohomologyRestriction (faceFlagStab N h 1).subtype (faceRep N h n) y = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy 1)
    have hcomp : (faceExt N h).inl = (faceFlagStab N h 1).subtype.comp (faceInlFlag N h 1) := rfl
    show twoCohomologyRestriction (faceExt N h).inl (faceRep N h n) y = 0
    rw [hcomp, FacePairing.twoCohomologyRestriction_comp, h1, map_zero]


variable (q : SL(3, ℤ)) (hq : q ∈ planeBorel)

/-- The identification `Γ_{(qh)⁻¹P(qh)} = Γ_{h⁻¹Ph}` of the plane groups. -/
def frameHom : gammaNPAt N (q * h) →* gammaNPAt N h :=
  Subgroup.inclusion (le_of_eq (gammaNPAt_mul_left N h q hq))

omit [NeZero N] in
theorem frameHom_bijective : Function.Bijective (frameHom N h q hq) := by
  constructor
  · exact Subgroup.inclusion_injective _
  · intro g
    exact ⟨⟨g.1, by rw [gammaNPAt_mul_left N h q hq]; exact g.2⟩, rfl⟩

/-- The coefficient comparison for the change of frame is the identity. -/
def frameT : GeneralEisenstein.HomogeneousPoly n →ₗ[ℂ] GeneralEisenstein.HomogeneousPoly n :=
  LinearMap.id

omit [NeZero N] in
theorem coe_frameHom (g : gammaNPAt N (q * h)) :
    ((frameHom N h q hq g : gammaNPAt N h) : SL(3, ℤ)) = (g : SL(3, ℤ)) :=
  Subgroup.coe_inclusion (le_of_eq (gammaNPAt_mul_left N h q hq)) g

omit [NeZero N] in
theorem frameT_intertwines (g : gammaNPAt N (q * h)) (v : GeneralEisenstein.HomogeneousPoly n) :
    frameT n ((faceRep N h n).ρ (frameHom N h q hq g) v) =
      (faceRep N (q * h) n).ρ g (frameT n v) := by
  change ambRep n ((frameHom N h q hq g : gammaNPAt N h) : SL(3, ℤ)) v = ambRep n (g : SL(3, ℤ)) v
  rw [coe_frameHom]

theorem frameHom_mem_flag (F F' : GL (Fin 2) ℚ)
    (hF : (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
      (faceFlagStab N h F').map (gammaNPAt N h).subtype) (s : faceFlagStab N (q * h) F) :
    frameHom N h q hq s.1 ∈ faceFlagStab N h F' := by
  have h1 : (s.1 : SL(3, ℤ)) ∈ (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype :=
    ⟨s.1, s.2, rfl⟩
  rw [hF] at h1
  obtain ⟨t, ht, hts⟩ := h1
  have : t = frameHom N h q hq s.1 := Subtype.ext (hts.trans (coe_frameHom N h q hq s.1).symm)
  rw [← this]; exact ht

/-- The identification of the two flag stabilizers. -/
def frameKappa (F F' : GL (Fin 2) ℚ)
    (hF : (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
      (faceFlagStab N h F').map (gammaNPAt N h).subtype) :
    faceFlagStab N (q * h) F →* faceFlagStab N h F' :=
  ((frameHom N h q hq).comp (faceFlagStab N (q * h) F).subtype).codRestrict _
    (frameHom_mem_flag N h q hq F F' hF)

theorem frameKappa_coe (F F' : GL (Fin 2) ℚ)
    (hF : (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
      (faceFlagStab N h F').map (gammaNPAt N h).subtype) (k : faceFlagStab N (q * h) F) :
    (((frameKappa N h q hq F F' hF k : faceFlagStab N h F') : gammaNPAt N h) : SL(3, ℤ)) =
      ((k : gammaNPAt N (q * h)) : SL(3, ℤ)) :=
  coe_frameHom N h q hq k.1

theorem frameKappa_bijective (F F' : GL (Fin 2) ℚ)
    (hF : (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
      (faceFlagStab N h F').map (gammaNPAt N h).subtype) :
    Function.Bijective (frameKappa N h q hq F F' hF) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun x : faceFlagStab N h F' => ((x : gammaNPAt N h) : SL(3, ℤ))) hab
    simp only [frameKappa_coe] at this
    exact this
  · intro t
    have h1 : ((t.1 : gammaNPAt N h) : SL(3, ℤ)) ∈
        (faceFlagStab N h F').map (gammaNPAt N h).subtype := ⟨t.1, t.2, rfl⟩
    rw [← hF] at h1
    obtain ⟨s, hs, hst⟩ := h1
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [frameKappa_coe]
    exact hst

theorem frame_flag_iff (F F' : GL (Fin 2) ℚ)
    (hF : (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
      (faceFlagStab N h F').map (gammaNPAt N h).subtype)
    (y : groupCohomology.H2 (faceRep N h n)) :
    twoCohomologyRestriction (faceFlagStab N (q * h) F).subtype (faceRep N (q * h) n)
        (EdgeNat.h2Map (frameHom N h q hq) (faceRep N h n) (faceRep N (q * h) n)
          (frameT n) (frameT_intertwines N h n q hq) y) = 0 ↔
      twoCohomologyRestriction (faceFlagStab N h F').subtype (faceRep N h n) y = 0 :=
  EdgeNat.restriction_h2Map_eq_zero_iff (frameHom N h q hq) (faceRep N h n)
    (faceRep N (q * h) n) (frameT n) (frameT_intertwines N h n q hq)
    (faceFlagStab N h F').subtype (faceFlagStab N (q * h) F).subtype
    (frameKappa N h q hq F F' hF) (fun _ => rfl) (frameKappa_bijective N h q hq F F' hF)
    Function.bijective_id y


include hq in
theorem faceFlagStab_mul_left_symm (F' : GL (Fin 2) ℚ) :
    ∃ F : GL (Fin 2) ℚ, (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
      (faceFlagStab N h F').map (gammaNPAt N h).subtype := by
  obtain ⟨F, hF⟩ := faceFlagStab_mul_left N (q * h) q⁻¹ (planeBorel.inv_mem hq) F'
  rw [inv_mul_cancel_left] at hF
  exact ⟨F, hF.symm⟩

/-- **Change of the integral conjugator within the plane.** For `q ∈ P(ℚ) ∩ SL₃(ℤ)` the transport
`H²(Γ_{h⁻¹Ph}, E_n) → H²(Γ_{(qh)⁻¹P(qh)}, E_n)` along the identification of the (equal) plane groups
maps the group of classes with edge in the mixed cuspidal group of the frame `h` onto that of the
frame `qh`: the group `𝒞_{P'}(E)` does not depend on the parametrization of the cusps of the binary
Levi. -/
theorem map_faceCuspidalInH2_frame :
    Submodule.map (EdgeNat.h2Map (frameHom N h q hq) (faceRep N h n) (faceRep N (q * h) n)
        (frameT n) (frameT_intertwines N h n q hq)) (faceCuspidalInH2 N h n) =
      faceCuspidalInH2 N (q * h) n := by
  rw [faceCuspidalInH2_eq_locallyInner, faceCuspidalInH2_eq_locallyInner,
    faceLocallyInner_eq_iInf, faceLocallyInner_eq_iInf]
  have hbij := EdgeNat.h2Map_surjective (frameHom N h q hq) (faceRep N h n) (faceRep N (q * h) n)
    (frameT n) (frameT_intertwines N h n q hq) (frameHom_bijective N h q hq) Function.bijective_id
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (Submodule.mem_iInf _).mpr fun F => ?_
    obtain ⟨F', hF⟩ := faceFlagStab_mul_left N h q hq F
    exact (frame_flag_iff N h n q hq F F' hF y).mpr (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy F'))
  · intro hz
    obtain ⟨y, rfl⟩ := hbij z
    refine ⟨y, (Submodule.mem_iInf _).mpr fun F' => ?_, rfl⟩
    obtain ⟨F, hF⟩ := faceFlagStab_mul_left_symm N h q hq F'
    exact (frame_flag_iff N h n q hq F F' hF y).mp (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hz F))

end FrameChange

end TernaryPeriodPolynomials.Argument.SeedC3S4c
