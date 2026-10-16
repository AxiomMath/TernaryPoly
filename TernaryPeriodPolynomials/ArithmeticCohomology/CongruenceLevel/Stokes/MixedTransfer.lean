module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Lifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish

@[expose] public section


/-!
# Mixed classes of the face groups give mixed classes at the orbit representatives

Formalized by Claude Sonnet 5.5.

For a face datum (`Grp i`, `emb i`) over the point `b i` and an equivariant map `α` from the complete flags to the label set, a class of `H²(Grp i, E)` whose restriction to the
stabilizer (lifted to `Grp i`) of every complete flag over `b i` vanishes is carried by `faceTau` to a class at the orbit representative that is mixed in the sense of `MixedModel`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Generic

variable {Z : Type} [MulAction Γ6 Z] {F : Type} (o : F → labelOrbits Γ6 Z) (b : F → Z)
  (hb : ∀ i, b i ∈ labelOrbit Γ6 Z (o i))
  (Grp : F → Type) [∀ i, Group (Grp i)] (emb : ∀ i, Grp i →* Γ6) (hinj : ∀ i, Function.Injective (emb i))
  (hrange : ∀ i, (emb i).range = MulAction.stabilizer Γ6 (b i))
  (α : Flag → Z) (hα : ∀ (γ : Γ6) (F : Flag), α (γ • F) = γ • α F)

/-- The stabilizer of a complete flag over `b i`, as a subgroup of the face group `Grp i`. -/
def stabLift (i : F) (F' : Flag) (hF' : α F' = b i) : ↥(MulAction.stabilizer Γ6 F') →* Grp i :=
  (MonoidHom.ofInjective (hinj i)).symm.toMonoidHom.comp
    ((MulAction.stabilizer Γ6 F').subtype.codRestrict (emb i).range (fun s => by
      rw [hrange i, ← hF']
      exact stab_flag_le_stab_pt α hα F' s.2))

theorem emb_stabLift (i : F) (F' : Flag) (hF' : α F' = b i) (s : MulAction.stabilizer Γ6 F') :
    emb i (stabLift b Grp emb hinj hrange α hα i F' hF' s) = s := by
  unfold stabLift
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

/-- Conjugation by `G` maps the stabilizer of `F₀` into that of `G • F₀`. -/
def stabConjFwd (G : Γ6) (F₀ : Flag) : ↥(MulAction.stabilizer Γ6 F₀) →* ↥(MulAction.stabilizer Γ6 (G • F₀)) where
  toFun s := ⟨G * s * G⁻¹, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 s.2]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a c := Subtype.ext (by
    change G * ((a : Γ6) * (c : Γ6)) * G⁻¹ = G * (a : Γ6) * G⁻¹ * (G * (c : Γ6) * G⁻¹)
    group)

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ6 V)

/-- **A class of the face group vanishing on the stabilizers of the flags over `b i` is carried by `faceTau` to a class vanishing on the stabilizers of the flags over `(o i).out`.** -/
theorem faceTau_restriction_zero (i : F) (x : groupCohomology.H2 (Rep.res (emb i) (Rep.of ρ)))
    (hx : ∀ (F' : Flag) (hF' : α F' = b i),
      twoCohomologyRestriction (stabLift b Grp emb hinj hrange α hα i F' hF') (Rep.res (emb i) (Rep.of ρ)) x = 0)
    (F₀ : Flag) (hF₀ : α F₀ = (o i).out) :
    twoCohomologyRestriction (Subgroup.inclusion (by
        have := stab_flag_le_stab_pt α hα F₀
        rw [hF₀] at this
        exact this : MulAction.stabilizer Γ6 F₀ ≤ MulAction.stabilizer Γ6 (o i).out))
      (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ))
      (faceTau o b hb Grp emb hinj hrange ρ i x) = 0 := by
  have hF' : α (faceG o b hb i • F₀) = b i := by
    rw [hα, hF₀, faceG_smul]
  have hκ : ∀ k : MulAction.stabilizer Γ6 F₀,
      faceAlpha o b hb Grp emb hinj hrange i (Subgroup.inclusion (by
        have := stab_flag_le_stab_pt α hα F₀
        rw [hF₀] at this
        exact this : MulAction.stabilizer Γ6 F₀ ≤ MulAction.stabilizer Γ6 (o i).out) k) =
      stabLift b Grp emb hinj hrange α hα i (faceG o b hb i • F₀) hF' (stabConjFwd (faceG o b hb i) F₀ k) := by
    intro k
    apply hinj i
    rw [emb_faceAlpha, emb_stabLift]
    rfl
  have h := EdgeNat.restriction_h2Map (faceAlpha o b hb Grp emb hinj hrange i)
    (Rep.res (emb i) (Rep.of ρ)) (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ))
    (ρ (faceG o b hb i)⁻¹) (faceTau_hT o b hb Grp emb hinj hrange ρ i)
    (stabLift b Grp emb hinj hrange α hα i (faceG o b hb i • F₀) hF')
    (Subgroup.inclusion (by
        have := stab_flag_le_stab_pt α hα F₀
        rw [hF₀] at this
        exact this : MulAction.stabilizer Γ6 F₀ ≤ MulAction.stabilizer Γ6 (o i).out))
    (stabConjFwd (faceG o b hb i) F₀) hκ x
  change _ = _ at h
  unfold faceTau
  rw [h, hx _ hF', map_zero]

section Rational

variable [Module ℚ V] [IsScalarTower ℚ ℂ V]

/-- **The rational transport of such a class is mixed at the orbit representative.** -/
theorem faceTauQ_mixed (i : F) (x : groupCohomology.H2 (Rep.res (emb i) (Rep.of ρ)))
    (hx : ∀ (F' : Flag) (hF' : α F' = b i),
      twoCohomologyRestriction (stabLift b Grp emb hinj hrange α hα i F' hF') (Rep.res (emb i) (Rep.of ρ)) x = 0) :
    MixedModel (W := qRepG ρ) α hα (o i) (faceTauQ o b hb Grp emb hinj hrange ρ i x) := by
  intro F₀ hF₀
  have h0 := faceTau_restriction_zero o b hb Grp emb hinj hrange α hα ρ i x hx F₀ hF₀
  have hq := qH2_map (ρ.comp (MulAction.stabilizer Γ6 (o i).out).subtype)
    (Subgroup.inclusion (by
        have := stab_flag_le_stab_pt α hα F₀
        rw [hF₀] at this
        exact this : MulAction.stabilizer Γ6 F₀ ≤ MulAction.stabilizer Γ6 (o i).out))
    (faceTau o b hb Grp emb hinj hrange ρ i x)
  refine Eq.trans hq.symm ?_
  change qH2 _ (twoCohomologyRestriction _ _ (faceTau o b hb Grp emb hinj hrange ρ i x)) = 0
  rw [h0]
  exact map_zero _

end Rational

end Generic

section CmpNat

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (gammaN 6) V)
  {A : Type} [Group A] (ι : A →* gammaN 6) {B : Type} [Group B] (κ : B →* A)

/-- **Naturality of the comparison with respect to restriction.** -/
theorem cmpH2_restriction (x : groupCohomology.H2 (Rep.res ι (Rep.of ρ))) :
    twoCohomologyRestriction κ (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ))) (cmpH2 ρ ι x) =
      cmpH2 ρ (ι.comp κ) (twoCohomologyRestriction κ (Rep.res ι (Rep.of ρ)) x) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.res ι (Rep.of ρ)) x
  unfold cmpH2
  rw [EdgeNat.h2Map_π, twoCohomologyRestriction_apply, twoCohomologyRestriction_apply]
  erw [EdgeNat.h2Map_π]
  congr 1

/-- … for the dual coefficient module. -/
theorem cmpH2Dual_restriction (x : groupCohomology.H2 (Rep.res ι (Rep.of ρ.dual))) :
    twoCohomologyRestriction κ (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual)) (cmpH2Dual ρ ι x) =
      cmpH2Dual ρ (ι.comp κ) (twoCohomologyRestriction κ (Rep.res ι (Rep.of ρ.dual)) x) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.res ι (Rep.of ρ.dual)) x
  unfold cmpH2Dual
  rw [EdgeNat.h2Map_π, twoCohomologyRestriction_apply, twoCohomologyRestriction_apply]
  erw [EdgeNat.h2Map_π]
  congr 1

end CmpNat

section Concrete

/-- A restriction vanishing along `ιA` vanishes along every `ιB` factoring through it. -/
theorem res_zero_of_factor {G A B : Type} [Group G] [Group A] [Group B] (ρ : Rep ℂ G)
    (y : groupCohomology.H2 ρ) (ιA : A →* G) (ιB : B →* G) (κ : B →* A) (h : ∀ b, ιA (κ b) = ιB b)
    (hy : twoCohomologyRestriction ιA ρ y = 0) : twoCohomologyRestriction ιB ρ y = 0 := by
  have hcomp : ιB = ιA.comp κ := MonoidHom.ext (fun b => (h b).symm)
  rw [hcomp, FacePairing.twoCohomologyRestriction_comp, hy, map_zero]

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (gammaN 6) V)

/-- **The restriction of a mixed class of the line group to the stabilizer of a complete flag over the line vanishes.** -/
theorem lineMixed_hx (i : LineFaces 6)
    (x₀ : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (hx₀ : ∀ F : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab 6 i.rep F).subtype
      (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) x₀ = 0)
    (F' : Flag) (hF' : flagLineOf F' = lineOf i.rep) :
    twoCohomologyRestriction (stabLift (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
      (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant i F' hF')
      (Rep.res (lineEmb i.rep) (Rep.of (rep6 ρ)))
      (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x₀) = 0 := by
  obtain ⟨g', rfl⟩ := exists_flagOf F'
  obtain ⟨q, rfl⟩ : ∃ q, g' = q * i.rep := ⟨g' * i.rep⁻¹, by group⟩
  have hl : lineOf i.rep = lineOf (q * i.rep) := hF'.symm
  have hq : q * i.rep * i.rep⁻¹ ∈ lineBorel := (lineOf_eq_iff i.rep (q * i.rep)).1 hl
  rw [mul_inv_cancel_right] at hq
  obtain ⟨F'', hF''⟩ := lineFlagStab_mul_left 6 i.rep q hq 1
  have hone := lineFlagStab_one_map 6 (by norm_num) (q * i.rep)
  have hB : gammaNBAt 6 (q * i.rep) = (lineFlagStab 6 i.rep F'').map (gammaNQAt 6 i.rep).subtype :=
    hone.symm.trans hF''
  set ι := stabLift (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
      (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant i (flagOf (q * i.rep)) hF' with hι
  have hmem : ∀ s, ι s ∈ lineFlagStab 6 i.rep F'' := by
    intro s
    have he : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) (ι s)) = s.1 :=
      emb_stabLift (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
        (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) flagLineOf
        TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant i (flagOf (q * i.rep)) hF' s
    have hs' : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) (ι s)) ∈
        MulAction.stabilizer Γ6 (flagOf (q * i.rep)) := by
      rw [he]; exact s.2
    have h1 := (mem_stabilizer_flagOf_iff (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) (ι s))
      (q * i.rep)).1 hs'
    rw [hB] at h1
    obtain ⟨k, hk, hkeq⟩ := h1
    have : k = ι s := Subtype.ext hkeq
    rw [← this]; exact hk
  have hnat := cmpH2_restriction ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
    (lineFlagStab 6 i.rep F'').subtype x₀
  rw [hx₀ F'', map_zero] at hnat
  exact res_zero_of_factor _ _ (lineFlagStab 6 i.rep F'').subtype ι (ι.codRestrict _ hmem) (fun s => rfl)
    hnat


/-- **The restriction of a mixed class of the line group to the stabilizer of a complete flag over the line vanishes.** -/
theorem lineMixedDual_hx (i : LineFaces 6)
    (x₀ : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx₀ : ∀ F : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab 6 i.rep F).subtype
      (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) x₀ = 0)
    (F' : Flag) (hF' : flagLineOf F' = lineOf i.rep) :
    twoCohomologyRestriction (stabLift (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
      (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant i F' hF')
      (Rep.res (lineEmb i.rep) (Rep.of (rep6 ρ).dual))
      (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x₀) = 0 := by
  obtain ⟨g', rfl⟩ := exists_flagOf F'
  obtain ⟨q, rfl⟩ : ∃ q, g' = q * i.rep := ⟨g' * i.rep⁻¹, by group⟩
  have hl : lineOf i.rep = lineOf (q * i.rep) := hF'.symm
  have hq : q * i.rep * i.rep⁻¹ ∈ lineBorel := (lineOf_eq_iff i.rep (q * i.rep)).1 hl
  rw [mul_inv_cancel_right] at hq
  obtain ⟨F'', hF''⟩ := lineFlagStab_mul_left 6 i.rep q hq 1
  have hone := lineFlagStab_one_map 6 (by norm_num) (q * i.rep)
  have hB : gammaNBAt 6 (q * i.rep) = (lineFlagStab 6 i.rep F'').map (gammaNQAt 6 i.rep).subtype :=
    hone.symm.trans hF''
  set ι := stabLift (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
      (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant i (flagOf (q * i.rep)) hF' with hι
  have hmem : ∀ s, ι s ∈ lineFlagStab 6 i.rep F'' := by
    intro s
    have he : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) (ι s)) = s.1 :=
      emb_stabLift (fun i : LineFaces 6 => lineOf i.rep) (fun i => ↥(gammaNQAt 6 i.rep))
        (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) flagLineOf
        TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant i (flagOf (q * i.rep)) hF' s
    have hs' : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) (ι s)) ∈
        MulAction.stabilizer Γ6 (flagOf (q * i.rep)) := by
      rw [he]; exact s.2
    have h1 := (mem_stabilizer_flagOf_iff (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) (ι s))
      (q * i.rep)).1 hs'
    rw [hB] at h1
    obtain ⟨k, hk, hkeq⟩ := h1
    have : k = ι s := Subtype.ext hkeq
    rw [← this]; exact hk
  have hnat := cmpH2Dual_restriction ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
    (lineFlagStab 6 i.rep F'').subtype x₀
  rw [hx₀ F'', map_zero] at hnat
  exact res_zero_of_factor _ _ (lineFlagStab 6 i.rep F'').subtype ι (ι.codRestrict _ hmem) (fun s => rfl)
    hnat


/-- **The restriction of a mixed class of the plane group to the stabilizer of a complete flag over the plane vanishes.** -/
theorem planeMixed_hx (i : PlaneFaces 6)
    (x₀ : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (hx₀ : ∀ F : GL (Fin 2) ℚ, twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr i) F).subtype
      (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) x₀ = 0)
    (F' : Flag) (hF' : flagPlaneOf F' = planeOf (planeFaceRepr i)) :
    twoCohomologyRestriction (stabLift (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
      (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant i F' hF')
      (Rep.res (planeEmb (planeFaceRepr i)) (Rep.of (rep6 ρ)))
      (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x₀) = 0 := by
  obtain ⟨g', rfl⟩ := exists_flagOf F'
  obtain ⟨q, rfl⟩ : ∃ q, g' = q * (planeFaceRepr i) := ⟨g' * (planeFaceRepr i)⁻¹, by group⟩
  have hl : planeOf (planeFaceRepr i) = planeOf (q * (planeFaceRepr i)) := hF'.symm
  have hq : q * (planeFaceRepr i) * (planeFaceRepr i)⁻¹ ∈ planeBorel := (planeOf_eq_iff (planeFaceRepr i) (q * (planeFaceRepr i))).1 hl
  rw [mul_inv_cancel_right] at hq
  obtain ⟨F'', hF''⟩ := faceFlagStab_mul_left 6 (planeFaceRepr i) q hq 1
  have hone := faceFlagStab_one_map 6 (by norm_num) (q * (planeFaceRepr i))
  have hB : gammaNBAt 6 (q * (planeFaceRepr i)) = (faceFlagStab 6 (planeFaceRepr i) F'').map (gammaNPAt 6 (planeFaceRepr i)).subtype :=
    hone.symm.trans hF''
  set ι := stabLift (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
      (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant i (flagOf (q * (planeFaceRepr i))) hF' with hι
  have hmem : ∀ s, ι s ∈ faceFlagStab 6 (planeFaceRepr i) F'' := by
    intro s
    have he : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (ι s)) = s.1 :=
      emb_stabLift (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf
        TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant i (flagOf (q * (planeFaceRepr i))) hF' s
    have hs' : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (ι s)) ∈
        MulAction.stabilizer Γ6 (flagOf (q * (planeFaceRepr i))) := by
      rw [he]; exact s.2
    have h1 := (mem_stabilizer_flagOf_iff (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (ι s))
      (q * (planeFaceRepr i))).1 hs'
    rw [hB] at h1
    obtain ⟨k, hk, hkeq⟩ := h1
    have : k = ι s := Subtype.ext hkeq
    rw [← this]; exact hk
  have hnat := cmpH2_restriction ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
    (faceFlagStab 6 (planeFaceRepr i) F'').subtype x₀
  rw [hx₀ F'', map_zero] at hnat
  exact res_zero_of_factor _ _ (faceFlagStab 6 (planeFaceRepr i) F'').subtype ι (ι.codRestrict _ hmem) (fun s => rfl)
    hnat


/-- **The restriction of a mixed class of the plane group to the stabilizer of a complete flag over the plane vanishes.** -/
theorem planeMixedDual_hx (i : PlaneFaces 6)
    (x₀ : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx₀ : ∀ F : GL (Fin 2) ℚ, twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr i) F).subtype
      (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) x₀ = 0)
    (F' : Flag) (hF' : flagPlaneOf F' = planeOf (planeFaceRepr i)) :
    twoCohomologyRestriction (stabLift (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
      (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant i F' hF')
      (Rep.res (planeEmb (planeFaceRepr i)) (Rep.of (rep6 ρ).dual))
      (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x₀) = 0 := by
  obtain ⟨g', rfl⟩ := exists_flagOf F'
  obtain ⟨q, rfl⟩ : ∃ q, g' = q * (planeFaceRepr i) := ⟨g' * (planeFaceRepr i)⁻¹, by group⟩
  have hl : planeOf (planeFaceRepr i) = planeOf (q * (planeFaceRepr i)) := hF'.symm
  have hq : q * (planeFaceRepr i) * (planeFaceRepr i)⁻¹ ∈ planeBorel := (planeOf_eq_iff (planeFaceRepr i) (q * (planeFaceRepr i))).1 hl
  rw [mul_inv_cancel_right] at hq
  obtain ⟨F'', hF''⟩ := faceFlagStab_mul_left 6 (planeFaceRepr i) q hq 1
  have hone := faceFlagStab_one_map 6 (by norm_num) (q * (planeFaceRepr i))
  have hB : gammaNBAt 6 (q * (planeFaceRepr i)) = (faceFlagStab 6 (planeFaceRepr i) F'').map (gammaNPAt 6 (planeFaceRepr i)).subtype :=
    hone.symm.trans hF''
  set ι := stabLift (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
      (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant i (flagOf (q * (planeFaceRepr i))) hF' with hι
  have hmem : ∀ s, ι s ∈ faceFlagStab 6 (planeFaceRepr i) F'' := by
    intro s
    have he : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (ι s)) = s.1 :=
      emb_stabLift (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf
        TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant i (flagOf (q * (planeFaceRepr i))) hF' s
    have hs' : gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (ι s)) ∈
        MulAction.stabilizer Γ6 (flagOf (q * (planeFaceRepr i))) := by
      rw [he]; exact s.2
    have h1 := (mem_stabilizer_flagOf_iff (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (ι s))
      (q * (planeFaceRepr i))).1 hs'
    rw [hB] at h1
    obtain ⟨k, hk, hkeq⟩ := h1
    have : k = ι s := Subtype.ext hkeq
    rw [← this]; exact hk
  have hnat := cmpH2Dual_restriction ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
    (faceFlagStab 6 (planeFaceRepr i) F'').subtype x₀
  rw [hx₀ F'', map_zero] at hnat
  exact res_zero_of_factor _ _ (faceFlagStab 6 (planeFaceRepr i) F'').subtype ι (ι.codRestrict _ hmem) (fun s => rfl)
    hnat

end Concrete

end TernaryPeriodPolynomials.Argument.GammaNStokes
