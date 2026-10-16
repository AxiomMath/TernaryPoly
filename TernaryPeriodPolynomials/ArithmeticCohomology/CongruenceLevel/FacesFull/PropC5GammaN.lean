module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineLemmaC3
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FlagDictionary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RestrictionComposition

@[expose] public section


/-!
# Global classes of `Γ(N)`: zero flag restrictions, mixed cuspidal face restrictions, and Proposition C.5 at level `Γ(N)`

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.

* `gammaNRepAll`, `rLine`, `rPlane`, `rFlag`, `ZeroFlags`: a global class of `H²(Γ(N), E_n)`, its restrictions to the line groups, plane groups and
  flag groups `Γ(N) ∩ g⁻¹ B g` (`r_Q`, `r_P`, `r_B`);
* `zeroFlags_line_mixed`, `zeroFlags_plane_mixed`, `zeroFlags_of_line_mixed`, `zeroFlags_iff_mixed`: **nonmixed exclusion for global classes**: zero
  flag restrictions `⟺` all maximal-face restrictions are mixed cuspidal (`N ≥ 3`; uses the flag dictionary `FlagDictionary` and the
  Hochschild-Serre identification `lineFaceCuspidalInH2 = lineLocallyInner`);
* `planeBoundary`, `lineBoundary`, `exists_coordinates`: the coordinates `(ξ_P, ξ_Q)` of such a class in `𝒞_P(E) = ⨁ 𝒞_{P'}(E)`, `𝒞_Q(E)`;
* `PropC5GammaN`: **the general `Γ(N)` statement of Proposition C.5**;
* `GammaNC5Obligations`, `propC5_gammaN_of_obligations`: the paper's proof, reduced to four exact analytic inputs at level `Γ(N)` (Eisenstein
  classes `ℰ_P`, dual classes `ℰ_Q^∨`, Stokes with the `Γ(N)` face pairings, perfect line pairing), recorded as structure fields.
-/

open CategoryTheory
open scoped MatrixGroups DirectSum

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section Global

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The coefficient module `E_n` restricted to the neat principal congruence subgroup `Γ(N)`. -/
def gammaNRepAll : Rep ℂ (gammaN N) := Rep.of ((ambRep n).comp (gammaN N).subtype)

omit [NeZero N] in
theorem gammaNBAt_le_gammaN (g : SL(3, ℤ)) : gammaNBAt N g ≤ gammaN N := by
  intro p hp
  have hq : g * p * g⁻¹ ∈ gammaN N := (Subgroup.mem_inf.mp hp).1
  have := (gammaN_normal N).conj_mem _ hq g⁻¹
  simpa [mul_assoc] using this

/-- Restriction of a global degree-two class of `Γ(N)` to the line group of the line cusp `h⁻¹Qh`. -/
def rLine (h : SL(3, ℤ)) :
    groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] groupCohomology.H2 (lineFaceRep N h n) :=
  twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAll N n)

/-- Restriction of a global degree-two class of `Γ(N)` to the plane group of the plane cusp `h⁻¹Ph`. -/
def rPlane (h : SL(3, ℤ)) :
    groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] groupCohomology.H2 (faceRep N h n) :=
  twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (gammaNRepAll N n)

/-- Restriction of a global degree-two class of `Γ(N)` to the flag group `Γ(N) ∩ g⁻¹ B g`. -/
def rFlag (g : SL(3, ℤ)) :
    groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] groupCohomology.H2 (flagRep N g n) :=
  twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (gammaNRepAll N n)

/-- **Zero flag restrictions** (`r_B c = 0`): the class restricts to zero on the stabilizer `Γ(N) ∩ g⁻¹ B g` of every rational complete
flag (every complete flag is `g⁻¹` times the standard one for an integral `g`). -/
def ZeroFlags (c : groupCohomology.H2 (gammaNRepAll N n)) : Prop := ∀ g : SL(3, ℤ), rFlag N n g c = 0

/-- Restricting a class of `H²(G, ρ)` along `ι : H → G` and then along `κ₀ : K → H` vanishes when the restriction along `ι_B : B → G`
vanishes and `ι ∘ κ₀` factors through `ι_B`. -/
theorem res_res_eq_zero {G H K B : Type} [Group G] [Group H] [Group K] [Group B]
    (ι : H →* G) (κ₀ : K →* H) (ιB : B →* G) (κ : K →* B) (hcomm : ι.comp κ₀ = ιB.comp κ)
    (ρ : Rep ℂ G) (y : groupCohomology.H2 ρ) (hy : twoCohomologyRestriction ιB ρ y = 0) :
    twoCohomologyRestriction κ₀ (Rep.res ι ρ) (twoCohomologyRestriction ι ρ y) = 0 := by
  have e1 := FacePairing.twoCohomologyRestriction_comp ι κ₀ ρ y
  have e2 := FacePairing.twoCohomologyRestriction_comp ιB κ ρ y
  have e3 : twoCohomologyRestriction κ (Rep.res ιB ρ) (twoCohomologyRestriction ιB ρ y) = 0 := by
    rw [hy, map_zero]
  have key : ∀ (f g : K →* G), f = g → twoCohomologyRestriction g ρ y = 0 →
      twoCohomologyRestriction f ρ y = 0 := by
    rintro f g rfl hz
    exact hz
  have h0 := key _ _ hcomm (e2.trans e3)
  exact e1.symm.trans h0

/-- **Nonmixed face components are excluded at the line cusps of `Γ(N)`**: a global class with zero flag restrictions has,
at every line cusp `h⁻¹Qh`, a face restriction lying in the image `lineFaceCuspidalInH2` of the mixed cuspidal group. -/
theorem zeroFlags_line_mixed (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (h : SL(3, ℤ)) : rLine N n h c ∈ lineFaceCuspidalInH2 N h n := by
  rw [lineFaceCuspidalInH2_eq_locallyInner, lineLocallyInner_eq_iInf]
  refine Submodule.mem_iInf _ |>.mpr fun F => ?_
  obtain ⟨g, hg⟩ := lineFlagStab_map_exists_gammaNBAt N hN h F
  rw [LinearMap.mem_ker]
  have hmem : ∀ k : lineFlagStab N h F, ((k : gammaNQAt N h) : SL(3, ℤ)) ∈ gammaNBAt N (blockDiagQ g⁻¹ * h) := by
    intro k
    rw [← hg]
    exact ⟨k.1, k.2, rfl⟩
  let κ : lineFlagStab N h F →* gammaNBAt N (blockDiagQ g⁻¹ * h) :=
    ((gammaNQAt N h).subtype.comp (lineFlagStab N h F).subtype).codRestrict _ hmem
  exact res_res_eq_zero (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp))
    (lineFlagStab N h F).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN N (blockDiagQ g⁻¹ * h))) κ
    (by ext; rfl) (gammaNRepAll N n) c (hz _)

/-- The same at the plane cusps of `Γ(N)`. -/
theorem zeroFlags_plane_mixed (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (h : SL(3, ℤ)) : rPlane N n h c ∈ faceCuspidalInH2 N h n := by
  rw [faceCuspidalInH2_eq_locallyInner, faceLocallyInner_eq_iInf]
  refine Submodule.mem_iInf _ |>.mpr fun F => ?_
  obtain ⟨g, hg⟩ := faceFlagStab_map_exists_gammaNBAt N hN h F
  rw [LinearMap.mem_ker]
  have hmem : ∀ k : faceFlagStab N h F, ((k : gammaNPAt N h) : SL(3, ℤ)) ∈ gammaNBAt N (blockDiag g⁻¹ * h) := by
    intro k
    rw [← hg]
    exact ⟨k.1, k.2, rfl⟩
  let κ : faceFlagStab N h F →* gammaNBAt N (blockDiag g⁻¹ * h) :=
    ((gammaNPAt N h).subtype.comp (faceFlagStab N h F).subtype).codRestrict _ hmem
  exact res_res_eq_zero (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp))
    (faceFlagStab N h F).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN N (blockDiag g⁻¹ * h))) κ
    (by ext; rfl) (gammaNRepAll N n) c (hz _)

/-- Converse of `res_res_eq_zero`: if the double restriction along `ι` then `κ₀` vanishes and `ι_B` factors through `ι ∘ κ₀`, the restriction
along `ι_B` vanishes. -/
theorem res_eq_zero_of_res_res {G H K B : Type} [Group G] [Group H] [Group K] [Group B]
    (ι : H →* G) (κ₀ : K →* H) (ιB : B →* G) (κ : B →* K) (hcomm : ιB = (ι.comp κ₀).comp κ)
    (ρ : Rep ℂ G) (y : groupCohomology.H2 ρ)
    (hy : twoCohomologyRestriction κ₀ (Rep.res ι ρ) (twoCohomologyRestriction ι ρ y) = 0) :
    twoCohomologyRestriction ιB ρ y = 0 := by
  have e1 := FacePairing.twoCohomologyRestriction_comp ι κ₀ ρ y
  have e2 := FacePairing.twoCohomologyRestriction_comp (ι.comp κ₀) κ ρ y
  have e3 : twoCohomologyRestriction κ (Rep.res (ι.comp κ₀) ρ) (twoCohomologyRestriction (ι.comp κ₀) ρ y) = 0 := by
    rw [e1, hy, map_zero]
  have key : ∀ (f g : B →* G), f = g → twoCohomologyRestriction g ρ y = 0 →
      twoCohomologyRestriction f ρ y = 0 := by
    rintro f g rfl hz
    exact hz
  exact key _ _ hcomm (e2.trans e3)

/-- **Mixed cuspidal maximal-face restrictions**: at every line cusp and every plane cusp the face restriction of the class lies in the image
of the mixed cuspidal group. -/
def MixedCuspidalRestrictions (c : groupCohomology.H2 (gammaNRepAll N n)) : Prop :=
  (∀ h : SL(3, ℤ), rLine N n h c ∈ lineFaceCuspidalInH2 N h n) ∧
    ∀ h : SL(3, ℤ), rPlane N n h c ∈ faceCuspidalInH2 N h n

/-- Mixed cuspidal line restrictions force zero restriction to every flag group. -/
theorem zeroFlags_of_line_mixed (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n))
    (hm : ∀ h : SL(3, ℤ), rLine N n h c ∈ lineFaceCuspidalInH2 N h n) : ZeroFlags N n c := by
  intro g
  have h1 := hm g
  rw [lineFaceCuspidalInH2_eq_locallyInner, lineLocallyInner_eq_iInf] at h1
  have h2 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h1 1)
  have himg := lineFlagStab_one_map N hN g
  let e : lineFlagStab N g 1 ≃* (lineFlagStab N g 1).map (gammaNQAt N g).subtype :=
    Subgroup.equivMapOfInjective _ _ (gammaNQAt N g).subtype_injective
  let e2 : (lineFlagStab N g 1).map (gammaNQAt N g).subtype ≃* gammaNBAt N g := MulEquiv.subgroupCongr himg
  let κ : gammaNBAt N g →* lineFlagStab N g 1 := (e.trans e2).symm.toMonoidHom
  exact res_eq_zero_of_res_res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N g hp))
    (lineFlagStab N g 1).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) κ
    (MonoidHom.ext fun b => by
      apply Subtype.ext
      change (b : SL(3, ℤ)) = (((e.trans e2).symm b : lineFlagStab N g 1) : SL(3, ℤ))
      have := (e.trans e2).apply_symm_apply b
      exact (congrArg (fun x : gammaNBAt N g => (x : SL(3, ℤ))) this).symm)
    (gammaNRepAll N n) c h2

theorem zeroFlags_iff_mixed (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n)) :
    ZeroFlags N n c ↔ MixedCuspidalRestrictions N n c :=
  ⟨fun hz => ⟨zeroFlags_line_mixed N n hN c hz, zeroFlags_plane_mixed N n hN c hz⟩,
    fun hm => zeroFlags_of_line_mixed N n hN c hm.1⟩

/-- The boundary vector of plane restrictions of a global class, at the chosen representatives of the plane faces. -/
def planeBoundary : groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] PlaneFaceH2 N n :=
  ∑ i : PlaneFaces N, (DirectSum.lof ℂ (PlaneFaces N)
    (fun i => groupCohomology.H2 (faceRep N (planeFaceRepr i) n)) i).comp (rPlane N n (planeFaceRepr i))

/-- The boundary vector of line restrictions of a global class, at the chosen representatives of the line faces. -/
def lineBoundary : groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] LineFaceH2 N n :=
  ∑ i : LineFaces N, (DirectSum.lof ℂ (LineFaces N)
    (fun i => groupCohomology.H2 (lineFaceRep N i.rep n)) i).comp (rLine N n i.rep)

theorem planeBoundary_apply (c : groupCohomology.H2 (gammaNRepAll N n)) (i : PlaneFaces N) :
    planeBoundary N n c i = rPlane N n (planeFaceRepr i) c := by
  simp only [planeBoundary, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply]
  simp [DirectSum.of_apply]

theorem lineBoundary_apply (c : groupCohomology.H2 (gammaNRepAll N n)) (i : LineFaces N) :
    lineBoundary N n c i = rLine N n i.rep c := by
  simp only [lineBoundary, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply]
  simp [DirectSum.of_apply]

/-- **A class with mixed cuspidal maximal-face restrictions has coordinates `(ξ_P, ξ_Q)`** in the direct sums `𝒞_P(E)`, `𝒞_Q(E)`
(the restrictions to the chosen representatives of the faces, read through the Hochschild-Serre injections). -/
theorem exists_coordinates (c : groupCohomology.H2 (gammaNRepAll N n)) (hm : MixedCuspidalRestrictions N n c) :
    (∃ ξP : PlaneCuspSum N n, planeCuspSumEmbedding N n ξP = planeBoundary N n c) ∧
      ∃ ξQ : LineCuspSum N n, lineCuspSumEmbedding N n ξQ = lineBoundary N n c := by
  refine ⟨?_, ?_⟩
  · have := (mem_range_planeCuspSumEmbedding N n (planeBoundary N n c)).mpr (fun i => by
      rw [planeBoundary_apply]; exact hm.2 _)
    exact this
  · have := (mem_range_lineCuspSumEmbedding N n (lineBoundary N n c)).mpr (fun i => by
      rw [lineBoundary_apply]; exact hm.1 _)
    exact this

/-- **The general `Γ(N)` statement of Proposition C.5 (`ar:prop:graph`), in the appendix's convention** (neat `Γ(N)`,
`3 ∣ N`; the finite covering group is averaged at the end and is **not** part of this statement).  There is a linear map `T : 𝒞_P(E) → 𝒞_Q(E)`
(the constant term) such that (a) every `ξ ∈ 𝒞_P(E)` is the plane restriction of a global degree-two class of `Γ(N)` with zero flag
restrictions whose line restriction is `Tξ`, and (b) every global class with mixed cuspidal maximal-face restrictions `(ξ_P, ξ_Q)` and zero
flag restrictions has `ξ_Q = T ξ_P`. -/
def PropC5GammaN : Prop :=
  ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
    (∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
      planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
        lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c) ∧
    ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
      ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
        planeCuspSumEmbedding N n ξP = planeBoundary N n c →
        lineCuspSumEmbedding N n ξQ = lineBoundary N n c → ξQ = T ξP

/-- **The exact analytic inputs of the paper's proof of Proposition C.5 at level `Γ(N)`**, recorded as the fields of a structure
(`PD`, `QD` stand for the dual mixed cuspidal groups `𝒞_P(E*)`, `𝒞_Q(E*)` and `Hd` for the global classes with coefficients `E*`
that are admissible for the Stokes pairing, i.e. with zero flag restrictions and mixed cuspidal face restrictions):

* `eisensteinP` (`ar:eq:constantterms`): the constant-term map `T` and, for every `ξ ∈ 𝒞_P(E)`, a global class `ℰ_P(ξ)` of `Γ(N)` with zero
  flag restrictions, plane restriction `ξ` and line restriction `Tξ` (needs the convergent Eisenstein series and its restriction identities
  at level `Γ(N)`; `Revision/Exports/EisensteinClass`, `EisensteinConstantTerm`);
* `dualEisenstein` (`ar:eq:dualconstantterms`): for every `η ∈ 𝒞_Q(E*)` a dual class `ℰ_Q^∨(η)` with line restriction `η` and plane
  restriction `T^∨ η`;
* `stokes` (Lemma `ar:lem:stokes`): `⟨ξ_P, ξ'_P⟩_P + ⟨ξ_Q, ξ'_Q⟩_Q = 0` for a global class with coefficients `E` and a dual global class,
  both with zero flag restrictions (the face pairings of `Γ(N)`, `pairP`, `pairQ`);
* `perfectQ` (`ar:eq:facepair`, `R = Q`): the line pairing of `Γ(N)` is nondegenerate in the first argument.

None of these four statements exists in the library at level `Γ(N)`: the `K†`-level counterparts are `constant_terms`, `dual_constant_terms_jmath`,
`global_stokes_glue`/`paper_stokes` and `facePairing_perfect_all`, which are statements for `rationalLevel` and do not imply the `Γ(N)` ones
(a `Γ(N)`-class is not `K†`-invariant). -/
structure GammaNC5Obligations (PD QD Hd : Type) [AddCommGroup PD] [Module ℂ PD] [AddCommGroup QD] [Module ℂ QD]
    [AddCommGroup Hd] [Module ℂ Hd] where
  T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n
  eisensteinP : ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
      planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
        lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c
  Td : QD →ₗ[ℂ] PD
  rPd : Hd →ₗ[ℂ] PD
  rQd : Hd →ₗ[ℂ] QD
  pairP : PlaneCuspSum N n →ₗ[ℂ] PD →ₗ[ℂ] ℂ
  pairQ : LineCuspSum N n →ₗ[ℂ] QD →ₗ[ℂ] ℂ
  dualEisenstein : ∀ η : QD, ∃ c' : Hd, rQd c' = η ∧ rPd c' = Td η
  stokes : ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
    ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
      planeCuspSumEmbedding N n ξP = planeBoundary N n c →
      lineCuspSumEmbedding N n ξQ = lineBoundary N n c →
      ∀ c' : Hd, pairP ξP (rPd c') + pairQ ξQ (rQd c') = 0
  perfectQ : ∀ ξQ : LineCuspSum N n, (∀ η : QD, pairQ ξQ η = 0) → ξQ = 0

/-- **Proposition C.5 at level `Γ(N)` from the paper's four inputs**: pair the class with `ℰ_Q^∨(η)` in the Stokes lemma, pair
`ℰ_P(ξ_P)` with the same dual class, subtract, and use the perfect line pairing. -/
theorem propC5_gammaN_of_obligations {PD QD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup QD] [Module ℂ QD]
    [AddCommGroup Hd] [Module ℂ Hd] (O : GammaNC5Obligations N n PD QD Hd) : PropC5GammaN N n := by
  refine ⟨O.T, O.eisensteinP, ?_⟩
  intro c hz ξP ξQ hP hQ
  obtain ⟨cP, hzP, hPP, hPQ⟩ := O.eisensteinP ξP
  have hdiff : ξQ - O.T ξP = 0 := by
    apply O.perfectQ
    intro η
    obtain ⟨c', hQ', hP'⟩ := O.dualEisenstein η
    have s1 := O.stokes c hz ξP ξQ hP hQ c'
    have s2 := O.stokes cP hzP ξP (O.T ξP) hPP hPQ c'
    rw [hQ', hP'] at s1 s2
    have : O.pairQ (ξQ - O.T ξP) η = 0 := by
      rw [map_sub, LinearMap.sub_apply]
      have := sub_eq_zero.mpr (s1.trans s2.symm)
      simpa using this
    exact this
  exact sub_eq_zero.mp hdiff

end Global

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
