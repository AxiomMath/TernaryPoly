module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.C5Reduction
public import TernaryPeriodPolynomials.BoundaryComparison.LevelTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge

@[expose] public section


/-!
# Level change `Γ(M) → Γ(N)` for the uniqueness clause of Proposition C.5

Formalized by Claude Sonnet 5.5.

For `N ∣ M` (so `Γ(M) ⊂ Γ(N)`), the uniqueness clause `UniqLevel` of Proposition C.5 ("a global class with zero flag restrictions and zero plane
restrictions has zero line restrictions", which is the case `ξ_P = 0` of the printed statement, `uniqLevel_of_propC5`) descends from `Γ(M)` to `Γ(N)`
(`uniqLevel_of_dvd`) by restriction to the deeper level: zero flag restrictions are preserved (`zeroFlags_resLevel`), vanishing of a face restriction is a
property of the face (`rPlane_zero_of_rel`, `rLine_zero_of_rel`, from the `res_conj`: inner automorphisms act trivially on `H²`), restriction
to the finite-index face group of level `M` is injective on `H²(-, E_n)` (`resLine_injective`, `resPlane_injective`, from the level-transfer
isomorphism `H²(S, ρ) ≅ H²(K, ρ)^{S/K}` `Statements.LevelTransfer`).  No face pairing and no Stokes lemma at level `N` is needed.
`propC5_of_uniq`: uniqueness at `N` plus Eisenstein existence at `N` (field `eisensteinP`) is `PropC5GammaN N n`; `propC5_of_obligations_at_level`:
the four analytic inputs at a common level `M` (where the `Γ(6)`-Stokes lemma applies, `6 ∣ M`) and Eisenstein existence at `N` give `PropC5GammaN N n`.
-/

open CategoryTheory
open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem gammaN_mono {N M : ℕ} (h : N ∣ M) : gammaN M ≤ gammaN N := by
  intro γ hγ
  rw [mem_gammaN] at hγ ⊢
  exact fun i j => (Int.natCast_dvd_natCast.mpr h).trans (hγ i j)

theorem gammaNBAt_mono {N M : ℕ} (h : N ∣ M) (g : SL(3, ℤ)) : gammaNBAt M g ≤ gammaNBAt N g := by
  intro p hp
  have h1 : g * p * g⁻¹ ∈ gammaNB M := hp
  show g * p * g⁻¹ ∈ gammaNB N
  exact ⟨gammaN_mono h h1.1, h1.2⟩

theorem gammaNQAt_mono {N M : ℕ} (h : N ∣ M) (g : SL(3, ℤ)) : gammaNQAt M g ≤ gammaNQAt N g := by
  intro p hp
  have h1 : g * p * g⁻¹ ∈ gammaNQ M := hp
  show g * p * g⁻¹ ∈ gammaNQ N
  exact ⟨gammaN_mono h h1.1, h1.2⟩

theorem gammaNPAt_mono {N M : ℕ} (h : N ∣ M) (g : SL(3, ℤ)) : gammaNPAt M g ≤ gammaNPAt N g := by
  intro p hp
  have h1 : g * p * g⁻¹ ∈ gammaNP M := hp
  show g * p * g⁻¹ ∈ gammaNP N
  exact ⟨gammaN_mono h h1.1, h1.2⟩

variable (N M n : ℕ)

/-- Restriction of a global class of `Γ(N)` to the deeper level `Γ(M)`, `N ∣ M`. -/
def resLevel (h : N ∣ M) : groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] groupCohomology.H2 (gammaNRepAll M n) :=
  twoCohomologyRestriction (Subgroup.inclusion (gammaN_mono h)) (gammaNRepAll N n)

/-- **Zero flag restrictions are preserved by restriction to a deeper level.** -/
theorem zeroFlags_resLevel (h : N ∣ M) (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c) :
    ZeroFlags M n (resLevel N M n h c) := by
  intro g
  exact res_res_eq_zero (Subgroup.inclusion (gammaN_mono h)) (Subgroup.inclusion (gammaNBAt_le_gammaN M g))
    (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (Subgroup.inclusion (gammaNBAt_mono h g)) (by ext; rfl)
    (gammaNRepAll N n) c (hz g)

open TernaryPeriodPolynomials.Argument.GammaNStokes (res_conj innerConj_hT)

/-- **Vanishing of a line-face restriction is a property of the face**: if the restriction of a global class of `Γ(N)` to the line group of
`h⁻¹Qh` vanishes, so does its restriction at every `h' = q h γ` (`q ∈ Q(ℤ)`, `γ ∈ Γ(N)`). -/
theorem rLine_zero_of_rel {N n : ℕ} [NeZero N] {h h' : SL(3, ℤ)} (hrel : (lineFaceSetoid N).r h h')
    (c : groupCohomology.H2 (gammaNRepAll N n)) (h0 : rLine N n h c = 0) : rLine N n h' c = 0 := by
  obtain ⟨q, hq, γ, hγ, rfl⟩ := hrel
  let g : gammaN N := ⟨γ, hγ⟩
  have hmem : ∀ s : gammaNQAt N (q * h * γ), γ * (s : SL(3, ℤ)) * γ⁻¹ ∈ gammaNQAt N h := by
    intro s
    rw [← gammaNQAt_mul_left N h q hq, mem_gammaNQAt]
    have := s.2
    rw [mem_gammaNQAt] at this
    have e : q * h * (γ * (s : SL(3, ℤ)) * γ⁻¹) * (q * h)⁻¹ = q * h * γ * (s : SL(3, ℤ)) * (q * h * γ)⁻¹ := by group
    rw [e]; exact this
  let φ : gammaNQAt N (q * h * γ) →* gammaNQAt N h :=
    { toFun := fun s => ⟨γ * (s : SL(3, ℤ)) * γ⁻¹, hmem s⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have key := res_conj (gammaNRepAll N n) g (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N (q * h * γ) hp)) φ
    (fun s => Subtype.ext rfl)
    (fun s v => by
      have := innerConj_hT (gammaNRepAll N n) g (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N (q * h * γ) hp) s) v
      exact this) c
  have h1 : twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAll N n) c = 0 := h0
  rw [h1, map_zero] at key
  exact key.symm

/-- **Vanishing of a plane-face restriction is a property of the face**: if the restriction of a global class of `Γ(N)` to the line group of
`h⁻¹Qh` vanishes, so does its restriction at every `h' = q h γ` (`q ∈ P(ℤ)`, `γ ∈ Γ(N)`). -/
theorem rPlane_zero_of_rel {N n : ℕ} [NeZero N] {h h' : SL(3, ℤ)} (hrel : (planeFaceSetoid N).r h h')
    (c : groupCohomology.H2 (gammaNRepAll N n)) (h0 : rPlane N n h c = 0) : rPlane N n h' c = 0 := by
  obtain ⟨q, hq, γ, hγ, rfl⟩ := hrel
  let g : gammaN N := ⟨γ, hγ⟩
  have hmem : ∀ s : gammaNPAt N (q * h * γ), γ * (s : SL(3, ℤ)) * γ⁻¹ ∈ gammaNPAt N h := by
    intro s
    rw [← gammaNPAt_mul_left N h q hq, mem_gammaNPAt]
    have := s.2
    rw [mem_gammaNPAt] at this
    have e : q * h * (γ * (s : SL(3, ℤ)) * γ⁻¹) * (q * h)⁻¹ = q * h * γ * (s : SL(3, ℤ)) * (q * h * γ)⁻¹ := by group
    rw [e]; exact this
  let φ : gammaNPAt N (q * h * γ) →* gammaNPAt N h :=
    { toFun := fun s => ⟨γ * (s : SL(3, ℤ)) * γ⁻¹, hmem s⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have key := res_conj (gammaNRepAll N n) g (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N (q * h * γ) hp)) φ
    (fun s => Subtype.ext rfl)
    (fun s v => by
      have := innerConj_hT (gammaNRepAll N n) g (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N (q * h * γ) hp) s) v
      exact this) c
  have h1 : twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N h hp)) (gammaNRepAll N n) c = 0 := h0
  rw [h1, map_zero] at key
  exact key.symm

section Injective

open TernaryPeriodPolynomials.Argument.LevelTransfer

/-- **Restriction to a finite-index subgroup is injective on `H²(-, E_n)`** (Mathlib's `groupCohomology`, degree two), for a subgroup `K ≤ S` of
`SL₃(ℤ)` normalized by `S` with `S/K` finite. -/
theorem res_injective_of_finite {S K : Subgroup SL(3, ℤ)} (hKS : K ≤ S) (hnorm : ∀ s ∈ S, ∀ k ∈ K, s⁻¹ * k * s ∈ K)
    [Fintype (S ⧸ K.subgroupOf S)] (n : ℕ) :
    Function.Injective (twoCohomologyRestriction (Subgroup.inclusion hKS) (Rep.of ((ambRep n).comp S.subtype))) := by
  have hM : twoCohomologyRestriction (Subgroup.inclusion hKS) (Rep.of ((ambRep n).comp S.subtype)) =
      resMathlib (ambRep n) hKS := rfl
  rw [hM]
  intro y y' hyy
  obtain ⟨x, rfl⟩ := (bridge (ambRep n) S).surjective y
  obtain ⟨x', rfl⟩ := (bridge (ambRep n) S).surjective y'
  have h1 : resMathlib (ambRep n) hKS (bridge (ambRep n) S x) = bridge (ambRep n) K (resH2 (ambRep n) hKS x) :=
    bridge_res (ambRep n) hKS x
  have h2 : resMathlib (ambRep n) hKS (bridge (ambRep n) S x') = bridge (ambRep n) K (resH2 (ambRep n) hKS x') :=
    bridge_res (ambRep n) hKS x'
  have h3 : bridge (ambRep n) K (resH2 (ambRep n) hKS x) = bridge (ambRep n) K (resH2 (ambRep n) hKS x') :=
    h1.symm.trans (hyy.trans h2)
  rw [resH2_injective (ambRep n) hKS hnorm ((bridge (ambRep n) K).injective h3)]

end Injective

section FaceInjective

variable {N M : ℕ} (hNM : N ∣ M) (n : ℕ) (h : SL(3, ℤ))

theorem gammaNQAt_normalized (s : SL(3, ℤ)) (hs : s ∈ gammaNQAt N h) (k : SL(3, ℤ)) (hk : k ∈ gammaNQAt M h) :
    s⁻¹ * k * s ∈ gammaNQAt M h := by
  rw [mem_gammaNQAt] at hs hk ⊢
  have e : h * (s⁻¹ * k * s) * h⁻¹ = (h * s * h⁻¹)⁻¹ * (h * k * h⁻¹) * (h * s * h⁻¹) := by group
  rw [e]
  refine ⟨?_, lineStab.mul_mem (lineStab.mul_mem (lineStab.inv_mem hs.2) hk.2) hs.2⟩
  have := (gammaN_normal M).conj_mem _ hk.1 (h * s * h⁻¹)⁻¹
  simpa using this

theorem gammaNPAt_normalized (s : SL(3, ℤ)) (hs : s ∈ gammaNPAt N h) (k : SL(3, ℤ)) (hk : k ∈ gammaNPAt M h) :
    s⁻¹ * k * s ∈ gammaNPAt M h := by
  rw [mem_gammaNPAt] at hs hk ⊢
  have e : h * (s⁻¹ * k * s) * h⁻¹ = (h * s * h⁻¹)⁻¹ * (h * k * h⁻¹) * (h * s * h⁻¹) := by group
  rw [e]
  refine ⟨?_, planeStab.mul_mem (planeStab.mul_mem (planeStab.inv_mem hs.2) hk.2) hs.2⟩
  have := (gammaN_normal M).conj_mem _ hk.1 (h * s * h⁻¹)⁻¹
  simpa using this

theorem gammaNQAt_finiteIndex [NeZero M] : ((gammaNQAt M h).subgroupOf (gammaNQAt N h)).FiniteIndex := by
  have hle : (gammaN M).subgroupOf (gammaNQAt N h) ≤ (gammaNQAt M h).subgroupOf (gammaNQAt N h) := by
    intro s hs
    have hs' : (s : SL(3, ℤ)) ∈ gammaN M := hs
    have hs2 : (s : SL(3, ℤ)) ∈ gammaNQAt N h := s.2
    rw [mem_gammaNQAt] at hs2
    show (s : SL(3, ℤ)) ∈ gammaNQAt M h
    rw [mem_gammaNQAt]
    exact ⟨(gammaN_normal M).conj_mem _ hs' h, hs2.2⟩
  have : ((gammaN M).subgroupOf (gammaNQAt N h)).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le hle

theorem gammaNPAt_finiteIndex [NeZero M] : ((gammaNPAt M h).subgroupOf (gammaNPAt N h)).FiniteIndex := by
  have hle : (gammaN M).subgroupOf (gammaNPAt N h) ≤ (gammaNPAt M h).subgroupOf (gammaNPAt N h) := by
    intro s hs
    have hs' : (s : SL(3, ℤ)) ∈ gammaN M := hs
    have hs2 : (s : SL(3, ℤ)) ∈ gammaNPAt N h := s.2
    rw [mem_gammaNPAt] at hs2
    show (s : SL(3, ℤ)) ∈ gammaNPAt M h
    rw [mem_gammaNPAt]
    exact ⟨(gammaN_normal M).conj_mem _ hs' h, hs2.2⟩
  have : ((gammaN M).subgroupOf (gammaNPAt N h)).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le hle

/-- Restriction of `H²(Γ_{h⁻¹Qh}(N), E_n)` to the line group of level `M` is injective. -/
theorem resLine_injective [NeZero M] :
    Function.Injective (twoCohomologyRestriction (Subgroup.inclusion (gammaNQAt_mono hNM h)) (lineFaceRep N h n)) := by
  have := gammaNQAt_finiteIndex (N := N) (M := M) h
  let : Fintype (gammaNQAt N h ⧸ (gammaNQAt M h).subgroupOf (gammaNQAt N h)) := Fintype.ofFinite _
  exact res_injective_of_finite (gammaNQAt_mono hNM h) (gammaNQAt_normalized h) n

/-- Restriction of `H²(Γ_{h⁻¹Ph}(N), E_n)` to the plane group of level `M` is injective. -/
theorem resPlane_injective [NeZero M] :
    Function.Injective (twoCohomologyRestriction (Subgroup.inclusion (gammaNPAt_mono hNM h)) (faceRep N h n)) := by
  have := gammaNPAt_finiteIndex (N := N) (M := M) h
  let : Fintype (gammaNPAt N h ⧸ (gammaNPAt M h).subgroupOf (gammaNPAt N h)) := Fintype.ofFinite _
  exact res_injective_of_finite (gammaNPAt_mono hNM h) (gammaNPAt_normalized h) n

end FaceInjective

section Descent

open TernaryPeriodPolynomials.Argument.FacePairing (twoCohomologyRestriction_comp)

theorem res_res_heq {G H K B : Type} [Group G] [Group H] [Group K] [Group B]
    (ι : H →* G) (κ₀ : K →* H) (ιB : B →* G) (κ : K →* B) (hcomm : ι.comp κ₀ = ιB.comp κ)
    (ρ : Rep ℂ G) (y : groupCohomology.H2 ρ) :
    HEq (twoCohomologyRestriction κ₀ (Rep.res ι ρ) (twoCohomologyRestriction ι ρ y))
      (twoCohomologyRestriction κ (Rep.res ιB ρ) (twoCohomologyRestriction ιB ρ y)) := by
  have e1 := twoCohomologyRestriction_comp ι κ₀ ρ y
  have e2 := twoCohomologyRestriction_comp ιB κ ρ y
  have key : ∀ f g : K →* G, f = g → HEq (twoCohomologyRestriction f ρ y) (twoCohomologyRestriction g ρ y) := by
    rintro f g rfl
    exact HEq.rfl
  exact (heq_of_eq e1.symm).trans ((key _ _ hcomm).trans (heq_of_eq e2))

variable {N M : ℕ} (n : ℕ)

theorem rPlane_zero_all [NeZero N] {c : groupCohomology.H2 (gammaNRepAll N n)} (hb : planeBoundary N n c = 0)
    (h : SL(3, ℤ)) : rPlane N n h c = 0 := by
  have h0 : rPlane N n (planeFaceRepr (Quotient.mk (planeFaceSetoid N) h : PlaneFaces N)) c = 0 := by
    have := planeBoundary_apply N n c (Quotient.mk (planeFaceSetoid N) h : PlaneFaces N)
    rw [hb] at this
    exact this.symm
  exact rPlane_zero_of_rel (N := N) (n := n) (Quotient.mk_out (s := planeFaceSetoid N) h) c h0

theorem rLine_zero_all [NeZero N] {c : groupCohomology.H2 (gammaNRepAll N n)} (hb : lineBoundary N n c = 0)
    (h : SL(3, ℤ)) : rLine N n h c = 0 := by
  have h0 : rLine N n (LineFaces.mk (N := N) h).rep c = 0 := by
    have := lineBoundary_apply N n c (LineFaces.mk (N := N) h)
    rw [hb] at this
    exact this.symm
  exact rLine_zero_of_rel (N := N) (n := n) ((lineFaceSetoid N).iseqv.symm (LineFaces.rel_rep h)) c h0

/-- The uniqueness clause of Proposition C.5 at level `Γ(N)`: a global class with zero flag restrictions and vanishing plane restrictions has
vanishing line restrictions. -/
def UniqLevel (N n : ℕ) [NeZero N] : Prop :=
  ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c → planeBoundary N n c = 0 → lineBoundary N n c = 0

/-- **Level descent of the uniqueness clause**: `UniqLevel M n → UniqLevel N n` for `N ∣ M`.  (Restrict to `Γ(M)`; zero plane restrictions and zero
flags are preserved; the hypothesis at level `M` gives zero line restrictions of the restricted class; restriction to the finite-index line
group of level `M` is injective.) -/
theorem uniqLevel_of_dvd [NeZero N] [NeZero M] (hNM : N ∣ M) (hU : UniqLevel M n) : UniqLevel N n := by
  intro c hz hP
  set c' := resLevel N M n hNM c with hc'
  have hz' : ZeroFlags M n c' := zeroFlags_resLevel N M n hNM c hz
  have hP' : planeBoundary M n c' = 0 := by
    refine DFinsupp.ext (fun j => ?_)
    rw [planeBoundary_apply]
    have hzero : twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N (planeFaceRepr j) hp))
        (gammaNRepAll N n) c = 0 := rPlane_zero_all n hP (planeFaceRepr j)
    exact res_res_eq_zero (Subgroup.inclusion (gammaN_mono hNM))
      (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr j) hp))
      (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N (planeFaceRepr j) hp))
      (Subgroup.inclusion (gammaNPAt_mono hNM (planeFaceRepr j))) (by ext; rfl) (gammaNRepAll N n) c hzero
  have hL' := hU c' hz' hP'
  refine DFinsupp.ext (fun i => ?_)
  rw [lineBoundary_apply]
  show rLine N n i.rep c = 0
  apply resLine_injective hNM n i.rep
  rw [map_zero]
  have h1 := rLine_zero_all n hL' i.rep
  have h2 := res_res_heq (Subgroup.inclusion (gammaN_mono hNM))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i.rep hp))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N i.rep hp))
    (Subgroup.inclusion (gammaNQAt_mono hNM i.rep)) (by ext; rfl) (gammaNRepAll N n) c
  exact (eq_of_heq h2.symm).trans h1

/-- `rFlag` is linear, so the zero-flag classes form a submodule. -/
theorem zeroFlags_sub {N n : ℕ} {c c' : groupCohomology.H2 (gammaNRepAll N n)} (h : ZeroFlags N n c) (h' : ZeroFlags N n c') :
    ZeroFlags N n (c - c') := by
  intro g
  rw [map_sub, h g, h' g, sub_zero]

/-- **From the Eisenstein existence at level `N` and the uniqueness clause at level `M`, `N ∣ M`, to Proposition C.5 at level `Γ(N)`.**
(a) is the hypothesis `eis`; (b): subtract the Eisenstein class with the same plane coordinates, then apply `UniqLevel N` (descended from `M`). -/
theorem propC5_of_uniq [NeZero N] (hU : UniqLevel N n)
    (eis : ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n, ∀ ξ : PlaneCuspSum N n,
      ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧ lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c) :
    PropC5GammaN N n := by
  obtain ⟨T, hT⟩ := eis
  refine ⟨T, hT, ?_⟩
  intro c hz ξP ξQ hP hQ
  obtain ⟨cE, hzE, hPE, hQE⟩ := hT ξP
  have hd := hU (c - cE) (zeroFlags_sub hz hzE) (by rw [map_sub, ← hP, ← hPE, sub_self])
  rw [map_sub, ← hQ, ← hQE, ← map_sub] at hd
  have := lineCuspSumEmbedding_injective N n (hd.trans (map_zero _).symm)
  exact sub_eq_zero.mp this

/-- **Proposition C.5 at level `Γ(N)` from level `M`, `N ∣ M`.** The uniqueness clause at the common level `M` (e.g. `M = lcm(N, 6)`, where the Stokes
lemma of `Γ(6)` is available) together with Eisenstein existence at level `N` gives Proposition C.5 at level `N`. -/
theorem propC5_of_level [NeZero N] [NeZero M] (hNM : N ∣ M) (hU : UniqLevel M n)
    (eis : ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n, ∀ ξ : PlaneCuspSum N n,
      ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧ lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c) :
    PropC5GammaN N n :=
  propC5_of_uniq n (uniqLevel_of_dvd n hNM hU) eis

/-- The uniqueness clause is the zero-plane-data case of Proposition C.5 (`N ≥ 3`). -/
theorem uniqLevel_of_propC5 [NeZero N] (hN : 3 ≤ N) (h : PropC5GammaN N n) : UniqLevel N n := by
  intro c hz hP
  obtain ⟨T, -, hb⟩ := h
  obtain ⟨-, ξQ, hQ⟩ : (∃ ξP : PlaneCuspSum N n, planeCuspSumEmbedding N n ξP = planeBoundary N n c) ∧
      ∃ ξQ : LineCuspSum N n, lineCuspSumEmbedding N n ξQ = lineBoundary N n c :=
    exists_coordinates N n c ((zeroFlags_iff_mixed N n hN c).mp hz)
  have := hb c hz 0 ξQ (by rw [map_zero, hP]) hQ
  rw [← hQ, this, map_zero, map_zero]

/-- The uniqueness clause at level `M` from the four analytic inputs at level `M` (`3 ≤ M`). -/
theorem uniqLevel_of_obligations {PD QD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup QD] [Module ℂ QD]
    [AddCommGroup Hd] [Module ℂ Hd] [NeZero M] (hM : 3 ≤ M) (O : GammaNC5Obligations M n PD QD Hd) : UniqLevel M n :=
  uniqLevel_of_propC5 n hM (propC5_gammaN_of_obligations M n O)

/-- **Proposition C.5 at an arbitrary level `Γ(N)` from the analytic inputs at the level `M = lcm(N, 6)`-type common level `M` (`N ∣ M`) and
Eisenstein existence at level `N`.** The Stokes field is needed only at the level `M`. -/
theorem propC5_of_obligations_at_level {PD QD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup QD] [Module ℂ QD]
    [AddCommGroup Hd] [Module ℂ Hd] [NeZero N] [NeZero M] (hNM : N ∣ M) (hM : 3 ≤ M) (O : GammaNC5Obligations M n PD QD Hd)
    (eis : ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n, ∀ ξ : PlaneCuspSum N n,
      ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧ lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c) :
    PropC5GammaN N n :=
  propC5_of_level n hNM (uniqLevel_of_obligations n hM O) eis

/-- The same from the per-face obligations of `GammaNC5FaceObligations` at the common level `M`. -/
theorem propC5_of_face_obligations_at_level {QDi : LineFaces M → Type} [∀ i, AddCommGroup (QDi i)] [∀ i, Module ℂ (QDi i)]
    {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd] [NeZero N] [NeZero M] (hNM : N ∣ M)
    (hM : 3 ≤ M) (O : GammaNC5FaceObligations M n QDi PD Hd)
    (eis : ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n, ∀ ξ : PlaneCuspSum N n,
      ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧ lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c) :
    PropC5GammaN N n :=
  propC5_of_obligations_at_level n hNM hM O.toObligations eis

end Descent


end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
