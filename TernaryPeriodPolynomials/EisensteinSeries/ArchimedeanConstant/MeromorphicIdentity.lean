module

public import Mathlib

@[expose] public section


/-!
# Identity theorem for everywhere-meromorphic functions on `ℂ`

If `f` is meromorphic at every point of `ℂ`, vanishes on a right half-plane and is analytic at
`s₀`, then `f s₀ = 0`. This is the continuation step of the large-`Re s` route: identities proved
for `Re s ≫ 0` hold at the cohomological point when both sides are meromorphic everywhere and
analytic there (as `IsStandardContinuation` and `PlaneEisensteinHolomorphic` supply).

Original work (AxiomDeep, Claude Opus 5.5).
-/

open Filter Topology

namespace TernaryPeriodPolynomials.ArchimedeanConstant

theorem meromorphic_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (hf : ∀ z, MeromorphicAt f z) (R : ℝ) (hR : ∀ s : ℂ, R < s.re → f s = 0)
    {s₀ : ℂ} (ha : AnalyticAt ℂ f s₀) : f s₀ = 0 := by
  let S : Set ℂ := {z | f =ᶠ[𝓝[≠] z] 0}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hz' : ∀ᶠ w in 𝓝[≠] z, f w = 0 := hz
    rw [eventually_nhdsWithin_iff] at hz'
    obtain ⟨U, hU, hUopen, hzU⟩ := eventually_nhds_iff.mp hz'
    refine Filter.mem_of_superset (hUopen.mem_nhds hzU) fun w hw => ?_
    by_cases hwz : w = z
    · rw [hwz]; exact hz
    · have hV : IsOpen (U ∩ {z}ᶜ) := hUopen.inter isOpen_compl_singleton
      have hwV : w ∈ U ∩ {z}ᶜ := ⟨hw, hwz⟩
      apply eventually_nhdsWithin_of_eventually_nhds
      exact Filter.mem_of_superset (hV.mem_nhds hwV) fun y hy => hU y hy.1 hy.2
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    rcases (hf z).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exact absurd h0 hz
    rw [eventually_nhdsWithin_iff] at hne
    obtain ⟨U, hU, hUopen, hzU⟩ := eventually_nhds_iff.mp hne
    refine Filter.mem_of_superset (hUopen.mem_nhds hzU) fun w hw => ?_
    by_cases hwz : w = z
    · rw [hwz]; exact hz
    · intro hwS
      have hV : IsOpen (U ∩ {z}ᶜ) := hUopen.inter isOpen_compl_singleton
      have hwV : w ∈ U ∩ {z}ᶜ := ⟨hw, hwz⟩
      have hne' : ∀ᶠ y in 𝓝[≠] w, f y ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds
          (Filter.mem_of_superset (hV.mem_nhds hwV) fun y hy => hU y hy.1 hy.2)
      have hS' : ∀ᶠ y in 𝓝[≠] w, f y = 0 := hwS
      obtain ⟨y, hy1, hy2⟩ := (hne'.and hS').exists
      exact hy1 hy2
  have hne : S.Nonempty := by
    refine ⟨((R + 1 : ℝ) : ℂ), ?_⟩
    apply eventually_nhdsWithin_of_eventually_nhds
    have hopenH : IsOpen {s : ℂ | R < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : ((R + 1 : ℝ) : ℂ) ∈ {s : ℂ | R < s.re} := by simp
    exact Filter.mem_of_superset (hopenH.mem_nhds hmem) fun s hs => hR s hs
  have huniv : S = Set.univ := (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left hne.ne_empty
  have hs₀ : f =ᶠ[𝓝[≠] s₀] 0 := by
    have : s₀ ∈ S := by rw [huniv]; exact Set.mem_univ _
    exact this
  have ht : Tendsto f (𝓝[≠] s₀) (𝓝 (f s₀)) :=
    ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht0 : Tendsto f (𝓝[≠] s₀) (𝓝 0) :=
    (tendsto_congr' hs₀).mpr tendsto_const_nhds
  exact tendsto_nhds_unique ht ht0

/-- Two everywhere-meromorphic functions agreeing on a right half-plane agree at every point where
both are analytic. -/
theorem meromorphic_identity_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : ℂ → E) (hf : ∀ z, MeromorphicAt f z) (hg : ∀ z, MeromorphicAt g z) (R : ℝ)
    (hR : ∀ s : ℂ, R < s.re → f s = g s) {s₀ : ℂ} (haf : AnalyticAt ℂ f s₀)
    (hag : AnalyticAt ℂ g s₀) : f s₀ = g s₀ := by
  have h := meromorphic_identity (fun s => f s - g s) (fun z => (hf z).sub (hg z)) R
    (fun s hs => by rw [hR s hs, sub_self]) (haf.sub hag)
  exact sub_eq_zero.mp h

/-- **Cocycle-level continuation.** A family of identities `J s i = c s * P s i + B s i`, valid
for `Re s > R` at every index `i`, with all three sides meromorphic everywhere and analytic at
`s₀`, holds at `s₀`. -/
theorem meromorphic_identity_family {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J P B : ℂ → ι → E) (c : ℂ → ℂ)
    (hJ : ∀ i z, MeromorphicAt (fun s => J s i) z) (hP : ∀ i z, MeromorphicAt (fun s => P s i) z)
    (hB : ∀ i z, MeromorphicAt (fun s => B s i) z) (hc : ∀ z, MeromorphicAt c z) (R : ℝ)
    (hR : ∀ s : ℂ, R < s.re → ∀ i, J s i = c s • P s i + B s i) {s₀ : ℂ}
    (haJ : ∀ i, AnalyticAt ℂ (fun s => J s i) s₀) (haP : ∀ i, AnalyticAt ℂ (fun s => P s i) s₀)
    (haB : ∀ i, AnalyticAt ℂ (fun s => B s i) s₀) (hac : AnalyticAt ℂ c s₀) :
    ∀ i, J s₀ i = c s₀ • P s₀ i + B s₀ i := by
  intro i
  exact meromorphic_identity_eq (fun s => J s i) (fun s => c s • P s i + B s i) (hJ i)
    (fun z => ((hc z).smul (hP i z)).add (hB i z)) R (fun s hs => hR s hs i) (haJ i)
    ((hac.smul (haP i)).add (haB i))

end TernaryPeriodPolynomials.ArchimedeanConstant
