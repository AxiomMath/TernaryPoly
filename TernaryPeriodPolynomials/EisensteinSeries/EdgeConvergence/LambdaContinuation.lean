module

public import Mathlib

@[expose] public section


/-!
# Continuation of the away multiplier without L-functions

Abstract form of the continuation step of the totality argument at the edge of absolute
convergence. A family of meromorphic functions `J d` and a family of analytic functions `R d`
on a preconnected set `Ω` are related, on a nonempty open part `V` of `Ω`, by a single factor
`lam` independent of the datum `d`: `J d = lam * R d` on `V`. The identity theorem then
propagates the cross-multiplied identity `J d * R d' = J d' * R d` from `V` to a punctured
neighbourhood of any `s₀ ∈ Ω`, and:

* either every `R d` vanishes near `s₀` (hence on `Ω`), and every `J d` vanishes near `s₀`;
* or some `R d₀` does not vanish near `s₀`, `lamTilde := J d₀ / R d₀` is meromorphic at `s₀`, and
  `J d = lamTilde * R d` on a punctured neighbourhood of `s₀` for every `d`.
-/

open Filter Topology

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace LambdaContinuation

/-- The continuation `J d₀ / R d₀` of the multiplier, for a base datum `d₀`. -/
noncomputable def lamTilde {D : Type*} (J R : D → ℂ → ℂ) (d₀ : D) : ℂ → ℂ := J d₀ / R d₀

theorem lamTilde_apply {D : Type*} (J R : D → ℂ → ℂ) (d₀ : D) (s : ℂ) :
    lamTilde J R d₀ s = J d₀ s / R d₀ s := rfl

/-- The hypotheses of the continuation argument: on a preconnected set `Ω`, the `J d` are
meromorphic and the `R d` analytic, and on a nonempty open subset `V` of `Ω` one factor `lam`
satisfies `J d = lam * R d` for every datum `d`. -/
structure ContinuationData {D : Type*} (Ω V : Set ℂ) (J R : D → ℂ → ℂ) (lam : ℂ → ℂ) :
    Prop where
  preconnected : IsPreconnected Ω
  isOpen : IsOpen V
  subset : V ⊆ Ω
  nonempty : V.Nonempty
  meromorphic : ∀ d, MeromorphicOn (J d) Ω
  analytic : ∀ d, AnalyticOnNhd ℂ (R d) Ω
  factor : ∀ d, ∀ s ∈ V, J d s = lam s * R d s

/-- A meromorphic function on a preconnected set that vanishes on a nonempty open subset
vanishes in a punctured neighbourhood of every point of the set. -/
theorem eventuallyEq_zero_nhdsNE_of_zero_on_open {U V : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f U) (hU : IsPreconnected U) (hV : IsOpen V) (hVU : V ⊆ U)
    {v : ℂ} (hv : v ∈ V) (hzero : ∀ s ∈ V, f s = 0) {s₀ : ℂ} (hs₀ : s₀ ∈ U) :
    ∀ᶠ s in 𝓝[≠] s₀, f s = 0 := by
  have hnhds : ∀ᶠ s in 𝓝 v, f s = 0 :=
    Filter.mem_of_superset (hV.mem_nhds hv) (fun s hs => hzero s hs)
  have hv0 : meromorphicOrderAt f v = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (eventually_nhdsWithin_of_eventually_nhds hnhds)
  have hs0 : meromorphicOrderAt f s₀ = ⊤ := by
    by_contra hne
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hf hU hs₀ (hVU hv) hne hv0
  exact meromorphicOrderAt_eq_top_iff.1 hs0

/-- The cross-multiplied identity `J d * R d' = J d' * R d` holds in a punctured neighbourhood of
every point of `Ω`. -/
theorem cross_mul_eventuallyEq {D : Type*} {Ω V : Set ℂ} {J R : D → ℂ → ℂ} {lam : ℂ → ℂ}
    (data : ContinuationData Ω V J R lam) (d d' : D) {s₀ : ℂ} (hs₀ : s₀ ∈ Ω) :
    ∀ᶠ s in 𝓝[≠] s₀, J d s * R d' s = J d' s * R d s := by
  obtain ⟨v, hv⟩ := data.nonempty
  have hF : MeromorphicOn (J d * R d' - J d' * R d) Ω :=
    ((data.meromorphic d).mul (data.analytic d').meromorphicOn).sub
      ((data.meromorphic d').mul (data.analytic d).meromorphicOn)
  have hz : ∀ᶠ s in 𝓝[≠] s₀, (J d * R d' - J d' * R d) s = 0 := by
    refine eventuallyEq_zero_nhdsNE_of_zero_on_open hF data.preconnected data.isOpen data.subset
      hv (fun s hs => ?_) hs₀
    show J d s * R d' s - J d' s * R d s = 0
    rw [data.factor d s hs, data.factor d' s hs]
    ring
  filter_upwards [hz] with s hs
  have hs' : J d s * R d' s - J d' s * R d s = 0 := hs
  exact sub_eq_zero.1 hs'

/-- If `R d₀` does not vanish in a neighbourhood of `s₀`, then `lamTilde = J d₀ / R d₀` is
meromorphic at `s₀`, `R d₀` has no zeros in a punctured neighbourhood, and `J d = lamTilde * R d`
in a punctured neighbourhood for every datum `d`. -/
theorem eventually_eq_lamTilde_mul {D : Type*} {Ω V : Set ℂ} {J R : D → ℂ → ℂ} {lam : ℂ → ℂ}
    (data : ContinuationData Ω V J R lam) {s₀ : ℂ} (hs₀ : s₀ ∈ Ω) (d₀ : D)
    (hd₀ : meromorphicOrderAt (R d₀) s₀ ≠ ⊤) :
    MeromorphicAt (lamTilde J R d₀) s₀ ∧ (∀ᶠ s in 𝓝[≠] s₀, R d₀ s ≠ 0) ∧
      ∀ d, ∀ᶠ s in 𝓝[≠] s₀, J d s = lamTilde J R d₀ s * R d s := by
  have hRmero : MeromorphicAt (R d₀) s₀ := (data.analytic d₀ s₀ hs₀).meromorphicAt
  have hne : ∀ᶠ s in 𝓝[≠] s₀, R d₀ s ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hRmero).1 hd₀
  refine ⟨(data.meromorphic d₀ s₀ hs₀).div hRmero, hne, fun d => ?_⟩
  filter_upwards [hne, cross_mul_eventuallyEq data d d₀ hs₀] with s hs hcross
  show J d s = J d₀ s / R d₀ s * R d s
  rw [div_mul_eq_mul_div, eq_div_iff hs]
  exact hcross

/-- If every `R d` vanishes in a neighbourhood of `s₀`, then every `J d` vanishes in a punctured
neighbourhood of `s₀`. -/
theorem eventually_zero_of_R_zero {D : Type*} {Ω V : Set ℂ} {J R : D → ℂ → ℂ} {lam : ℂ → ℂ}
    (data : ContinuationData Ω V J R lam) {s₀ : ℂ} (hs₀ : s₀ ∈ Ω)
    (hR0 : ∀ d, ∀ᶠ s in 𝓝 s₀, R d s = 0) (d : D) :
    ∀ᶠ s in 𝓝[≠] s₀, J d s = 0 := by
  obtain ⟨v, hv⟩ := data.nonempty
  have hRz : ∀ s ∈ Ω, R d s = 0 := fun s hs =>
    (data.analytic d).eqOn_zero_of_preconnected_of_eventuallyEq_zero data.preconnected hs₀
      (hR0 d) hs
  refine eventuallyEq_zero_nhdsNE_of_zero_on_open (data.meromorphic d) data.preconnected
    data.isOpen data.subset hv (fun s hs => ?_) hs₀
  rw [data.factor d s hs, hRz s (data.subset hs), mul_zero]

/-- An analytic function that does not vanish in a neighbourhood of `x` has finite meromorphic
order at `x`. -/
theorem meromorphicOrderAt_ne_top_of_not_eventually_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (h : ¬ ∀ᶠ z in 𝓝 x, f z = 0) :
    meromorphicOrderAt f x ≠ ⊤ := by
  intro htop
  have hz : ∀ᶠ z in 𝓝[≠] x, f z = 0 := meromorphicOrderAt_eq_top_iff.1 htop
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact h h0
  · obtain ⟨s, hs0, hsne⟩ := (hz.and hne).exists
    exact hsne hs0

/-- **Continuation of the multiplier.** Either every `R d` and every `J d` vanishes near `s₀`
(the `J d` in a punctured neighbourhood), or there is a datum `d₀` for which `lamTilde = J d₀ / R d₀`
is meromorphic at `s₀`, `R d₀` has no zeros in a punctured neighbourhood of `s₀`, and
`J d = lamTilde * R d` in a punctured neighbourhood of `s₀` for every datum `d`. -/
theorem lambda_continuation {D : Type*} {Ω V : Set ℂ} {J R : D → ℂ → ℂ} {lam : ℂ → ℂ}
    (data : ContinuationData Ω V J R lam) {s₀ : ℂ} (hs₀ : s₀ ∈ Ω) :
    ((∀ d, ∀ᶠ s in 𝓝 s₀, R d s = 0) ∧ ∀ d, ∀ᶠ s in 𝓝[≠] s₀, J d s = 0) ∨
      ∃ d₀, MeromorphicAt (lamTilde J R d₀) s₀ ∧ (∀ᶠ s in 𝓝[≠] s₀, R d₀ s ≠ 0) ∧
        ∀ d, ∀ᶠ s in 𝓝[≠] s₀, J d s = lamTilde J R d₀ s * R d s := by
  by_cases h : ∀ d, ∀ᶠ s in 𝓝 s₀, R d s = 0
  · exact Or.inl ⟨h, fun d => eventually_zero_of_R_zero data hs₀ h d⟩
  · right
    obtain ⟨d₀, hd₀⟩ := not_forall.1 h
    exact ⟨d₀, eventually_eq_lamTilde_mul data hs₀ d₀
      (meromorphicOrderAt_ne_top_of_not_eventually_zero (data.analytic d₀ s₀ hs₀) hd₀)⟩

/-- A function that is continuous at `s₀` and vanishes in a punctured neighbourhood of `s₀`
vanishes at `s₀`. -/
theorem value_eq_zero_of_eventually_zero_nhdsNE {f : ℂ → ℂ} {s₀ : ℂ} (hf : ContinuousAt f s₀)
    (h : ∀ᶠ s in 𝓝[≠] s₀, f s = 0) : f s₀ = 0 := by
  have h1 : Tendsto f (𝓝[≠] s₀) (𝓝 (f s₀)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h' : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] s₀] f := h.mono fun s hs => hs.symm
  have h2 : Tendsto f (𝓝[≠] s₀) (𝓝 0) := tendsto_const_nhds.congr' h'
  exact tendsto_nhds_unique h1 h2

/-- In the vanishing alternative of `lambda_continuation`, the value at `s₀` of every `J d` that is
analytic at `s₀` is zero. -/
theorem value_eq_zero_of_alternative {D : Type*} {J : D → ℂ → ℂ} {s₀ : ℂ}
    (hzero : ∀ d, ∀ᶠ s in 𝓝[≠] s₀, J d s = 0) (d : D) (hJ : AnalyticAt ℂ (J d) s₀) :
    J d s₀ = 0 :=
  value_eq_zero_of_eventually_zero_nhdsNE hJ.continuousAt (hzero d)

/-- The punctured-neighbourhood statements used in the Cauchy lift: a property holding in a
punctured neighbourhood of `s₀` holds on a punctured ball. -/
theorem exists_punctured_ball {P : ℂ → Prop} {s₀ : ℂ} (h : ∀ᶠ s in 𝓝[≠] s₀, P s) :
    ∃ ε > 0, ∀ s, s ≠ s₀ → dist s s₀ < ε → P s := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hP⟩ := h
  exact ⟨ε, hε, fun s hs hd => hP hd hs⟩

end LambdaContinuation

end TernaryPeriodPolynomials.EdgeConvergence
