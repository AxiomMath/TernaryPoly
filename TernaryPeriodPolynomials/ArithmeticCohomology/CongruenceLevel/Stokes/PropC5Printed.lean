module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PropC5Final
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.SeedInjective

@[expose] public section


/-!
# Proposition C.5 at `Γ(N)` with the printed constant-term map

Formalized by Claude Sonnet 5.5.

`propC5_gammaN_printed`: for `3 ≤ N`, `4 ≤ n` there is ONE linear map `T : 𝒞_P(E) → 𝒞_Q(E)` which is the printed intertwiner of `ar:eq:constantterms` (`r_Q ℰ_P(ξ) = Tξ` for the classical series and every presentation of `ξ` by a tuple of cusp forms:
`classicalLine`), with (a) every `ξ` the plane restriction of a global class of zero flag restrictions whose line restriction is `Tξ`, and (b) every global class with zero flag restrictions and
mixed cuspidal restrictions `(ξ_P, ξ_Q)` has `ξ_Q = T ξ_P`.  (b) is the uniqueness clause of `propC5_gammaN` applied to the classical classes, which identifies its abstract `T` with the printed one.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.FormClassK

theorem propC5_gammaN_printed {N n : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      (∀ (f : TwTuple N n) (ξ : PlaneCuspSum N n), planeCuspSumEmbedding N n ξ = seedBoundary N n f →
        lineCuspSumEmbedding N n (T ξ) = lineBoundary N n (classCG N n hn f)) ∧
      (∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
          lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c) ∧
      ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
        ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
          planeCuspSumEmbedding N n ξP = planeBoundary N n c →
          lineCuspSumEmbedding N n ξQ = lineBoundary N n c → ξQ = T ξP := by
  obtain ⟨T, hT⟩ := EichlerShimuraInj.classicalLine N n hN hn
  obtain ⟨T0, -, hu⟩ := propC5_gammaN hN hn
  have hP := classicalPlaneConstantTerms N n hN hn
  have hTT : ∀ ξ, T0 ξ = T ξ := fun ξ => by
    obtain ⟨f, hf⟩ := seedBoundary_surjective N n ξ
    obtain ⟨hz, hpl⟩ := hP f
    exact (hu _ hz ξ (T ξ) (hf.trans hpl.symm) (hT f ξ hf)).symm
  refine ⟨T, hT, fun ξ => ?_, fun c hc ξP ξQ h1 h2 => ?_⟩
  · obtain ⟨f, hf⟩ := seedBoundary_surjective N n ξ
    obtain ⟨hz, hpl⟩ := hP f
    exact ⟨classCG N n hn f, hz, hf.trans hpl.symm, hT f ξ hf⟩
  · rw [← hTT]
    exact hu c hc ξP ξQ h1 h2

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
