module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NPlaneValues

@[expose] public section


/-!
# Canonicity of `T` from Eichler-Shimura injectivity; line restrictions are mixed cuspidal

Formalized by Claude Sonnet 5.5.
* `SeedMapInjective`: the injectivity of the seed map `f ↦ seedBoundary f` (Eichler-Shimura injectivity at level `Γ(N)`, face by face).* **`classicalLine_of_seedInjective`**: `SeedMapInjective → ClassicalLineConstantTerm` (the canonical, presentation-independent `r_Q ℰ_P(ξ) = Tξ`), using the unconditional plane constant terms.
* **`classCG_line_mixed`**: `r_Q ℰ_P ∈ 𝒞_{Q'}(E)` at every line cusp (unconditional).
-/

open scoped MatrixGroups DirectSum
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Eichler-Shimura injectivity at level `Γ(N)`, in the form needed here**: the seed vector of a tuple of cusp forms (holomorphic seeds of `f x false`,
antiholomorphic seeds of `f x true`, at the plane faces) vanishes only for the zero tuple, i.e. the map `S_{n+3}(Γ(N)) ⊕ \\bar S_{n+3}(Γ(N)) → H¹_cusp(Γ_2(N), Sym^{n+1})`,
face by face, is injective.  NOT proved in the library (only spanning, `eichler_shimura_spanning_gammaN`; injectivity only for `Γ₁'(3)`: `levelPeriodMap_injective_levelThree`,
and level one: `levelOnePeriodMap_injective`, by Hecke kernel stability and Euler-product nonvanishing of the moment). -/
def SeedMapInjective : Prop := ∀ f : TwTuple N n, seedBoundary N n f = 0 → f = 0

/-- **Canonicity of `T` from Eichler-Shimura injectivity.**  If the seed map is injective, the section-independent statement `ClassicalLineConstantTerm`
(`r_Q ℰ_P(ξ) = Tξ` for one linear `T` and EVERY presentation of `ξ` by a tuple of cusp forms) holds. -/
theorem classicalLine_of_seedInjective (hN : 3 ≤ N) (hn : 4 ≤ n) (hinj : SeedMapInjective N n) :
    ClassicalLineConstantTerm N n hn := by
  have hP := classicalPlaneConstantTerms N n hN hn
  have hl := classicalLinearity N n hn
  have hm : ∀ f : TwTuple N n, MixedCuspidalRestrictions N n (classCG N n hn f) := fun f =>
    (zeroFlags_iff_mixed N n hN _).1 (hP f).1
  have hrangeP : ∀ f : TwTuple N n, seedLin hn hl f ∈ LinearMap.range (planeCuspSumEmbedding N n) := fun f => by
    obtain ⟨⟨ξP, hξP⟩, -⟩ := exists_coordinates N n _ (hm f)
    exact ⟨ξP, hξP.trans (hP f).2⟩
  let eP := LinearEquiv.ofInjective (planeCuspSumEmbedding N n) (planeCuspSumEmbedding_injective N n)
  let σ : TwTuple N n →ₗ[ℂ] PlaneCuspSum N n :=
    eP.symm.toLinearMap ∘ₗ (seedLin hn hl).codRestrict (LinearMap.range (planeCuspSumEmbedding N n)) hrangeP
  have hσ : ∀ f, planeCuspSumEmbedding N n (σ f) = seedBoundary N n f := fun f => by
    have := eP.apply_symm_apply ⟨seedLin hn hl f, hrangeP f⟩
    exact congrArg Subtype.val this
  have hσinj : Function.Injective σ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply hinj
    rw [← hσ, hf, map_zero]
  have hσsurj : Function.Surjective σ := fun ξ => by
    obtain ⟨f, hf⟩ := seedBoundary_surjective N n ξ
    exact ⟨f, planeCuspSumEmbedding_injective N n ((hσ f).trans hf.symm)⟩
  let s : PlaneCuspSum N n →ₗ[ℂ] TwTuple N n := (LinearEquiv.ofBijective σ ⟨hσinj, hσsurj⟩).symm.toLinearMap
  have hs : ∀ ξ, σ (s ξ) = ξ := fun ξ => (LinearEquiv.ofBijective σ ⟨hσinj, hσsurj⟩).apply_symm_apply ξ
  have hs' : ∀ f, s (σ f) = f := fun f => (LinearEquiv.ofBijective σ ⟨hσinj, hσsurj⟩).symm_apply_apply f
  have hrangeQ : ∀ ξ : PlaneCuspSum N n,
      lineBoundary N n (classCG N n hn (s ξ)) ∈ LinearMap.range (lineCuspSumEmbedding N n) := fun ξ => by
    obtain ⟨-, ⟨ξQ, hξQ⟩⟩ := exists_coordinates N n _ (hm (s ξ))
    exact ⟨ξQ, hξQ⟩
  let L : PlaneCuspSum N n →ₗ[ℂ] LineFaceH2 N n := lineBoundary N n ∘ₗ classLin hn hl ∘ₗ s
  have hL : ∀ ξ, L ξ ∈ LinearMap.range (lineCuspSumEmbedding N n) := hrangeQ
  let eQ := LinearEquiv.ofInjective (lineCuspSumEmbedding N n) (lineCuspSumEmbedding_injective N n)
  refine ⟨eQ.symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range (lineCuspSumEmbedding N n)) hL, fun f ξ hξ => ?_⟩
  have h1 : σ f = ξ := planeCuspSumEmbedding_injective N n ((hσ f).trans hξ.symm)
  have h2 : s ξ = f := by rw [← h1]; exact hs' f
  have := eQ.apply_symm_apply ⟨L ξ, hL ξ⟩
  refine (congrArg Subtype.val this).trans ?_
  show L ξ = _
  change lineBoundary N n (classCG N n hn (s ξ)) = _
  rw [h2]

/-- **U6 is free: the line restrictions of the classical series are mixed cuspidal** (`r_Q ℰ_P ∈ 𝒞_{Q'}(E)` at every line cusp), from `r_B = 0`
(`classicalPlaneConstantTerms`) and S1's `zeroFlags_line_mixed`.  Only the IDENTIFICATION of this class with `Tξ` needs the unfolding. -/
theorem classCG_line_mixed (hN : 3 ≤ N) (hn : 4 ≤ n) (f : TwTuple N n) (h : SL(3, ℤ)) :
    rLine N n h (classCG N n hn f) ∈ lineFaceCuspidalInH2 N h n :=
  zeroFlags_line_mixed N n hN _ (classicalPlaneConstantTerms N n hN hn f).1 h

end TernaryPeriodPolynomials.Argument.FormClassK
