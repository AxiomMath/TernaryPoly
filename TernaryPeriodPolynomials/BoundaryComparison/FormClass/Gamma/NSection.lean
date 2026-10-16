module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NConstantTerms

@[expose] public section


/-!
# `eisensteinP` at level `Γ(N)` without unfolding the series at the line face (linear section)

Formalized by Claude Sonnet 5.5.

**Finding.**  The field `eisensteinP` of the `GammaNC5Obligations` asks for ONE linear map `T : 𝒞_P(E) → 𝒞_Q(E)` and, for every `ξ`, a global class with zero flag restrictions, plane coordinate `ξ` and line coordinate `Tξ`.
It does not ask that `T` be the integral intertwiner, nor independent of choices.  Given the plane constant terms for the classical series (`ClassicalPlaneConstantTerms`: `r_B = 0` and `r_P ℰ_P(ξ) = ξ` at every plane face;
the L3-L8), the linearity of the series class and of the seed vector in the cusp forms (`ClassicalLinearity`; the scalar action is twisted by complex conjugation on the antiholomorphic seed, `TwTuple`) and Eichler-Shimura
spanning (every `ξ` is a seed vector), a ℂ-linear section `s` of the seed map gives `T := (line coordinate) ∘ ℰ ∘ s`: line restrictions of a class with zero flag restrictions are mixed cuspidal (`zeroFlags_iff_mixed`,
`exists_coordinates`), so `T` is defined by inverting the injection `lineCuspSumEmbedding`.  `eisensteinP_of_section` does this.  NO line unfolding is used, and nothing from Proposition C.5 (no circularity).

What this does NOT give: the canonical, section-independent `T` (`ClassicalLineConstantTerm`, needing injectivity of the seed map = Eichler-Shimura injectivity, or the explicit unfolding of the series at the line face) and the
identification of `T` with the printed intertwiner `eq:intertwiner`.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- Tuples of cusp forms indexed by the plane faces and the two seeds, with the scalar action twisted by complex conjugation on the antiholomorphic
seed (`b = true`): `(λ • f) x true = conj λ • f x true`.  The class of the series with seed `b = true` is conjugate-linear in the cusp form. -/
def TwTuple : Type := PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)

instance : AddCommGroup (TwTuple N n) := inferInstanceAs (AddCommGroup (PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)))

instance : SMul ℂ (TwTuple N n) where
  smul a f := fun x b => (if b then star a else a) • f x b

instance : Module ℂ (TwTuple N n) where
  one_smul f := by
    funext x b
    change (if b then star (1 : ℂ) else (1 : ℂ)) • f x b = f x b
    cases b <;> simp
  mul_smul a c f := by
    funext x b
    change (if b then star (a * c) else a * c) • f x b = (if b then star a else a) • ((if b then star c else c) • f x b)
    cases b <;> simp [mul_smul, star_mul']
  smul_zero a := by
    funext x b
    change (if b then star a else a) • (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) = 0
    simp
  smul_add a f g := by
    funext x b
    change (if b then star a else a) • (f x b + g x b) =
      (if b then star a else a) • f x b + (if b then star a else a) • g x b
    rw [smul_add]
  add_smul a c f := by
    funext x b
    change (if b then star (a + c) else a + c) • f x b = (if b then star a else a) • f x b + (if b then star c else c) • f x b
    cases b <;> simp [add_smul]
  zero_smul f := by
    funext x b
    change (if b then star (0 : ℂ) else (0 : ℂ)) • f x b = 0
    cases b <;> simp

/-- **Linearity of the classical series class and of the seed vector in the cusp forms** (for the twisted scalar action of `TwTuple`): additivity and
compatibility with the scalar action.  These are S6's `eisensteinAtClassC_add/_cmul` and the corresponding additivity and homogeneity of the seed
classes `faceSeedKerClass`, `faceSeedConjKerClass` in `f` (conjugate-homogeneous for the antiholomorphic seed). -/
structure ClassicalLinearity (hn : 4 ≤ n) : Prop where
  class_add : ∀ f g : TwTuple N n, classCG N n hn (f + g) = classCG N n hn f + classCG N n hn g
  class_smul : ∀ (a : ℂ) (f : TwTuple N n), classCG N n hn (a • f) = a • classCG N n hn f
  seed_add : ∀ f g : TwTuple N n, seedBoundary N n (f + g) = seedBoundary N n f + seedBoundary N n g
  seed_smul : ∀ (a : ℂ) (f : TwTuple N n), seedBoundary N n (a • f) = a • seedBoundary N n f

variable {N n}

/-- `classCG` as a ℂ-linear map on tuples. -/
def classLin (hn : 4 ≤ n) (hl : ClassicalLinearity N n hn) : TwTuple N n →ₗ[ℂ] groupCohomology.H2 (gammaNRepAll N n) where
  toFun f := classCG N n hn f
  map_add' := hl.class_add
  map_smul' := hl.class_smul

/-- `seedBoundary` as a ℂ-linear map on tuples. -/
def seedLin (hn : 4 ≤ n) (hl : ClassicalLinearity N n hn) : TwTuple N n →ₗ[ℂ] PlaneFaceH2 N n where
  toFun f := seedBoundary N n f
  map_add' := hl.seed_add
  map_smul' := hl.seed_smul

/-- **The `eisensteinP` obligation of `GammaNC5Obligations` from the plane constant terms, by a linear section** (no unfolding at the line face).  If the
classical series has `r_B = 0` and `r_P ℰ_P(ξ) = ξ` (`ClassicalPlaneConstantTerms`), is linear in the cusp forms and the seed vectors exhaust `𝒞_P(E)`
(Eichler-Shimura spanning), then for the ℂ-linear map `T := (line coordinate) ∘ ℰ ∘ s`, with `s` a ℂ-linear section of the seed map, every `ξ` is the plane coordinate of the
global class `ℰ(sξ)` with zero flag restrictions and line coordinate `Tξ`.  Here `T` depends on the chosen section `s`; the canonical, section-independent
`T` is `ClassicalLineConstantTerm` (which needs injectivity of the seed map, or the explicit unfolding). -/
theorem eisensteinP_of_section (hN : 3 ≤ N) (hn : 4 ≤ n) (hP : ClassicalPlaneConstantTerms N n hn)
    (hl : ClassicalLinearity N n hn)
    (hsurj : ∀ ξ : PlaneCuspSum N n, ∃ f : TwTuple N n, planeCuspSumEmbedding N n ξ = seedBoundary N n f) :
    ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
          lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c := by
  -- the plane side: the seed map lands in the range of the injective embedding
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
  have hσsurj : Function.Surjective σ := fun ξ => by
    obtain ⟨f, hf⟩ := hsurj ξ
    exact ⟨f, planeCuspSumEmbedding_injective N n ((hσ f).trans hf.symm)⟩
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective σ (LinearMap.range_eq_top.2 hσsurj)
  -- the line side
  have hrangeQ : ∀ ξ : PlaneCuspSum N n,
      lineBoundary N n (classCG N n hn (s ξ)) ∈ LinearMap.range (lineCuspSumEmbedding N n) := fun ξ => by
    obtain ⟨-, ⟨ξQ, hξQ⟩⟩ := exists_coordinates N n _ (hm (s ξ))
    exact ⟨ξQ, hξQ⟩
  let L : PlaneCuspSum N n →ₗ[ℂ] LineFaceH2 N n := lineBoundary N n ∘ₗ classLin hn hl ∘ₗ s
  have hL : ∀ ξ, L ξ ∈ LinearMap.range (lineCuspSumEmbedding N n) := hrangeQ
  let eQ := LinearEquiv.ofInjective (lineCuspSumEmbedding N n) (lineCuspSumEmbedding_injective N n)
  refine ⟨eQ.symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range (lineCuspSumEmbedding N n)) hL, fun ξ => ?_⟩
  refine ⟨classCG N n hn (s ξ), (hP _).1, ?_, ?_⟩
  · have h1 : σ (s ξ) = ξ := LinearMap.congr_fun hs ξ
    exact ((congrArg (planeCuspSumEmbedding N n) h1).symm.trans (hσ (s ξ))).trans ((hP (s ξ)).2).symm
  · have := eQ.apply_symm_apply ⟨L ξ, hL ξ⟩
    exact congrArg Subtype.val this

end TernaryPeriodPolynomials.Argument.FormClassK
