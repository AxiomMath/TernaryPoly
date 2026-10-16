module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.BaseCusp

@[expose] public section


/-!
# The classical constant terms at level `Γ(N)` (statements)

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:constantterms` in the
appendix convention of the paper.

These are DEFINITIONS of propositions (nothing assumes them):
* `classCG`: the summed classical series, a global class of `Γ(N)` (`gammaNRepAll`; `gammaRep (gammaN N) n = gammaNRepAll N n` by `rfl`);
* `seedBoundary`: the boundary vector of seed classes at the plane faces `planeFaceRepr i`;
* `ClassicalPlaneConstantTerms`: `r_B = 0` (`ZeroFlags`) and `r_P ℰ_P(ξ) = ξ` at every plane face;
* `ClassicalLineConstantTerm`: `r_Q ℰ_P(ξ) = Tξ` with ONE ℂ-linear `T : 𝒞_P(E) → 𝒞_Q(E)`.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

section GammaNLevel

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The summed classical series as a global class of `Γ(N)` (the finite sum over the plane cusps `x` and both seeds `b` of the
complexified series class at the cusp `x`, seed `b`, of the cusp form `f x b`). -/
def classCG (hn : 4 ≤ n) (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    groupCohomology.H2 (gammaNRepAll N n) :=
  ∑ x : PlaneFaces N, ∑ b : Bool, EisensteinClass.complexify (gammaN N) n
    (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (planeFaceRepr x) b hn)

open scoped Classical in
/-- The boundary vector of seed classes: at the plane face `i` (representative `planeFaceRepr i`), the class of the holomorphic seed of
`f i false` plus the class of the antiholomorphic seed of `f i true`, conjugated to the cusp `planeFaceRepr i`. -/
def seedBoundary (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) : PlaneFaceH2 N n :=
  ∑ i : PlaneFaces N, DirectSum.lof ℂ (PlaneFaces N) (fun i => groupCohomology.H2 (faceRep N (planeFaceRepr i) n)) i
    ((faceSeedKerClass N (planeFaceRepr i) n (f i false)).1 +
      (faceSeedConjKerClass N (planeFaceRepr i) n (f i true)).1)

/-- **`ar:eq:constantterms`, first and third identities, at level `Γ(N)` for the classical series** ( with the
convention of the paper): the global class has zero flag restrictions (`r_B = 0`) and its plane boundary vector is the vector of
seeds (`r_P ℰ_P(ξ) = ξ`, at every plane face). -/
def ClassicalPlaneConstantTerms (hn : 4 ≤ n) : Prop :=
  ∀ f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ),
    ZeroFlags N n (classCG N n hn f) ∧ planeBoundary N n (classCG N n hn f) = seedBoundary N n f

/-- **`ar:eq:constantterms`, second identity, at level `Γ(N)` for the classical series** (`r_Q ℰ_P(ξ) = Tξ`): there is ONE ℂ-linear map
`T : 𝒞_P(E) → 𝒞_Q(E)` such that, for every tuple `f` and every `ξ ∈ 𝒞_P(E)` with plane boundary vector the seed vector of `f`
(`ξ` is the class represented by the seeds of `f`), the line boundary vector of the global class of `f` is that of `Tξ`. -/
def ClassicalLineConstantTerm (hn : 4 ≤ n) : Prop :=
  ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
    ∀ (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (ξ : PlaneCuspSum N n),
      planeCuspSumEmbedding N n ξ = seedBoundary N n f →
        lineCuspSumEmbedding N n (T ξ) = lineBoundary N n (classCG N n hn f)

/-- **CONSISTENCY REDUCTION, NOT A PROOF ROUTE.**  If the classical series has `r_B = 0` and `r_P ℰ_P(ξ) = ξ` (`ClassicalPlaneConstantTerms`) and Proposition C.5 holds at
level `Γ(N)` (`PropC5GammaN`, uniqueness clause with the linear map `T`), then `r_Q ℰ_P(ξ) = Tξ` for that same `T`.  This shows that the line constant term is
consistent with, and determined by, Prop C.5 plus the plane constant terms.  It must NOT be used to discharge `ClassicalLineConstantTerm` inside the paper's proof route:
in the paper Prop C.5 is PROVED from the line constant term ( pairs the class with `ℰ_Q^∨` and uses `r_Q ℰ_P(ξ) = Tξ`; this is the field `eisensteinP` of
`GammaNC5Obligations`), so feeding this reduction into `propC5_gammaN_of_obligations` or into `eisensteinP_of_classical` would be circular.  The line constant term
must come from the direct unfolding of the series at the line face. -/
theorem classicalLine_of_propC5 (hN : 3 ≤ N) (hn : 4 ≤ n) (hP : ClassicalPlaneConstantTerms N n hn)
    (hC : PropC5GammaN N n) : ClassicalLineConstantTerm N n hn := by
  obtain ⟨T, -, huniq⟩ := hC
  refine ⟨T, fun f ξ hξ => ?_⟩
  obtain ⟨hz, hpl⟩ := hP f
  have hm := (zeroFlags_iff_mixed N n hN _).1 hz
  obtain ⟨⟨ξP, hξP⟩, ⟨ξQ, hξQ⟩⟩ := exists_coordinates N n _ hm
  have hξξP : ξ = ξP :=
    planeCuspSumEmbedding_injective N n (hξ.trans (hpl.symm.trans hξP.symm))
  have := huniq _ hz ξP ξQ hξP hξQ
  rw [hξξP, ← this]
  exact hξQ

/-- **The `eisensteinP` obligation of `GammaNC5Obligations` from the classical constant terms** (the hypothesis `hL` must be the directly unfolded line constant term, never `classicalLine_of_propC5`, which would be circular).  If the classical series satisfies the plane and line constant terms
and every `ξ ∈ 𝒞_P(E)` is the seed vector of a tuple of cusp forms (Eichler-Shimura spanning with linearity of the seed classes in `f`), then for the
map `T` of `ClassicalLineConstantTerm` every `ξ` is the plane coordinate of a global class with zero flag restrictions whose line coordinate is `Tξ`. -/
theorem eisensteinP_of_classical (hn : 4 ≤ n) (hP : ClassicalPlaneConstantTerms N n hn)
    (hL : ClassicalLineConstantTerm N n hn)
    (hsurj : ∀ ξ : PlaneCuspSum N n, ∃ f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ),
      planeCuspSumEmbedding N n ξ = seedBoundary N n f) :
    ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
          lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c := by
  obtain ⟨T, hT⟩ := hL
  refine ⟨T, fun ξ => ?_⟩
  obtain ⟨f, hf⟩ := hsurj ξ
  obtain ⟨hz, hpl⟩ := hP f
  exact ⟨classCG N n hn f, hz, hf.trans hpl.symm, hT f ξ hf⟩

end GammaNLevel

end TernaryPeriodPolynomials.Argument.FormClassK
