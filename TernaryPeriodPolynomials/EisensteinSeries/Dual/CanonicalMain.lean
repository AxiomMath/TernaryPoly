module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.DualCanonical
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.DualFlags
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NCanonical
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedSurj

@[expose] public section


open scoped MatrixGroups DirectSum
open CategoryTheory
open scoped Classical
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK

/-!
# The dual constant terms `r_P ℰ_Q^∨(η) = T^∨ η`, conditional on canonicity of `T`

Formalized by Claude Sonnet 5.5.
Hypothesis, kept explicit: `ClassicalLineConstantTerm N n hn` (`FormClassK/GammaNConstantTerms`), i.e.
canonicity of `T` (one linear `T` with `r_Q ℰ_P(ξ) = Tξ` for every presentation of `ξ`; follows from `SeedMapInjective` by `classicalLine_of_seedInjective`).

* `PsiQ` (equivalence `∏_x 𝒞_{P'}(E) ≃ ∏_x 𝒞_Q(E^∨)`), `PsiP`: the `ȷ`-transport of the cuspidal data.
* **`dual_rP_eq_dualT_of_canonical`**: `T^∨ := PsiP ∘ T ∘ PsiQ⁻¹` satisfies, for every tuple `u` whose dual seed vector is `η`:
  `r_Q ℰ^∨(u) = η`, `r_P ℰ^∨(u) = T^∨ η`, `r_B ℰ^∨(u) = 0`.
* `dual_seed_exists`, `dual_constant_terms_all`: every `η ∈ 𝒞_Q(E^∨)` is the dual seed vector of a tuple, so `ℰ^∨(η)` exists with these constant terms.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) (n : ℕ)

section Global

variable [NeZero N]

/-- The plane groups of the dual series at the line faces: `H²(Γ_{ȷ(l)⁻¹Pȷ(l)}, E^∨)`, `l = LineFaces.rep i`. -/
abbrev DPi (N n : ℕ) (i : LineFaces N) :=
  groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N (jmath i.rep)))))

/-- `𝒞_Q(E^∨)` at the line cusp `ȷ(planeFaceRepr x)` (the face `x` of the dual construction). -/
abbrev QDJ (N n : ℕ) [NeZero N] (x : PlaneFaces N) := ↥(dualCuspidalQ N n (jmath (planeFaceRepr x)))

/-- `𝒞_P(E) → 𝒞_Q(E^∨)` at the face `x`: the `ȷ`-pullback of the injection `𝒞_{P'}(E) → H²(Γ_{P'}, E)`. -/
def phiQ (x : PlaneFaces N) : faceCuspidal N (planeFaceRepr x) n →ₗ[ℂ] QDJ N n x :=
  ((pullQP' N n (planeFaceRepr x)) ∘ₗ faceCuspidalEmbedding N n (planeFaceRepr x)).codRestrict _ (fun ξ => by
    rw [dualCuspidalQ_jmath]
    refine Submodule.mem_map_of_mem ?_
    rw [faceCuspidalInH2_eq_range]
    exact ⟨ξ, rfl⟩)

theorem phiQ_bijective (x : PlaneFaces N) : Function.Bijective (phiQ N n x) := by
  constructor
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    exact faceCuspidalEmbedding_injective N n _ ((pullQP'_bijective N n (planeFaceRepr x)).1 h1)
  · rintro ⟨y, hy⟩
    rw [dualCuspidalQ_jmath] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [faceCuspidalInH2_eq_range] at hz
    obtain ⟨ξ, rfl⟩ := hz
    exact ⟨ξ, rfl⟩

/-- `𝒞_Q(E) → H²(Γ_{ȷ(l)⁻¹Pȷ(l)}, E^∨)`: injection into `H²(Γ_{Q'}, E)` followed by the `ȷ`-pullback. -/
def phiP (i : LineFaces N) : lineFaceCuspidal N i.rep n →ₗ[ℂ] DPi N n i :=
  pullPQ' N n i.rep ∘ₗ lineFaceCuspidalEmbedding N i.rep n

/-- The `ȷ`-transport of the cuspidal data on the plane side: `∏_x 𝒞_{P'}(E) ≃ ∏_x 𝒞_Q(E^∨)`. -/
def PsiQ : (∀ x : PlaneFaces N, faceCuspidal N (planeFaceRepr x) n) ≃ₗ[ℂ] ∀ x : PlaneFaces N, QDJ N n x :=
  LinearEquiv.piCongrRight fun x => LinearEquiv.ofBijective (phiQ N n x) (phiQ_bijective N n x)

/-- The `ȷ`-transport of the line cuspidal data into the dual plane groups. -/
def PsiP : (∀ i : LineFaces N, lineFaceCuspidal N i.rep n) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i :=
  LinearMap.pi fun i => phiP N n i ∘ₗ LinearMap.proj i

end Global



theorem rPlane_eq_resToC (h : SL(3, ℤ)) (c : groupCohomology.H2 (gammaNRepAll N n)) :
    rPlane N n h c = resToC N n (ρ := gammaRhoC (gammaN N) n) (gammaNPAt N h) (gammaNPAt_le N h) c := rfl

theorem rLine_eq_resToC (h : SL(3, ℤ)) (c : groupCohomology.H2 (gammaNRepAll N n)) :
    rLine N n h c = resToC N n (ρ := gammaRhoC (gammaN N) n) (gammaNQAt N h) (gammaNQAt_le_N N h) c := rfl

section Result

variable [NeZero N]

/-- **The dual constant terms `r_Q ℰ_Q^∨(η) = η`, `r_P ℰ_Q^∨(η) = T^∨ η`, `r_B ℰ_Q^∨(η) = 0` for the faces of the dual construction, conditional on
canonicity of `T`** (`ClassicalLineConstantTerm`: `r_Q ℰ_P(ξ) = Tξ` for ONE linear `T` and every presentation of `ξ`).  The faces of type `Q` of the dual
construction are the `ȷ`-images of the plane faces, with representatives `ȷ(planeFaceRepr x)`; the faces of type `P` are the `ȷ`-images of the line faces, with
representatives `ȷ(LineFaces.rep i)`.  `T^∨ = ȷ^* ∘ T ∘ (ȷ^*)⁻¹` is a single linear map, independent of the presentation `u` of `η`; no invertibility or adjoint
normalization is assumed. -/
theorem dual_rP_eq_dualT_of_canonical (hN : 3 ≤ N) (hn : 4 ≤ n) (hT : TernaryPeriodPolynomials.Argument.FormClassK.ClassicalLineConstantTerm N n hn) :
    ∃ Td : (∀ x : PlaneFaces N, QDJ N n x) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i,
      ∀ (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (η : ∀ x : PlaneFaces N, QDJ N n x),
        (∀ x, (η x).1 = dualSeedHolC N n (u x false) (jmath (planeFaceRepr x)) +
            dualSeedConjC N n (u x true) (jmath (planeFaceRepr x))) →
        (∀ x, resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
            (gammaNQAt_le_N N (jmath (planeFaceRepr x))) (dualEJ N n hn u) = (η x).1) ∧
        (∀ i : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath i.rep))
            (gammaNPAt_le N (jmath i.rep)) (dualEJ N n hn u) = Td η i) ∧
        DualZeroFlags N n (dualEJ N n hn u) := by
  obtain ⟨T, hT⟩ := hT
  let eP := DirectSum.linearEquivFunOnFintype ℂ (PlaneFaces N) (fun x => faceCuspidal N (planeFaceRepr x) n)
  let eL := DirectSum.linearEquivFunOnFintype ℂ (LineFaces N) (fun i => lineFaceCuspidal N i.rep n)
  refine ⟨PsiP N n ∘ₗ eL.toLinearMap ∘ₗ T ∘ₗ eP.symm.toLinearMap ∘ₗ (PsiQ N n).symm.toLinearMap, fun u η hη => ?_⟩
  obtain ⟨hz, hpl⟩ := classicalPlaneConstantTerms N n hN hn u
  obtain ⟨⟨ξP, hξP⟩, -⟩ := exists_coordinates N n _ ((zeroFlags_iff_mixed N n hN _).1 hz)
  have hξ : planeCuspSumEmbedding N n ξP = seedBoundary N n u := hξP.trans hpl
  have hx : ∀ x, faceCuspidalEmbedding N n (planeFaceRepr x) (ξP x) = seedBoundary N n u x := fun x => by
    rw [← hξ]; rfl
  have hQ : ∀ x, (η x).1 = pullQP' N n (planeFaceRepr x) (seedBoundary N n u x) := fun x => by
    rw [hη x, seedBoundary_apply, dualSeedHolC_jmath, dualSeedConjC_jmath]
    exact ((pullQP' N n (planeFaceRepr x)).map_add _ _).symm
  have hηeq : PsiQ N n (eP ξP) = η := by
    funext x
    apply Subtype.ext
    change pullQP' N n (planeFaceRepr x) (faceCuspidalEmbedding N n (planeFaceRepr x) (ξP x)) = _
    rw [hx, hQ]
  have hL := hT u ξP hξ
  refine ⟨fun x => ?_, fun i => ?_, ?_⟩
  · have hpx : resToC N n (ρ := gammaRhoC (gammaN N) n) (gammaNPAt N (planeFaceRepr x))
        (gammaNPAt_le N (planeFaceRepr x)) (classCG N n hn u) = seedBoundary N n u x := by
      rw [← hpl, planeBoundary_apply]; rfl
    rw [dualEJ_eq]
    refine (resToC_dual_Q N n (planeFaceRepr x) (classCG N n hn u)).trans ?_
    rw [hQ x, hpx]
  · have e1 : (PsiQ N n).symm η = eP ξP := by rw [← hηeq]; exact LinearEquiv.symm_apply_apply _ _
    change _ = PsiP N n (eL (T (eP.symm ((PsiQ N n).symm η)))) i
    rw [e1, LinearEquiv.symm_apply_apply, dualEJ_eq]
    refine (resToC_dual_P N n i.rep (classCG N n hn u)).trans ?_
    change _ = pullPQ' N n i.rep (lineFaceCuspidalEmbedding N i.rep n ((T ξP) i))
    have h2 : lineFaceCuspidalEmbedding N i.rep n ((T ξP) i) = lineBoundary N n (classCG N n hn u) i := by
      rw [← hL]; rfl
    rw [h2, lineBoundary_apply]
    rfl
  · rw [← mem_dualZeroFlagsSubmodule]
    unfold dualEJ
    refine Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun b _ => ?_
    exact (mem_dualZeroFlagsSubmodule N n).2 (dualClassC_zeroFlags N n hN hn _ b _)

/-- **Every `η ∈ 𝒞_Q(E^∨)` is the dual seed vector of a tuple of cusp forms** (Eichler-Shimura spanning, S4's `mem_dualCuspidalQ_iff_seeds`). -/
theorem dual_seed_exists (η : ∀ x : PlaneFaces N, QDJ N n x) :
    ∃ u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), ∀ x, (η x).1 =
      dualSeedHolC N n (u x false) (jmath (planeFaceRepr x)) + dualSeedConjC N n (u x true) (jmath (planeFaceRepr x)) := by
  have h1 : ∀ x : PlaneFaces N, ∃ f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), (η x).1 =
      dualSeedHolC N n f (jmath (planeFaceRepr x)) + dualSeedConjC N n g (jmath (planeFaceRepr x)) := fun x =>
    (mem_dualCuspidalQ_iff_seeds N n (jmath (planeFaceRepr x)) _).1 (η x).2
  choose F G hFG using h1
  exact ⟨fun x b => if b then G x else F x, hFG⟩

/-- **`eq:dualconstantterms` for `Γ(N)`, conditional on canonicity of `T`**: a single linear `T^∨` such that every `η ∈ 𝒞_Q(E^∨)` is the line coordinate of a
global class `ℰ^∨(η)` with zero flag restrictions and plane coordinate `T^∨ η`. -/
theorem dual_constant_terms_all (hN : 3 ≤ N) (hn : 4 ≤ n)
    (hT : TernaryPeriodPolynomials.Argument.FormClassK.ClassicalLineConstantTerm N n hn) :
    ∃ Td : (∀ x : PlaneFaces N, QDJ N n x) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i,
      ∀ η : ∀ x : PlaneFaces N, QDJ N n x, ∃ c : groupCohomology.H2 (Rep.of (dualRhoC N n)),
        (∀ x, resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
            (gammaNQAt_le_N N (jmath (planeFaceRepr x))) c = (η x).1) ∧
        (∀ i : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath i.rep))
            (gammaNPAt_le N (jmath i.rep)) c = Td η i) ∧ DualZeroFlags N n c := by
  obtain ⟨Td, hTd⟩ := dual_rP_eq_dualT_of_canonical N n hN hn hT
  refine ⟨Td, fun η => ?_⟩
  obtain ⟨u, hu⟩ := dual_seed_exists N n η
  exact ⟨dualEJ N n hn u, hTd u η hu⟩

end Result



end TernaryPeriodPolynomials.Argument.EisensteinDual
