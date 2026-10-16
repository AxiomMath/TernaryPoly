module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FaceOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FlagDictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineLevelDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineLemmaC3
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.C5Reduction

@[expose] public section


/-!
# Face assertions of Appendix C at level `Γ(N)`: surjectivity, orbits, direct sums, flags, level descent, Proposition C.5

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.
This completes the `Γ(N)` face data of `Exports/GammaNFaces` (line faces and flags, edge injectivity, nonmixed exclusion):

* **F6** `lineFaceEdge_surjective`, `faceEdge_surjective`: the Hochschild-Serre edge is a bijection `ker(res_N) ≃ H¹(L, H¹(N, E))` for every
  line and plane cusp of `Γ(N)` (`H²` of the Levi vanishes); hence `𝒞_Q(E) → H²(Γ_Q, E)` is an injection with image exactly
  `lineFaceCuspidalInH2` (`lineFaceCuspidalInH2_eq_range`, `faceCuspidalInH2_eq_range`);
* **F3, F4** `LineFaces N` (`Γ(N)`-orbits of rational lines), `lineFaces_finite`, `exists_lineFace_rep`, `lineFaceCuspidalInH2_orbit`,
  `lineFaceCuspidalInH2_of_rel`, and the direct sums `LineCuspSum N n = ⨁_{faces} 𝒞_{Q'}(E)`, `PlaneCuspSum N n = ⨁_{faces} 𝒞_{P'}(E)` with their
  injections into `⨁ H²` (`lineCuspSumEmbedding_injective`, `mem_range_lineCuspSumEmbedding`, and the plane analogues);
* **flag dictionary** (R5 3.5): the stabilizer of the flag of every frame `F ∈ GL₂(ℚ)` over a plane or line cusp is a flag group `gammaNBAt N (q h)`
  (`faceFlagStab_map_exists_gammaNBAt`, `lineFlagStab_map_exists_gammaNBAt`, `range_faceFlagStab_map`, `range_lineFlagStab_map`);
* **F9 for line faces** `locallyInnerClasses_lineFlag_iff`, `locallyInnerClasses_lineFlag_eq_transfer`,
  `mem_map_locallyInnerClasses_lineFlag_iff`, `lemma_C3_final_sentence_line`: the comparison `Γ(N) ⊂ K†` by invariants for lines (the line analogue of
  `Statements.LemmaC3Final`);
* **Proposition C.5 at level `Γ(N)`** (G7): `ZeroFlags` `⟺` `MixedCuspidalRestrictions`, `PropC5GammaN`, and `propC5_gammaN_of_obligations`, which reduces it to
  four exact named inputs (`GammaNC5Obligations`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.GammaNFacesFull

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.SeedC3S4c

alias line_edge_surjective := lineFaceEdge_surjective
alias plane_edge_surjective := faceEdge_surjective
alias line_cuspidal_range := lineFaceCuspidalInH2_eq_range
alias plane_cuspidal_range := faceCuspidalInH2_eq_range
alias line_faces_finite := lineFaces_finite
alias line_cuspidal_orbit := lineFaceCuspidalInH2_orbit
alias line_flag_level_descent := locallyInnerClasses_lineFlag_iff
alias line_flag_transfer := locallyInnerClasses_lineFlag_eq_transfer
alias zero_flags_iff_mixed := zeroFlags_iff_mixed
alias prop_C_5_gammaN_of_obligations := propC5_gammaN_of_obligations

/-- **Face data of `Γ(N)` (G6).**  For `N ≥ 3`: (1) the Hochschild-Serre edges of all line and plane cusps are bijective; (2) the groups
`lineFaceCuspidalInH2`, `faceCuspidalInH2` are the images of the injections of `𝒞_Q(E)`, `𝒞_P(E)`; (3) the sets of faces are finite; (4) the direct
sums embed into the face cohomology and the embeddings are injective. -/
theorem gammaN_faces_full (N : ℕ) [NeZero N] (n : ℕ) :
    (∀ h : SL(3, ℤ), Function.Bijective (lineFaceEdge N h n) ∧ Function.Bijective (faceEdge N h n)) ∧
    (∀ h : SL(3, ℤ), lineFaceCuspidalInH2 N h n = LinearMap.range (lineFaceCuspidalEmbedding N h n) ∧
      faceCuspidalInH2 N h n = LinearMap.range (faceCuspidalEmbedding N n h)) ∧
    Finite (LineFaces N) ∧ Finite (PlaneFaces N) ∧
    Function.Injective (lineCuspSumEmbedding N n) ∧ Function.Injective (planeCuspSumEmbedding N n) :=
  ⟨fun h => ⟨⟨lineFaceEdge_injective N h n, lineFaceEdge_surjective N h n⟩,
      ⟨faceEdge_injective N h n, faceEdge_surjective N h n⟩⟩,
    fun h => ⟨lineFaceCuspidalInH2_eq_range N h n, faceCuspidalInH2_eq_range N n h⟩,
    lineFaces_finite N, planeFaces_finite N, lineCuspSumEmbedding_injective N n,
    planeCuspSumEmbedding_injective N n⟩

end TernaryPeriodPolynomials.Argument.Statements.GammaNFacesFull
