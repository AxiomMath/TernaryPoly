module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.LevelN
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QDiAlignInst
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PropC5Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PropC5Printed

@[expose] public section


/-!
# Proposition C.5 at `Γ(N)` by the paper's route, with the literal Stokes lemma as the Stokes input

Formalized by Claude Sonnet 5.5.  (Proposition `ar:prop:graph`, "pair with `ℰ_Q^∨(η)` in Lemma C.2, pair `ℰ_P(ξ_P)` with the same class, subtract, use the perfect line pairing").

The paper's argument is already formalised as `propC5_gammaN_of_obligations` (`GammaNC5Obligations`; per face `GammaNC5FaceObligations`) with the descent from a common level `M` (`propC5_of_face_obligations_at_level`).  Its fields are instantiated by
`eisensteinP_gammaN` (Eisenstein existence), `dualEisenstein_gammaN` (dual series), `qdiAlignmentInst` and `pairQfaceCan_perfect` (the canonical perfect line pairings), and the Stokes field `StokesAtLevel`.  Here it is derived from the literal Stokes lemma `StokesGammaNLiteral` of the canonical pairings:

* `stokesAtLevel_of_literal`: `StokesGammaNLiteral M n hM` implies `StokesAtLevel hM hn qdiAlignmentInst` (plane pairing `pairP = -∑_j pairPfaceCan(·, ψ_j ·)`, the sign being the relative orientation `ε_P = -ε_Q`).
* `propC5_gammaN_paperRoute`: Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`, with the Stokes input `stokes_gammaN_literal_uncond` at the level `lcm(N, 6)` and no abstract obligation left.
* `propC5_gammaN_printed_paperRoute`: the printed-`T` form (`propC5_gammaN_printed`) with the uniqueness clause supplied by the paper's route.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction
open TernaryPeriodPolynomials.Argument.EisensteinClass

section Stokes

variable {M n : ℕ} [NeZero M]

/-- **`StokesAtLevel` from the literal Stokes lemma.**  The line pairings are the canonical ones transported along `qdiAlignmentInst`; the plane pairing is
`-∑_j pairPfaceCan(·, ψ_j ·)` (`ψ_j` the identification of the dual plane restriction with the cuspidal group of the literal dual).  For `c₀` with zero flags and a dual Eisenstein class `c'`,
`StokesGammaNLiteral` reads `∑_P can - ∑_Q can = 0`, which is the stated relation. -/
theorem stokesAtLevel_of_literal (hM : 3 ≤ M) (hn : 4 ≤ n) (hS : StokesGammaNLiteral M n hM) :
    StokesAtLevel hM hn (qdiAlignmentInst (M := M) (n := n)) := by
  choose ψ hψ using fun j : PlaneFaces M => exists_planeDualMap n hM hn j
  let pP : ∀ j : PlaneFaces M, faceCuspidal M (planeFaceRepr j) n →ₗ[ℂ]
      groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j))))) →ₗ[ℂ] ℂ :=
    fun j => (pairPfaceCan n hM (planeFaceRepr j)).compl₂ (ψ j)
  refine ⟨(-1 : ℂ) • sumPairing _ _ pP, ?_⟩
  intro c₀ hz ξP ξQ hξP hξQ c'
  have hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual (toLiteralG M n c'.1) := hdZero n hM hn c'
  have h := hS c₀ hz (toLiteralG M n c'.1) hz'
  simp only [planeFaceOrientationSign, lineFaceOrientationSign, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at h
  have hP : ∑ j : PlaneFaces M, canAtClassP M (planeFaceRepr j) n hM c₀ hz (toLiteralG M n c'.1) hz' =
      sumPairing _ _ pP ξP (dualRP hn c') := by
    rw [sumPairing_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e : canAtClassP M (planeFaceRepr j) n hM c₀ hz (toLiteralG M n c'.1) hz' =
        pairPfaceCan n hM (planeFaceRepr j) (ξP j) (ψ j ((dualRP hn c') j)) := by
      unfold canAtClassP canAtP
      rw [planeEdge_planeClass n (planeFaceRepr j) hM c₀ hz (ξP j) (planeEmb_component n c₀ ξP hξP j), hψ j c']
      rfl
    simp only [pP, LinearMap.compl₂_apply]
    exact e
  have hQ : ∑ i : LineFaces M, canAtClass M i.rep n hM c₀ hz (toLiteralG M n c'.1) hz' =
      sumPairing _ _ ((qdiAlignmentInst (M := M) (n := n)).pairQ hM) ξQ (dualRQ hM hn c') := by
    rw [sumPairing_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact canAtClass_rep_eq hM hn c₀ hz ξQ hξQ c' i
  rw [hP, hQ] at h
  simp only [LinearMap.smul_apply, smul_eq_mul]
  linear_combination (-1 : ℂ) * h

end Stokes

section Main

variable {N n : ℕ} [NeZero N]

/-- **Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`, by the paper's route**: Eisenstein existence at `N` and at `M = lcm(N, 6)`, the dual series at `M`, the perfect canonical line pairings, and the literal Stokes lemma
`stokes_gammaN_literal_uncond` at `M`; no abstract obligation remains. -/
theorem propC5_gammaN_paperRoute (hN : 3 ≤ N) (hn : 4 ≤ n) : PropC5GammaN N n :=
  propC5_gammaN_of_stokes_lcm hN hn
    (stokesAtLevel_of_literal (three_le_lcm hN) hn (stokes_gammaN_literal_uncond (three_le_lcm hN) hn))

/-- The printed-`T` form of Proposition C.5 (`propC5_gammaN_printed`), with the uniqueness clause supplied by the paper's route. -/
theorem propC5_gammaN_printed_paperRoute (hN : 3 ≤ N) (hn : 4 ≤ n) :
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
  obtain ⟨T0, -, hu⟩ := propC5_gammaN_paperRoute hN hn
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

end Main

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
