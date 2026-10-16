module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Orientation
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Assembly

@[expose] public section


/-!
# Nonvanishing of the Stokes sums: the precise analytic input

Formalized by Claude Sonnet 5.5.

`exists_nonzero_line_sum`: if a global class `c` with zero flag restrictions has NONZERO line boundary `r_Q c`, then there is a dual class `c' ∈ Hd` (an admissible dual Eisenstein class) with
`∑_Q ⟨r_Q c, r_Q c'⟩_Q ≠ 0` (the dual line restriction of `c'` is chosen from the perfectness of the canonical line pairing, and `dualEisenstein_gammaN`).  With the literal Stokes lemma this gives a nonzero plane sum, and therefore
`orientation_signs_forced'`: the relative orientation sign is forced as soon as ONE zero-flag class has a nonzero line boundary, i.e. the constant-term map `T` of Proposition C.5 is nonzero.  This last input is analytic
(nonvanishing of an Eisenstein constant term, `real_constant_term_nonvanishing`); it is not available at level `Γ(N)` in the library.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

variable {N n : ℕ} [NeZero N]

theorem exists_nonzero_line_sum (hN : 3 ≤ N) (hn : 4 ≤ n) (c : groupCohomology.H2 (gammaNRepAll N n))
    (hz : ZeroFlags N n c) (hc : lineBoundary N n c ≠ 0) :
    ∃ c' : Hd (N := N) (n := n) hn,
      ∑ i : LineFaces N, canAtClass N i.rep n hN c hz (toLiteralG N n c'.1) (hdZero n hN hn c') ≠ 0 := by
  obtain ⟨ξQ, hξQ⟩ := (exists_coordinates N n c ((zeroFlags_iff_mixed N n hN c).1 hz)).2
  have hξ0 : ξQ ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hξQ, map_zero])
  obtain ⟨i, hi⟩ : ∃ i, ξQ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ0 (DFinsupp.ext h)
  obtain ⟨b, hb⟩ : ∃ b, (qdiAlignmentInst (M := N) (n := n)).pairQ hN i (ξQ i) b ≠ 0 := by
    by_contra h
    push Not at h
    exact hi ((qdiAlignmentInst (M := N) (n := n)).pairQ_perfect hN i (ξQ i) h)
  obtain ⟨Td, hTd⟩ := dualEisenstein_gammaN (N := N) (n := n) hN hn
  obtain ⟨c', hc'⟩ := (hTd (DirectSum.lof ℂ (LineFaces N) (fun i => QDi N n i) i b))
  refine ⟨c', ?_⟩
  have e : ∀ i' : LineFaces N, canAtClass N i'.rep n hN c hz (toLiteralG N n c'.1) (hdZero n hN hn c') =
      (qdiAlignmentInst (M := N) (n := n)).pairQ hN i' (ξQ i') ((dualRQ hN hn c') i') :=
    fun i' => canAtClass_rep_eq hN hn c hz ξQ hξQ c' i'
  simp only [e]
  rw [Finset.sum_eq_single i]
  · rw [hc'.1]
    simpa [DirectSum.lof_eq_of] using hb
  · intro j _ hj
    rw [hc'.1, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj, map_zero]
  · simp

/-- **The relative orientation sign is forced, given one zero-flag class with nonzero line boundary** (the constant-term map `T` of Proposition C.5 is nonzero). -/
theorem orientation_signs_forced' (hN : 3 ≤ N) (hn : 4 ≤ n) (hS : StokesGammaNLiteral N n hN) (εP εQ : ℂ)
    (h : ∀ (c₀ : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c₀)
      (c₀' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c₀'),
      εP * ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN c₀ hz c₀' hz' +
        εQ * ∑ i : LineFaces N, canAtClass N i.rep n hN c₀ hz c₀' hz' = 0)
    (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c) (hc : lineBoundary N n c ≠ 0) : εP + εQ = 0 := by
  obtain ⟨c', hc'⟩ := exists_nonzero_line_sum hN hn c hz hc
  refine orientation_signs_forced hN hS εP εQ h c hz (toLiteralG N n c'.1) (hdZero n hN hn c') ?_
  have h1 := hS c hz (toLiteralG N n c'.1) (hdZero n hN hn c')
  simp only [planeFaceOrientationSign, lineFaceOrientationSign, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at h1
  intro hP
  apply hc'
  linear_combination hP - h1

end TernaryPeriodPolynomials.Argument
