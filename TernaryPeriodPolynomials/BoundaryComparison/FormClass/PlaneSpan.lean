module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.T
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlane
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.Span
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.Intertwiner.Printed

@[expose] public section


/-!
# L9: the plane coordinate of a locally inner class is a finite sum of plane source classes; the printed intertwiner on sums

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 (end of proof), Proposition C.5 and `eq:intertwiner`.

* `innerBoundary_plane_mem_span`: `InnerBoundary plane ξ → ξ ∈ automorphicPlaneSpan n` for `0 < n`, extracted from `constant_terms`
  (`CuspidalSpan/GlobalRealization.lean:`): `ξ = ξ' + (ξ - ξ')` with `good_plane_cuspidal_span` and `bad_plane_cuspidal_span`.
* `mem_span_exists_sourceClass_sum`: finite source-class representation of an element of `automorphicPlaneSpan n`.
* `T0_sum_printed`: `T₀ (∑ [plane_i]) = ∑ [sourceStandard plane_i]` (linearity and the `T0_eq_printed`).
* **`formClass_line_eq_printedT_sum`**: for the classical series (hypothesis `SeriesRestrictionInSeedSpan` for each summand, as in M3) there is a finite family of
  sources with plane coordinate `∑ [plane_i]` and line coordinate `∑ [sourceStandard plane_i]`.  The family is existential; identifying it with the seeds
  of the series is the separate coordinate dictionary (the per-cusp values and `Statements.LemmaC3Final`).
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.CuspidalSpan
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- **Inner plane classes lie in the span of the seeds.**  Every mixed cuspidal plane class `ξ` (`InnerBoundary` on the plane) of
positive degree is a combination of plane source classes of paper data: the decomposition `ξ = ξ' + (ξ - ξ')` of
`constant_terms` (`GlobalRealization.lean:`), with `ξ'` from `good_plane_cuspidal_span` and `ξ - ξ'` from
`bad_plane_cuspidal_span`.  Only `0 < n` is used. -/
theorem innerBoundary_plane_mem_span (n : ℕ) (hn : 0 < n) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) : ξ ∈ automorphicPlaneSpan n := by
  obtain ⟨ξ', hξ'mem, hξ'good⟩ := TernaryPeriodPolynomials.good_plane_cuspidal_span n hn ξ hξ
  have hξ'inner : InnerBoundary n trivialCharacter .plane ξ' :=
    automorphicPlaneSpan_subset_innerBoundary hξ'mem
  have hdiff_inner : InnerBoundary n trivialCharacter .plane (ξ - ξ') := by
    rw [innerBoundary_iff_endpointH2] at hξ hξ'inner ⊢
    rw [map_sub, hξ, hξ'inner, sub_zero]
  have hdiff := TernaryPeriodPolynomials.bad_plane_cuspidal_span n hn (ξ - ξ') hξ'good hdiff_inner
  have := Submodule.add_mem _ hξ'mem hdiff
  simpa using this

/-- **Finite source-class representation.**  An element of `automorphicPlaneSpan n` is a finite sum of plane source classes of
paper data (scalars absorbed into the sources; the empty sum is `0`). -/
theorem mem_span_exists_sourceClass_sum (n : ℕ) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : ξ ∈ automorphicPlaneSpan n) :
    ∃ (ι : Type) (_ : Fintype ι) (D : ι → CohomologicalCuspData n)
      (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane),
      ξ = ∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i) := by
  unfold automorphicPlaneSpan at hξ
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨D, hD⟩ := hx
    rw [← SourceSpace.sourceClass_range D.inducingData .plane] at hD
    obtain ⟨p, rfl⟩ := hD
    exact ⟨Unit, inferInstance, fun _ => D, fun _ => p, by simp⟩
  | zero => exact ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨ι, _, D, p, rfl⟩ := hx
    obtain ⟨κ, _, E, q, rfl⟩ := hy
    exact ⟨ι ⊕ κ, inferInstance, Sum.elim D E, fun i => Sum.casesOn i p q, by rw [Fintype.sum_sum_type]; rfl⟩
  | smul a x _ hx =>
    obtain ⟨ι, _, D, p, rfl⟩ := hx
    refine ⟨ι, inferInstance, D, fun i => a • p i, ?_⟩
    simp [Finset.smul_sum]

section Printed

open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.ConvergenceC4

variable (n : ℕ)

/-- **The printed intertwiner on a finite sum of plane source classes**: by linearity of `T₀` and `T0_eq_printed`. -/
theorem T0_sum_printed (hn : 4 ≤ n) {ι : Type} [Fintype ι] (D : ι → CohomologicalCuspData n)
    (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane) :
    (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose
        (∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i)) =
      ∑ i, SourceSpace.sourceClass (D i).inducingData .line
        (EndpointSourceStandard.sourceStandard (D i).inducingData hn
          (planeEisensteinConvergent hn (D i).inducingData) (p i)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => PrintedIntertwiner.T0_eq_printed (D i) hn (p i)

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) [Fintype (PlaneFaces N)]

/-- **`r_Q = T r_P` with the printed intertwiner, for the classical series, with no hypothesis on the plane coordinate.**  The plane
coordinate of the `K†`-corestriction is mixed cuspidal (`PlaneLocallyInner`), so it lies in the span of the plane seeds
(`innerBoundary_plane_mem_span`), i.e. is a finite sum of plane source classes, and the line coordinate is the corresponding finite sum
of the printed integrals `sourceStandard` (`eq:intertwiner`).  The finite family is existential: it is NOT identified with the seeds of
the series `f` (that is the separate coordinate dictionary). -/
theorem formClass_line_eq_printedT_sum (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (hS : ∀ x b, SeriesRestrictionInSeedSpan N n hn (f x b) x b)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, complexify (gammaN N) n
        (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b)
          (Quotient.out x) b hn))) :
    ∃ (ι : Type) (_ : Fintype ι) (D : ι → CohomologicalCuspData n)
      (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane),
      (globalCoordinates n trivialCharacter c).1 =
          ∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i) ∧
        (globalCoordinates n trivialCharacter c).2 =
          ∑ i, SourceSpace.sourceClass (D i).inducingData .line
            (EndpointSourceStandard.sourceStandard (D i).inducingData hn
              (planeEisensteinConvergent hn (D i).inducingData) (p i)) := by
  have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
    intro e
    rw [hc]
    exact classK_edge_vanishing N h3 hN n _ (formClass_planeLocallyInner N n h3 hN hn f hS) e
  have hin : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 :=
    innerBoundary_of_edgeVanishing n trivialCharacter .plane c he
  obtain ⟨ι, _, D, p, hp⟩ := mem_span_exists_sourceClass_sum n _
    (innerBoundary_plane_mem_span n (by omega) _ hin)
  refine ⟨ι, inferInstance, D, p, hp, ?_⟩
  rw [formClass_line_eq_T0 N h3 hN n hn f hS c hc, hp]
  exact T0_sum_printed n hn D p

end Printed

end TernaryPeriodPolynomials.Argument.FormClassK
