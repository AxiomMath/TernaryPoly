module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryHeckeDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeGoodCusps
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.ClusterDetection
public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.PlaneSpanDecomposition
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlane
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison

@[expose] public section


/-!
# The core of Appendix C.6 along the paper route, without isotypical-projector existence

For `n ≥ 4` and `T₀ = (line_constant_term_comparison n hn).choose`: an inner plane class `ξ` vanishing at the good plane whose image `T₀ ξ`
vanishes at the good line is zero.

1. `bad_plane_cuspidal_span` writes `ξ = ∑_D f D`, `f D ∈ boundarySummand D` (finite sum, `PlaneSpanDecomposition`).
2. The pair-level classes `c D = (f D, T₀ (f D))` lie in `associatePair D`, on which every away-three Hecke operator
   acts by the scalar `pairCharacter D` (`pairCharacter_spec`); the sum `∑ c D = (ξ, T₀ ξ)` vanishes on the good cusps.
3. Hecke operators preserve good-cusp vanishing (`away_three_hecke_good_cusps`), so by `HeckeCluster.cluster_mem`
   (Lagrange interpolation in the Hecke operators) the sum over each pair-character class vanishes on the good cusps.
4. `ClusterDetection.cluster_zero` (explicit entry scalar, multiplicity one at the bad-plane cusp) kills each class sum;
   `HeckeCluster.sum_eq_zero_of_classwise_zero'` assembles.

No `BadPlaneInjectivity.Ported*` input (existence of the isotypical projector of `EigenSeparated`) is used: the
projector is replaced by the explicit polynomial in the Hecke operators of step 3.  `T₀` is `line_constant_term_comparison`'s map, the plane
Eisenstein hypothesis `planeEisensteinConvergent`, the Hecke witness `boundary_hecke_descent`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein
open Homogeneous Adelic


namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd
open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

/-- **Appendix C.6 core along the paper route.** -/
theorem appendix_C6_core_ms (n : ℕ) (hn : 4 ≤ n)
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line
      ((TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose ξ)) : ξ = 0 := by
  classical
  set T₀ := (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose with hT₀def
  have hT₀ : IsUniquenessMap n trivialCharacter T₀ :=
    (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2
  have hspan : ξ ∈ automorphicPlaneSpan n :=
    TernaryPeriodPolynomials.bad_plane_cuspidal_span n (by omega) ξ hgood hξ
  obtain ⟨f, hf, hsum⟩ := exists_finsupp_of_mem_automorphicPlaneSpan n ξ hspan
  have hhol : ∀ D : CohomologicalCuspData n, PlaneEisensteinConvergent D.inducingData := fun D =>
    planeEisensteinConvergent (by omega) D.inducingData
  obtain ⟨hecke, hhecke⟩ :=
    TernaryPeriodPolynomials.BoundaryHeckeDescent.boundary_hecke_descent n trivialCharacter
  -- pair-level classes
  let c : CohomologicalCuspData n → BoundaryCoordinates n trivialCharacter := fun D => (f D, T₀ (f D))
  have hc : ∀ D ∈ f.support, c D ∈ associatePair D.inducingData := by
    intro D _
    have hTmem : T₀ (f D) ∈ boundarySummand D.inducingData .line :=
      T₀_mapsTo_std D hn (hhol D) T₀ hT₀ (⟨f D, hf D⟩ : boundarySummand D.inducingData .plane)
    exact Submodule.mem_prod.mpr ⟨hf D, hTmem⟩
  have hsum_eq : (∑ D ∈ f.support, c D) = (ξ, T₀ ξ) := by
    apply Prod.ext
    · show (∑ D ∈ f.support, c D).1 = ξ
      rw [Prod.fst_sum, ← hsum]; rfl
    · show (∑ D ∈ f.support, c D).2 = T₀ ξ
      rw [Prod.snd_sum, ← hsum, map_finsuppSum]; rfl
  have hgood_total : GoodBoundaryVanishing n trivialCharacter (∑ D ∈ f.support, c D) := by
    rw [hsum_eq]; exact ⟨hgood, hline⟩
  -- fiberwise vanishing
  have hclass : ∀ D₀ ∈ f.support,
      ∑ D ∈ f.support.filter (fun D => pairChar hecke hhecke D = pairChar hecke hhecke D₀), f D = 0 := by
    intro D₀ hD₀
    have hW : ∀ j : {t : HeckeCorrespondence // AwayThree t}, ∀ x ∈ goodBoundarySubmodule n trivialCharacter,
        pairHecke D₀.inducingData hecke j.1 x ∈ goodBoundarySubmodule n trivialCharacter := fun j x hx =>
      (mem_goodBoundarySubmodule n trivialCharacter _).mpr
        (TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.away_three_hecke_good_cusps
          n (by omega) D₀.inducingData hecke hhecke j.1 j.2 x hx)
    have heig : ∀ D ∈ f.support, ∀ j : {t : HeckeCorrespondence // AwayThree t},
        pairHecke D₀.inducingData hecke j.1 (c D) = pairChar hecke hhecke D j • c D := by
      intro D hD j
      exact TernaryPeriodPolynomials.Spectral.pairCharacter_spec D.inducingData hecke hhecke
        j.1 j.2 (c D) (hc D hD)
    have hcl := cluster_mem (goodBoundarySubmodule n trivialCharacter)
      (fun j => pairHecke D₀.inducingData hecke j.1) hW f.support c (pairChar hecke hhecke) heig
      ((mem_goodBoundarySubmodule n trivialCharacter _).mpr hgood_total) D₀
    rw [mem_goodBoundarySubmodule] at hcl
    have hpair : (∑ D ∈ f.support.filter (fun D => pairChar hecke hhecke D = pairChar hecke hhecke D₀), c D) =
        (∑ D ∈ f.support.filter (fun D => pairChar hecke hhecke D = pairChar hecke hhecke D₀), f D,
         T₀ (∑ D ∈ f.support.filter (fun D => pairChar hecke hhecke D = pairChar hecke hhecke D₀), f D)) := by
      apply Prod.ext
      · show (∑ D ∈ _, c D).1 = _
        rw [Prod.fst_sum]
      · show (∑ D ∈ _, c D).2 = _
        rw [Prod.snd_sum, map_sum]
    rw [hpair] at hcl
    refine cluster_zero n hn hecke hhecke hhol T₀ hT₀ _ f (fun D hD => hf D) ?_ hcl.1 hcl.2
    intro D hD D' hD'
    rw [Finset.mem_filter] at hD hD'
    exact hD.2.trans hD'.2.symm
  have hzero : ∑ D ∈ f.support, f D = 0 :=
    sum_eq_zero_of_classwise_zero' f.support (pairChar hecke hhecke) f hclass
  rw [← hsum]
  exact hzero

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
