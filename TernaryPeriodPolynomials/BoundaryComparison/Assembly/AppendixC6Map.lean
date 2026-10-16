module

public import TernaryPeriodPolynomials.BoundaryComparison.Assembly.Detection
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryHeckeDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeGoodCusps
public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.PlaneSpanDecomposition
public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.TEliminate
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlane

@[expose] public section


/-!
# Appendix C.6 for an arbitrary uniqueness map, through the classical faces

* `appendix_C6_core_of_map`: the core of Appendix C.6 (`ξ` inner, zero at the good plane, `T₀ ξ` zero at the good
  line, hence `ξ = 0`) for an arbitrary `T₀` with `IsUniquenessMap n trivialCharacter T₀`, using
  `cluster_zero_classical` (detection through the classical faces and the R3 certificate).
* `appendix_C6_of_map`: exactly the statement of `bad_plane_data_injective` (`Targets/AppendixC6.lean`), via
  `appendix_C6_of_core` (`BadPlaneInjectivity/TEliminate.lean`).

This module imports neither `Targets.PropC5` nor `Targets.AppendixC6`.

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.
-/

open GeneralEisenstein
open Homogeneous Adelic


namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

/-- **Appendix C.6 core for an arbitrary uniqueness map `T₀`, through the classical faces.**  The copy of
`appendix_C6_core_ms` with `T₀ := (line_constant_term_comparison n hn).choose` generalized to any `T₀` satisfying the uniqueness clause
`IsUniquenessMap` (R1's `paperGraphMap` in the final assembly) and the detection `cluster_zero_classical` (through the
R3 certificate). -/
theorem appendix_C6_core_of_map (n : ℕ) (hn : 4 ≤ n)
    (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT₀ : IsUniquenessMap n trivialCharacter T₀)
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T₀ ξ)) : ξ = 0 := by
  classical
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
    refine cluster_zero_classical n hn hecke hhecke hhol T₀ hT₀ _ f (fun D hD => hf D) ?_ hcl.1 hcl.2
    intro D hD D' hD'
    rw [Finset.mem_filter] at hD hD'
    exact hD.2.trans hD'.2.symm
  have hzero : ∑ D ∈ f.support, f D = 0 :=
    sum_eq_zero_of_classwise_zero' f.support (pairChar hecke hhecke) f hclass
  rw [← hsum]
  exact hzero


/-- **`bad_plane_data_injective` for an arbitrary uniqueness map `T₀`.**  Exactly the statement of
`TernaryPeriodPolynomials.bad_plane_data_injective`, with the extra inputs `T₀`, `hT₀`. -/
theorem appendix_C6_of_map (n : ℕ) (hn : 4 ≤ n)
    (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT₀ : IsUniquenessMap n trivialCharacter T₀)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T ξ)) : ξ = 0 :=
  appendix_C6_of_core n T₀ hT₀
    (fun ξ' hξ' hgood' hline' => appendix_C6_core_of_map n hn T₀ hT₀ ξ' hξ' hgood' hline')
    T hT ξ hξ hgood hline

end TernaryPeriodPolynomials.Argument.BoundaryComparison
