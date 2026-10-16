module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Thom
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.Metrizable.Basic

@[expose] public section


/-!
# Locality for Poincaré duality: the Thom cochain of a thin tube

* `exists_tube_radius`: for a closed set `N` on which a continuous function `f` is positive there is a
  positive continuous function `ρ ≤ ε` with `ρ < f` on `N` (Tietze extension): the radius of a thin tube
  that avoids `N`.
* `exists_thom_pullback`: for a continuous map `g : E ⟶ ℝ³` there is a scalar 3-cochain `y = y₀ ∘ g_*`
  of `E` that is a cocycle, vanishes on simplices subordinate to `{‖g‖ > 1}`, and on a chain `c` with
  boundary over `{‖g‖ > 1}` takes the value `degR3 (g_* c)` (the local degree along `g`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open TopologicalSpace CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

/-- **Thin tube radius.**  A continuous positive radius below `ε` that stays below `f` on the closed set
`N` where `f > 0`. -/
theorem exists_tube_radius {E : Type*} [TopologicalSpace E] [MetrizableSpace E]
    (f : E → ℝ) (hfc : Continuous f) (N : Set E) (hN : IsClosed N) (hNf : ∀ s ∈ N, 0 < f s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : E → ℝ, Continuous ρ ∧ (∀ s, 0 < ρ s) ∧ (∀ s, ρ s ≤ ε) ∧ ∀ s ∈ N, ρ s < f s := by
  rcases N.eq_empty_or_nonempty with hNe | hNne
  · exact ⟨fun _ => ε, continuous_const, fun _ => hε, fun _ => le_rfl, by simp [hNe]⟩
  let _ : MetricSpace E := TopologicalSpace.metrizableSpaceMetric E
  have hcN : Continuous (fun s : N => f s / 2) := (hfc.comp continuous_subtype_val).div_const 2
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hN (⟨fun s : N => f s / 2, hcN⟩ : C(N, ℝ))
  have hFN : ∀ s ∈ N, F s = f s / 2 := by
    intro s hs
    have := congrArg (fun G : C(N, ℝ) => G ⟨s, hs⟩) hF
    simpa using this
  refine ⟨fun s => min ε (|F s| + Metric.infDist s N), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.min ((F.continuous.abs).add (Metric.continuous_infDist_pt N))
  · intro s
    by_cases hs : s ∈ N
    · have hpos := hNf s hs
      refine lt_min hε ?_
      rw [hFN s hs, abs_of_pos (by linarith)]
      have := Metric.infDist_nonneg (x := s) (s := N)
      linarith
    · refine lt_min hε ?_
      have hd : 0 < Metric.infDist s N := (hN.notMem_iff_infDist_pos hNne).mp hs
      have := abs_nonneg (F s)
      linarith
  · intro s; exact min_le_left _ _
  · intro s hs
    have hpos := hNf s hs
    calc min ε (|F s| + Metric.infDist s N) ≤ |F s| + Metric.infDist s N := min_le_right _ _
      _ = f s / 2 := by
        rw [hFN s hs, abs_of_pos (by linarith), Metric.infDist_zero_of_mem hs, add_zero]
      _ < f s := by linarith

/-- **The Thom cochain along a map to `ℝ³`.** -/
theorem exists_thom_pullback {E : TopCat.{0}} (g : E ⟶ TopCat.of R3) :
    ∃ y : singularChainGroup ℚ E 3 →ₗ[ℚ] ℚ,
      (∀ e : singularChainGroup ℚ E 4, y ((singularBoundary ℚ E 3).hom e) = 0) ∧
      (∀ τ : SingularSimplex E 3, IsSubordinate {s : E | 1 < ‖g s‖} τ →
        y (chainGenerator ℚ E 3 τ) = 0) ∧
      (∀ c : singularChainGroup ℚ E 3,
        (singularBoundary ℚ E 2).hom c ∈ subChainSubmodule ℚ E {s : E | 1 < ‖g s‖} 2 →
        ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ g 3).hom c)) = 0,
          y c = degR3 ((singularChainMap ℚ g 3).hom c) h) := by
  obtain ⟨y₀, hy₀d, hy₀v, hy₀c⟩ := exists_thom_cochain 1 zero_le_one
  refine ⟨y₀.comp (singularChainMap ℚ g 3).hom, ?_, ?_, ?_⟩
  · intro e
    rw [LinearMap.comp_apply]
    have h1 := singularChainMap_boundary_apply ℚ g 3 e
    have h2 : (singularChainMap ℚ g 3).hom ((singularBoundary ℚ E 3).hom e) =
        (singularBoundary ℚ (TopCat.of R3) 3).hom ((singularChainMap ℚ g 4).hom e) := h1.symm
    rw [h2]
    exact hy₀d _
  · intro τ hτ
    rw [LinearMap.comp_apply, singularChainMap_generator]
    apply hy₀v
    rw [isSubordinate_pushSimplex_iff]
    exact hτ
  · intro c hc
    have h1 := singularChainMap_boundary_apply ℚ g 2 c
    have hb : (singularBoundary ℚ (TopCat.of R3) 2).hom ((singularChainMap ℚ g 3).hom c) ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 := by
      have : (singularBoundary ℚ (TopCat.of R3) 2).hom ((singularChainMap ℚ g 3).hom c) =
          (singularChainMap ℚ g 2).hom ((singularBoundary ℚ E 2).hom c) := h1
      rw [this]
      exact singularChainMap_mem_sub g {v : R3 | 1 < ‖v‖} 2 hc
    exact hy₀c _ hb

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
