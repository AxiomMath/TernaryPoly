module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.FiniteChartPartition
public import Mathlib.Geometry.Manifold.Algebra.Structures

@[expose] public section


/-! A finite compact smooth scalar partition equal to one near an actual compact quotient set. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothDeRhamGluing SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpacePositive SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold Topology

theorem exists_finite_compact_scalar_partition (K : Set OrbitSpace) (hK : IsCompact K) :
    ∃ s : Finset Space, ∃ ψ : s → OrbitSpace → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ (quotientChart i.val).source) ∧
      (∀ i q, ψ i q ∈ Icc (0 : ℝ) 1) ∧
      ∃ U : Set OrbitSpace, IsOpen U ∧ K ⊆ U ∧
        ∀ q ∈ U, ∑ i, ψ i q = 1 := by
  classical
  obtain ⟨T, hTc, hKT⟩ := exists_compact_superset hK
  obtain ⟨β, hβ1, hβ0, hβr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Coordinates) (n := ⊤) hK.isClosed hKT
  have hβs : tsupport (β : OrbitSpace → ℝ) ⊆ T := by
    apply closure_minimal _ hTc.isClosed
    intro q hq
    by_contra h
    exact hq (hβ0 q h)
  have hβc : HasCompactSupport (β : OrbitSpace → ℝ) :=
    hTc.of_isClosed_subset isClosed_closure hβs
  obtain ⟨s, φ, hφ⟩ := exists_finite_chart_partition (tsupport (β : OrbitSpace → ℝ)) hβc
  refine ⟨s, (fun i q => β q * φ i q), (fun i => β.contMDiff.mul (φ i).contMDiff),
    (fun i => hβc.mul_right), (fun i => tsupport_mul_subset_right.trans (hφ i)), ?_, ?_⟩
  · intro i q
    exact ⟨mul_nonneg (hβr q).1 (φ.nonneg i q),
      (mul_le_mul_of_nonneg_left (φ.le_one i q) (hβr q).1).trans (by simpa using (hβr q).2)⟩
  · obtain ⟨U, hU, hKU, hU1⟩ := mem_nhdsSet_iff_exists.mp hβ1
    refine ⟨U, hU, hKU, ?_⟩
    intro q hq
    have hb : β q = 1 := hU1 hq
    have hqs : q ∈ tsupport (β : OrbitSpace → ℝ) := subset_closure (show β q ≠ 0 by rw [hb]; exact one_ne_zero)
    simpa only [hb, one_mul, finsum_eq_sum_of_fintype] using φ.sum_eq_one hqs

end TernaryPoly.PolynomialFormCoordinates
