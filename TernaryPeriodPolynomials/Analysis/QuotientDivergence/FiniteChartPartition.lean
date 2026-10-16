module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingPartition

@[expose] public section

/-! A genuine finite chart-subordinate smooth partition near any compact quotient set. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open SmoothDeRhamGluing Set
open scoped ContDiff Manifold

theorem exists_finite_chart_partition (K : Set OrbitSpace) (hK : IsCompact K) :
    ∃ s : Finset Space, ∃ φ : SmoothPartitionOfUnity s 𝓘(ℝ, Coordinates) OrbitSpace K,
      φ.IsSubordinate (fun S => (quotientChart S.val).source) := by
  have hcover : K ⊆ ⋃ S : Space, (quotientChart S).source := by
    intro q _
    obtain ⟨S, hS⟩ := quotientCharts_cover q
    exact mem_iUnion.mpr ⟨S, hS⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun S : Space => (quotientChart S).source) (fun S => (quotientChart S).open_source) hcover
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    hK.isClosed (fun S : s => (quotientChart S.val).source)
    (fun S => (quotientChart S.val).open_source) (by
      intro q hq
      obtain ⟨S, hS, hqS⟩ := mem_iUnion₂.mp (hs hq)
      exact mem_iUnion.mpr ⟨⟨S, hS⟩, hqS⟩)
  exact ⟨s, φ, hφ⟩

end TernaryPoly.PolynomialFormCoordinates
