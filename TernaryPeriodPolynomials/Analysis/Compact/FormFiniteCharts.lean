module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingPartitionSupport
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingSupport
public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.FiniteChartPartition

@[expose] public section


/-! Genuine finite chart decomposition of compact polynomial-coefficient forms. -/
noncomputable section
namespace TernaryPoly.CompactFormFiniteCharts
open SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SmoothCoveringDeRham SmoothLocalDeRham SmoothDeRhamGluing
open Set
open scoped ContDiff Manifold

/-- Every genuine quotient-compact form is a finite sum of forms supported compactly in single charts. -/
theorem exists_finite_chart_decomposition {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : Representation ℝ DeckGroup F) (k : ℕ)
    (w : CompactSupportForm ρ univ k) :
    ∃ s : Finset Space, ∃ a : s → CompactSupportForm ρ univ k,
      (∀ S, quotientSupport (a S).val ⊆ (quotientChart S.val).source) ∧ ∑ S, a S = w := by
  classical
  obtain ⟨s, φ, hφ⟩ := PolynomialFormCoordinates.exists_finite_chart_partition (quotientSupport w.val) w.property.1
  let a : s → CompactSupportForm ρ univ k := fun S =>
    compactScalarMultiply (φ S) (φ S).contMDiff.contMDiffOn k w
  refine ⟨s, a, ?_, ?_⟩
  · intro S
    exact (quotientSupport_scalarMultiply_subset_tsupport (φ S) (φ S).contMDiff.contMDiffOn w.val).trans (hφ S)
  · apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x hx
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ S : s, (φ S) (coordinateProjection x) • w.val.val.val x) = w.val.val.val x
    by_cases hw : w.val.val.val x = 0
    · simp only [hw, smul_zero, Finset.sum_const_zero]
    · have hsum := φ.sum_eq_one (subset_closure ⟨x, hw, rfl⟩)
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [← Finset.sum_smul, hsum, one_smul]

end TernaryPoly.CompactFormFiniteCharts
