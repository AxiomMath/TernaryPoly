module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Tests
public import TernaryPeriodPolynomials.Analysis.Compact.FormFiniteCharts
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.OpenCharts

@[expose] public section

/-! Finite actual chart decomposition preserves the original intrinsic test domain. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpacePositive
  SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham SmoothDeRhamGluing
open scoped ContDiff Manifold

/-- The chart open of the genuine local chart domain is the original open intersected with the
actual chart source. -/
theorem intrinsicChartOpen_chartDomain (S : Space) (U : Set OrbitSpace) :
    chartOpen S (chartDomain S U) = U ∩ (quotientChart S).source := by
  ext q
  constructor
  · intro hq
    exact ⟨chartOpen_subset_of_chartDomain S Subset.rfl hq, hq.1⟩
  · intro hq
    refine ⟨hq.2, (quotientChart S).map_source hq.2, ?_⟩
    change (quotientChart S).symm (quotientChart S q) ∈ U
    simpa only [(quotientChart S).left_inv hq.2] using hq.1

/-- Finite chart partition of a genuine compact form preserves its genuine support. -/
theorem compactForm_finite_chart_decomposition_support {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (ρ : Representation ℝ DeckGroup F)
    (k : ℕ) (w : CompactSupportForm ρ univ k) :
    ∃ s : Finset Space, ∃ a : s → CompactSupportForm ρ univ k,
      (∀ S, quotientSupport (a S).val ⊆ quotientSupport w.val ∩ (quotientChart S.val).source) ∧
      ∑ S, a S = w := by
  classical
  obtain ⟨s, φ, hφ⟩ := PolynomialFormCoordinates.exists_finite_chart_partition
    (quotientSupport w.val) w.property.1
  let a : s → CompactSupportForm ρ univ k := fun S =>
    compactScalarMultiply (φ S) (φ S).contMDiff.contMDiffOn k w
  refine ⟨s, a, ?_, ?_⟩
  · intro S
    exact subset_inter (quotientSupport_scalarMultiply (φ S) (φ S).contMDiff.contMDiffOn w.val)
      ((quotientSupport_scalarMultiply_subset_tsupport (φ S) (φ S).contMDiff.contMDiffOn w.val).trans (hφ S))
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

/-- Every actual intrinsic compact test is a finite sum of actual tests supported both in its
original quotient domain and in individual genuine chart sources. -/
theorem supportedCompactCore_finite_chart_decomposition (n k : ℕ) (U : Set OrbitSpace)
    (w : supportedCompactCore n k U) :
    ∃ s : Finset Space, ∃ a : (S : s) → supportedCompactCore n k (U ∩ (quotientChart S.val).source),
      (∑ S : s, supportedCompactInclusion n k inter_subset_left (a S)) = w := by
  classical
  exact (compactForm_finite_chart_decomposition_support (deckRepresentation n) k w.val).elim
    (fun s hs => hs.elim (fun a ha => by
      let b (S : s) : supportedCompactCore n k (U ∩ (quotientChart S.val).source) :=
        ⟨a S, (ha.1 S).trans (inter_subset_inter_left _ w.property)⟩
      refine ⟨s, b, ?_⟩
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      change (∑ i : s, a i) = w.val
      exact ha.2))

/-- Intrinsic currents are separated by their restrictions to all actual chart sources. -/
theorem intrinsicCurrent_ext_chartSources (n k : ℕ) (U : Set OrbitSpace)
    (T R : IntrinsicCurrent n k U)
    (h : ∀ S : Space, intrinsicCurrentRestriction n k
      (inter_subset_left : U ∩ (quotientChart S).source ⊆ U) T =
      intrinsicCurrentRestriction n k inter_subset_left R) : T = R := by
  apply LinearMap.ext
  intro w
  exact (supportedCompactCore_finite_chart_decomposition n k U w).elim (fun s hs =>
    hs.elim (fun a ha => by
      have he : T (∑ S : s, supportedCompactInclusion n k inter_subset_left (a S)) =
          R (∑ S : s, supportedCompactInclusion n k inter_subset_left (a S)) := by
        simp only [map_sum]
        exact Finset.sum_congr rfl (fun S _ => LinearMap.congr_fun (h S.val) (a S))
      exact (congrArg T ha).symm.trans (he.trans (congrArg R ha))))

/-- Intrinsic currents are separated by restrictions to the actual chart domains of their
original quotient open. -/
theorem intrinsicCurrent_ext_chartDomains (n k : ℕ) (U : Set OrbitSpace)
    (T R : IntrinsicCurrent n k U)
    (h : ∀ S : Space, intrinsicCurrentRestriction n k
      (chartOpen_subset_of_chartDomain S (Subset.rfl : chartDomain S U ⊆ chartDomain S U)) T =
      intrinsicCurrentRestriction n k
        (chartOpen_subset_of_chartDomain S (Subset.rfl : chartDomain S U ⊆ chartDomain S U)) R) : T = R := by
  apply intrinsicCurrent_ext_chartSources n k U T R
  intro S
  apply LinearMap.ext
  intro w
  let w' : supportedCompactCore n k (chartOpen S (chartDomain S U)) :=
    ⟨w.val, fun q hq => (Set.ext_iff.mp (intrinsicChartOpen_chartDomain S U) q).mpr (w.property hq)⟩
  have he := LinearMap.congr_fun (h S) w'
  exact he

end TernaryPoly.PolynomialFormWeakSmooth
