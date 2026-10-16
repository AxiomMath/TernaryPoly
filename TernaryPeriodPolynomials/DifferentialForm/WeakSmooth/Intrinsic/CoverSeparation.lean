module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.FiniteCharts

@[expose] public section

/-! Actual compact-test locality for arbitrary genuine quotient open covers. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpacePositive
  SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham SmoothDeRhamGluing
open scoped ContDiff Manifold

/-- An actual compact quotient set admits a finite genuine smooth partition subordinate to any
actual open cover of that compact set. -/
theorem intrinsicCompact_finite_open_partition {ι : Type} (K : Set OrbitSpace) (hK : IsCompact K)
    (V : ι → Set OrbitSpace) (hV : ∀ i, IsOpen (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ s : Finset ι, ∃ φ : SmoothPartitionOfUnity s 𝓘(ℝ, Coordinates) OrbitSpace K,
      φ.IsSubordinate (fun i => V i.val) := by
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV hcover
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    hK.isClosed (fun i : s => V i.val) (fun i => hV i.val) (by
      intro q hq
      obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.mp (hs hq)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hqi⟩)
  exact ⟨s, φ, hφ⟩

/-- Every genuine compact form is a finite sum of genuine compact forms supported in a chosen
open cover of its actual support. -/
theorem compactForm_finite_open_decomposition {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (ρ : Representation ℝ DeckGroup F)
    (k : ℕ) (w : CompactSupportForm ρ univ k) {ι : Type} (V : ι → Set OrbitSpace)
    (hV : ∀ i, IsOpen (V i)) (hcover : quotientSupport w.val ⊆ ⋃ i, V i) :
    ∃ s : Finset ι, ∃ a : s → CompactSupportForm ρ univ k,
      (∀ i, quotientSupport (a i).val ⊆ V i.val) ∧ ∑ i, a i = w := by
  classical
  obtain ⟨s, φ, hφ⟩ := intrinsicCompact_finite_open_partition
    (quotientSupport w.val) w.property.1 V hV hcover
  let a : s → CompactSupportForm ρ univ k := fun i =>
    compactScalarMultiply (φ i) (φ i).contMDiff.contMDiffOn k w
  refine ⟨s, a, ?_, ?_⟩
  · intro i
    exact (quotientSupport_scalarMultiply_subset_tsupport (φ i) (φ i).contMDiff.contMDiffOn w.val).trans (hφ i)
  · apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x hx
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ i : s, (φ i) (coordinateProjection x) • w.val.val.val x) = w.val.val.val x
    by_cases hw : w.val.val.val x = 0
    · simp only [hw, smul_zero, Finset.sum_const_zero]
    · have hsum := φ.sum_eq_one (subset_closure ⟨x, hw, rfl⟩)
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [← Finset.sum_smul, hsum, one_smul]

/-- Actual intrinsic tests decompose into a finite sum of actual tests on any open cover. -/
theorem supportedCompactCore_finite_open_decomposition (n k : ℕ) (U : Set OrbitSpace)
    (w : supportedCompactCore n k U) {ι : Type} (V : ι → Set OrbitSpace)
    (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U) (hcover : U ⊆ ⋃ i, V i) :
    ∃ s : Finset ι, ∃ a : (i : s) → supportedCompactCore n k (V i.val),
      (∑ i : s, supportedCompactInclusion n k (hVU i.val) (a i)) = w := by
  classical
  exact (compactForm_finite_open_decomposition (deckRepresentation n) k w.val V hV
    (w.property.trans hcover)).elim (fun s hs => hs.elim (fun a ha => by
      let b (i : s) : supportedCompactCore n k (V i.val) := ⟨a i, ha.1 i⟩
      refine ⟨s, b, ?_⟩
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      change (∑ i : s, a i) = w.val
      exact ha.2))

/-- Genuine intrinsic currents are separated by restrictions to every genuine open cover. -/
theorem intrinsicCurrent_ext_cover (n k : ℕ) (U : Set OrbitSpace)
    {ι : Type} (V : ι → Set OrbitSpace) (hV : ∀ i, IsOpen (V i))
    (hVU : ∀ i, V i ⊆ U) (hcover : U ⊆ ⋃ i, V i) (T R : IntrinsicCurrent n k U)
    (h : ∀ i, intrinsicCurrentRestriction n k (hVU i) T =
      intrinsicCurrentRestriction n k (hVU i) R) : T = R := by
  apply LinearMap.ext
  intro w
  exact (supportedCompactCore_finite_open_decomposition n k U w V hV hVU hcover).elim
    (fun s hs => hs.elim (fun a ha => by
      have he : T (∑ i : s, supportedCompactInclusion n k (hVU i.val) (a i)) =
          R (∑ i : s, supportedCompactInclusion n k (hVU i.val) (a i)) := by
        simp only [map_sum]
        exact Finset.sum_congr rfl (fun i _ => LinearMap.congr_fun (h i.val) (a i))
      exact (congrArg T ha).symm.trans (he.trans (congrArg R ha))))

end TernaryPoly.PolynomialFormWeakSmooth
