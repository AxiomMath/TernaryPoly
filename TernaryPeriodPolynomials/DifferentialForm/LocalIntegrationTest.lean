module

public import TernaryPeriodPolynomials.DifferentialForm.LocalIntegrationByParts
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Locality
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCutoff

@[expose] public section


/-! Local integration by parts against arbitrary smooth forms, using genuine compact test cutoffs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open Set MeasureTheory Filter
open scoped ContDiff Topology

/-- No support assumption on the second form is needed for the actual local adjoint identity. -/
theorem integral_extDeriv_localAdjoint_test (n k : ℕ)
    (f : Coordinates → FormValue n k) (g : Coordinates → FormValue n (k + 1))
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (hg : ContDiffOn ℝ ∞ g positiveCoordinates)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ positiveCoordinates) :
    ∫ x, coordinateDensity x * formPairing n (k + 1) x (extDeriv f x) (g x) =
      ∫ x, coordinateDensity x * formPairing n k x (f x) (localAdjoint n k g x) := by
  obtain ⟨φ, hφ, _, hφs, hφ1⟩ := CompactSmoothCutoff.exists_cutoff hfc isOpen_positiveCoordinates hfs
  let z : Coordinates → FormValue n (k + 1) := fun x => φ x • g x
  let : IsBoundedSMul ℝ (FormValue n (k + 1)) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n (k + 1)) _ _ inferInstance
  have hz : ContDiffOn ℝ ∞ z positiveCoordinates := ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates)
    (F := FormValue n (k + 1)) hφ.contDiffOn hg
  have hzφ : tsupport z ⊆ tsupport φ := tsupport_smul_subset_left φ g
  have hzs : tsupport z ⊆ positiveCoordinates := hzφ.trans hφs
  have hnear (x : Coordinates) (hx : x ∈ tsupport f) : z =ᶠ[𝓝 x] g := by
    filter_upwards [hφ1 x hx] with y hy
    simp only [z, Pi.one_apply] at hy ⊢
    rw [hy]
    exact one_smul ℝ (g y)
  calc
    _ = ∫ x, coordinateDensity x * formPairing n (k + 1) x (extDeriv f x) (z x) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      by_cases hx : x ∈ tsupport f
      · rw [(hnear x hx).eq_of_nhds]
      · rw [extDeriv_eq_zero_of_notMem_tsupport n k f hx, formPairing_zero_left, formPairing_zero_left]
    _ = ∫ x, coordinateDensity x * formPairing n k x (f x) (localAdjoint n k z x) :=
      integral_extDeriv_localAdjoint n k f z hf hz hfc hfs hzs
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      by_cases hx : x ∈ tsupport f
      · rw [localAdjoint_congr n k (hnear x hx)]
      · rw [image_eq_zero_of_notMem_tsupport hx, formPairing_zero_left, formPairing_zero_left]

end TernaryPoly.PolynomialFormCoordinates
