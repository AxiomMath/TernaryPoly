module

public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCutoff
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! Genuine compact smooth extensions of chart coefficients, equal on actual neighborhoods. -/
noncomputable section
namespace TernaryPoly.CompactSmoothCoefficientExtension
open Set Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- One genuine cutoff simultaneously extends every member of a smooth coefficient family. -/
theorem exists_extensions {I : Type*} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : I → E → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) :
    ∃ g : I → E → ℝ, ∃ T : Set E, IsCompact T ∧ T ⊆ U ∧
      (∀ i, ContDiff ℝ ∞ (g i) ∧ tsupport (g i) ⊆ T) ∧
      ∀ x ∈ K, ∀ i, g i =ᶠ[𝓝 x] f i := by
  obtain ⟨χ, hχ, hcχ, hsχ, hχone⟩ := CompactSmoothCutoff.exists_cutoff hK hU hKU
  let g (i : I) (x : E) := χ x * f i x
  have hs (i : I) : tsupport (g i) ⊆ tsupport χ := tsupport_mul_subset_left
  refine ⟨g, tsupport χ, hcχ, hsχ, ?_, ?_⟩
  · intro i
    exact ⟨CompactCoordinateIntegration.contDiff_of_tsupport_subset hU
      (hχ.contDiffOn.mul (hf i)) ((hs i).trans hsχ), hs i⟩
  · intro x hx i
    filter_upwards [hχone x hx] with y hy
    simp only [g, hy, Pi.one_apply, one_mul]

/-- A single local coefficient therefore admits an actual compact global smooth extension. -/
theorem exists_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨g, T, hT, hTU, hg, he⟩ := exists_extensions hK hU hKU (fun _ : Unit => f) (fun _ => hf)
  exact ⟨g (), (hg ()).1, hT.of_isClosed_subset (isClosed_tsupport _) (hg ()).2,
    (hg ()).2.trans hTU, fun x hx => he x hx ()⟩

end TernaryPoly.CompactSmoothCoefficientExtension
