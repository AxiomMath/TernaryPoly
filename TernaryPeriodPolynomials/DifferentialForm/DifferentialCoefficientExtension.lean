module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Differential
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCoefficientExtension

@[expose] public section


/-! Actual compact smooth extensions of the true exterior-differential coefficients. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SymmetricSpaceCharts
open scoped ContDiff Topology

theorem exists_differential_coefficient_extensions (n k : ℕ) {K : Set Coordinates}
    (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates) :
    ∃ a : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ,
    ∃ T : Set Coordinates, IsCompact T ∧ T ⊆ positiveCoordinates ∧
      (∀ j i d, ContDiff ℝ ∞ (a j i d) ∧ tsupport (a j i d) ⊆ T) ∧
      ∀ x ∈ K, ∀ j i d, a j i d =ᶠ[𝓝 x] differentialCoefficients n k j i d := by
  let f : (Index n (k+1) × Index n k × Fin 5) → Coordinates → ℝ :=
    fun z => differentialCoefficients n k z.1 z.2.1 z.2.2
  have hf : ∀ z, ContDiffOn ℝ ∞ (f z) positiveCoordinates := fun _ => contDiffOn_const
  obtain ⟨g,T,hT,hTp,hg,he⟩ := CompactSmoothCoefficientExtension.exists_extensions
    hK isOpen_positiveCoordinates hKpos f hf
  exact ⟨(fun j i d => g (j,i,d)),T,hT,hTp,(fun j i d => hg (j,i,d)),
    fun x hx j i d => he x hx (j,i,d)⟩

end TernaryPoly.PolynomialFormCoordinates
