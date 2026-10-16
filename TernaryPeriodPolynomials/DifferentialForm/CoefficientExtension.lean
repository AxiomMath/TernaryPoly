module

public import TernaryPeriodPolynomials.DifferentialForm.AdjointFirstOrder
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCoefficientExtension

@[expose] public section


/-! Genuine compact smooth extensions of every actual local adjoint coefficient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SymmetricSpaceCharts
open scoped ContDiff Topology

theorem exists_adjoint_coefficient_extensions (n k : ℕ) {K : Set Coordinates}
    (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates) :
    ∃ a b : Index n k → Index n (k+1) → Index n k → Index n (k+1) → Fin 5 → Coordinates → ℝ,
    ∃ T : Set Coordinates, IsCompact T ∧ T ⊆ positiveCoordinates ∧
      (∀ i t l j d, ContDiff ℝ ∞ (a i t l j d) ∧ ContDiff ℝ ∞ (b i t l j d) ∧
        tsupport (a i t l j d) ⊆ T ∧ tsupport (b i t l j d) ⊆ T) ∧
      ∀ x ∈ K, ∀ i t l j d,
        a i t l j d =ᶠ[𝓝 x] adjointFirstCoefficient n k i t l j d ∧
        b i t l j d =ᶠ[𝓝 x] adjointZeroCoefficient n k i t l j d := by
  let I := Index n k × Index n (k+1) × Index n k × Index n (k+1) × Fin 5
  let f : Bool × I → Coordinates → ℝ := fun z =>
    if z.1 then adjointFirstCoefficient n k z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2
    else adjointZeroCoefficient n k z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2
  have hf : ∀ z, ContDiffOn ℝ ∞ (f z) positiveCoordinates := by
    intro z
    dsimp only [f]
    split
    · exact contDiffOn_adjointFirstCoefficient n k _ _ _ _ _
    · exact contDiffOn_adjointZeroCoefficient n k _ _ _ _ _
  obtain ⟨g,T,hT,hTp,hg,he⟩ := CompactSmoothCoefficientExtension.exists_extensions
    hK isOpen_positiveCoordinates hKpos f hf
  refine ⟨(fun i t l j d => g (true,i,t,l,j,d)),
    (fun i t l j d => g (false,i,t,l,j,d)), T, hT, hTp, ?_, ?_⟩
  · intro i t l j d
    exact ⟨(hg _).1,(hg _).1,(hg _).2,(hg _).2⟩
  · intro x hx i t l j d
    exact ⟨he x hx (true,i,t,l,j,d), he x hx (false,i,t,l,j,d)⟩

end TernaryPoly.PolynomialFormCoordinates
