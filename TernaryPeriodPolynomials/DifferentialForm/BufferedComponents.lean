module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.BufferDerivatives
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula

@[expose] public section


/-! Exact scalar-coordinate formulas for legitimate chart buffers. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff Topology

theorem components_smul_function (n k : ℕ) (χ : Coordinates → ℝ) (w : Coordinates → FormValue n k) :
    components n k (fun x => χ x • w x) = fun i x => χ x * components n k w i x := by
  funext i x
  change (coordinates n k (χ x • w x)) i = _
  rw [map_smul]
  rfl

theorem components_cutoffChartRaw_buffer (n k : ℕ) (S : Space) (χ θ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k)
    (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1) :
    components n k (cutoffChartRaw n k S χ w) =
      fun i x => χ x * components n k (cutoffChartRaw n k S θ w) i x :=
  (congrArg (components n k) (cutoffChartRaw_buffer n k S χ θ w hθ)).trans
    (components_smul_function n k χ _)

theorem components_mollifiedChartRaw_buffer (n k : ℕ) (S : Space) (χ η θ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k)
    (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1) (c : ℝ) :
    components n k (mollifiedChartRaw n k S χ η c w) =
      fun i x => η x * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => χ z * components n k (cutoffChartRaw n k S θ w) i z) x := by
  funext i x
  exact (components_mollifiedChartRaw n k S χ η c w i x).trans
    (congrArg (fun f : Coordinates → ℝ => η x * scalarConvolution volume
      (CompactScalarMollifier.kernel Coordinates volume c) f x)
      (congrFun (components_cutoffChartRaw_buffer n k S χ θ w hθ) i))

theorem components_cutoffChartRaw_differential_buffer (n k : ℕ) (S : Space) (χ θ : Coordinates → ℝ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (w : CompactSupportForm (deckRepresentation n) univ k) :
    components n (k+1) (cutoffChartRaw n (k+1) S χ (compactDifferential (deckRepresentation n) isOpen_univ k w).val) =
      fun i x => χ x * components n (k+1) (extDeriv (cutoffChartRaw n k S θ w.val)) i x :=
  (congrArg (components n (k+1)) (cutoffChartRaw_differential_buffer n k S χ θ hsχ hθ w)).trans
    (components_smul_function n (k+1) χ _)

theorem components_cutoffChartRaw_adjoint_buffer (n k : ℕ) (S : Space) (χ θ : Coordinates → ℝ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (w : CompactSupportForm (deckRepresentation n) univ (k+1)) :
    components n k (cutoffChartRaw n k S χ (compactAdjoint n k w).val) =
      fun i x => χ x * components n k (localAdjoint n k (cutoffChartRaw n (k+1) S θ w.val)) i x :=
  (congrArg (components n k) (cutoffChartRaw_adjoint_buffer n k S χ θ hsχ hθ w)).trans
    (components_smul_function n k χ _)

end TernaryPoly.PolynomialFormCoordinates
