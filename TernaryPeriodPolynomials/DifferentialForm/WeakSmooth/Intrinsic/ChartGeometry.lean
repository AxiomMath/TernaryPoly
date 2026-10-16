module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.FormCurrent
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.OpenCharts

@[expose] public section


/-! Actual coordinate domains inside the genuine quotient open cut out by that chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped ContDiff

/-- The actual coordinate test domain lies in the genuine covering preimage of its chart open. -/
theorem intrinsicChart_domain_lifted (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) :
    (Ω : Set Coordinates) ⊆ liftedDomain (chartOpen S Ω) := by
  intro x hx
  exact chartDomain_liftedDomain S ⟨hΩ hx, chartOpen_contains S (hΩ hx) hx⟩

/-- A genuine local smooth equivariant form is genuinely smooth on the actual coordinate domain. -/
theorem intrinsicChart_local_smooth (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : EquivariantForm (deckRepresentation n) (chartOpen S Ω) k) :
    ContDiffOn ℝ ∞ a.val.val Ω :=
  (Form.smooth a.val).mono (intrinsicChart_domain_lifted S Ω hΩ)

/-- Actual scalar coordinates of a genuine local smooth equivariant form are continuous on the
actual scalar-test domain. -/
theorem intrinsicChart_local_coefficient_continuous (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : EquivariantForm (deckRepresentation n) (chartOpen S Ω) k) (i : Index n k) :
    ContinuousOn (components n k a.val.val i) Ω :=
  (contDiffOn_components n k (intrinsicChart_local_smooth n k S Ω hΩ a) i).continuousOn

end TernaryPoly.PolynomialFormWeakSmooth
