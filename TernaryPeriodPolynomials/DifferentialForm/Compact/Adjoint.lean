module

public import TernaryPeriodPolynomials.DifferentialForm.EquivariantAdjoint
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Linear
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport

@[expose] public section


/-! The genuine linear adjoint preserves the actual compact support on the arithmetic quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham SmoothLocalDeRham Set Filter
open scoped ContDiff Topology

/-- The descended adjoint is linear on the genuine smooth equivariant section space. -/
def equivariantAdjointLinear (n k : ℕ) : EquivariantForm (deckRepresentation n) univ (k + 1) →ₗ[ℝ]
    EquivariantForm (deckRepresentation n) univ k where
  toFun := equivariantAdjoint n k
  map_add' w z := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    have hxp : x ∈ positiveCoordinates := by simpa only [liftedDomain_univ] using hx
    change (equivariantAdjoint n k (w + z)).val.val x =
      (equivariantAdjoint n k w).val.val x + (equivariantAdjoint n k z).val.val x
    rw [equivariantAdjoint_apply n k (w + z) hxp, equivariantAdjoint_apply n k w hxp,
      equivariantAdjoint_apply n k z hxp]
    exact localAdjoint_add n k
      (by simpa only [liftedDomain_univ] using Form.smooth w.val)
      (by simpa only [liftedDomain_univ] using Form.smooth z.val) hxp
  map_smul' c w := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    have hxp : x ∈ positiveCoordinates := by simpa only [liftedDomain_univ] using hx
    change (equivariantAdjoint n k (c • w)).val.val x = c • (equivariantAdjoint n k w).val.val x
    rw [equivariantAdjoint_apply n k (c • w) hxp, equivariantAdjoint_apply n k w hxp]
    exact localAdjoint_smul n k c (by simpa only [liftedDomain_univ] using Form.smooth w.val) hxp

/-- The true closed projected support is not enlarged by the descended adjoint. -/
theorem quotientSupport_equivariantAdjoint (n k : ℕ)
    (w : EquivariantForm (deckRepresentation n) univ (k + 1)) :
    quotientSupport (equivariantAdjoint n k w) ⊆ quotientSupport w := by
  apply closure_minimal _ isClosed_closure
  rintro q ⟨x, hx, rfl⟩
  by_contra hq
  have hxne : (equivariantAdjoint n k w).val.val x ≠ 0 := hx
  have hxd : x ∈ liftedDomain univ := by
    by_contra hn
    exact hxne (Form.outside (equivariantAdjoint n k w).val hn)
  have hxp : x ∈ positiveCoordinates := by simpa only [liftedDomain_univ] using hxd
  have hp : ContinuousAt coordinateProjection x := coordinateProjection_continuousOn.continuousAt
    (isOpen_positiveCoordinates.mem_nhds hxp)
  have hnear : ∀ᶠ y in 𝓝 x, coordinateProjection y ∉ quotientSupport w :=
    hp.eventually (isClosed_closure.isOpen_compl.mem_nhds hq)
  have he : w.val.val =ᶠ[𝓝 x] 0 := by
    filter_upwards [hnear] with y hy
    by_contra hn
    exact hy (subset_closure ⟨y, hn, rfl⟩)
  apply hxne
  rw [equivariantAdjoint_apply n k w hxp, localAdjoint_congr n k he, localAdjoint_zero]
  rfl

/-- The actual compact smooth adjoint used to define the Hilbert-space adjoint core. -/
def compactAdjoint (n k : ℕ) : CompactSupportForm (deckRepresentation n) univ (k + 1) →ₗ[ℝ]
    CompactSupportForm (deckRepresentation n) univ k where
  toFun w := ⟨equivariantAdjoint n k w.val,
    w.property.1.of_isClosed_subset isClosed_closure (quotientSupport_equivariantAdjoint n k w.val),
    subset_univ _⟩
  map_add' w z := Subtype.ext ((equivariantAdjointLinear n k).map_add w.val z.val)
  map_smul' c w := Subtype.ext ((equivariantAdjointLinear n k).map_smul c w.val)

@[simp] theorem compactAdjoint_apply (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ (k + 1)) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    (compactAdjoint n k w).val.val.val x = localAdjoint n k w.val.val.val x :=
  equivariantAdjoint_apply n k w.val hx

end TernaryPoly.PolynomialFormCoordinates
