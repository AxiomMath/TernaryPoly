module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingScalar

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U : Set OrbitSpace} {n : ℕ}

/-- Off the closed projected support, an actual covering representative vanishes locally. -/
theorem raw_eventually_zero (w : EquivariantForm ρ U n) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) (hq : coordinateProjection x ∉ quotientSupport w) :
    (w.val : RawForm Coordinates F n) =ᶠ[𝓝 x] 0 := by
  have hp := coordinateProjection_continuousOn.continuousAt (isOpen_positiveCoordinates.mem_nhds hx)
  have hnear : ∀ᶠ y in 𝓝 x, coordinateProjection y ∉ quotientSupport w :=
    hp.eventually (isClosed_closure.isOpen_compl.mem_nhds hq)
  filter_upwards [hnear] with y hy
  by_contra hn
  exact hy (subset_closure ⟨y, hn, rfl⟩)

/-- A covering form whose projected closed support lies in its domain is smooth across the
boundary of that domain, throughout the actual positive-coordinate covering. -/
theorem raw_smooth_of_support_subset (hU : IsOpen U) (w : EquivariantForm ρ U n)
    (hw : quotientSupport w ⊆ U) :
    ContDiffOn ℝ ∞ (w.val : RawForm Coordinates F n) positiveCoordinates := by
  intro x hx
  by_cases hq : coordinateProjection x ∈ U
  · exact ((Form.smooth w.val x ⟨hx, hq⟩).contDiffAt
      ((liftedDomain_isOpen hU).mem_nhds ⟨hx, hq⟩)).contDiffWithinAt
  · have he := raw_eventually_zero w hx (fun h => hq (hw h))
    exact ((contDiffAt_const (c := (0 : Coordinates [⋀^Fin n]→L[ℝ] F))).congr_of_eventuallyEq he).contDiffWithinAt

theorem quotientSupport_scalarMultiply (φ : OrbitSpace → ℝ)
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U) (w : EquivariantForm ρ U n) :
    quotientSupport (scalarMultiply ρ φ hφ n w) ⊆ quotientSupport w := by
  apply closure_mono
  apply image_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  rw [scalarMultiply_apply, hx, smul_zero]

/-- Multiplication by a smooth quotient function preserves genuine quotient compact support. -/
def compactScalarMultiply (φ : OrbitSpace → ℝ)
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U) (n : ℕ) :
    CompactSupportForm ρ U n →ₗ[ℝ] CompactSupportForm ρ U n where
  toFun w := ⟨scalarMultiply ρ φ hφ n w.val,
    w.property.1.of_isClosed_subset isClosed_closure (quotientSupport_scalarMultiply φ hφ w.val),
    (quotientSupport_scalarMultiply φ hφ w.val).trans w.property.2⟩
  map_add' w z := Subtype.ext (map_add _ w.val z.val)
  map_smul' c w := Subtype.ext (map_smul _ c w.val)

end TernaryPoly.SmoothDeRhamGluing
