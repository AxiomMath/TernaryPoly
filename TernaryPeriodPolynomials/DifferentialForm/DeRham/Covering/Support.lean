module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.LocalExactness

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U : Set OrbitSpace} {n : ℕ}

/-- Closed support on the actual quotient: the closure of the projection of the nonzero
covering values. This uses the true covering projection, not compact support upstairs. -/
def quotientSupport (w : EquivariantForm ρ U n) : Set OrbitSpace :=
  closure (coordinateProjection '' Function.support (w.val : RawForm Coordinates F n))

@[simp] theorem quotientSupport_zero : quotientSupport (0 : EquivariantForm ρ U n) = ∅ := by
  simp [quotientSupport]

theorem quotientSupport_add (w z : EquivariantForm ρ U n) :
    quotientSupport (w + z) ⊆ quotientSupport w ∪ quotientSupport z := by
  rw [quotientSupport, quotientSupport, quotientSupport, ← closure_union, ← image_union]
  apply closure_mono
  apply image_mono
  exact Function.support_add (w.val : RawForm Coordinates F n) (z.val : RawForm Coordinates F n)

theorem quotientSupport_smul (c : ℝ) (w : EquivariantForm ρ U n) :
    quotientSupport (c • w) ⊆ quotientSupport w := by
  apply closure_mono
  apply image_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  change c • (w.val : RawForm Coordinates F n) x = 0
  rw [hx, smul_zero]

/-- Exterior differentiation cannot enlarge closed projected support. The proof uses the
actual projection's continuity and the locality of the literal exterior derivative. -/
theorem quotientSupport_differential (hU : IsOpen U) (w : EquivariantForm ρ U n) :
    quotientSupport (differential ρ hU n w) ⊆ quotientSupport w := by
  apply closure_minimal _ isClosed_closure
  rintro q ⟨x, hx, rfl⟩
  by_contra hq
  have hxne : ((differential ρ hU n w).val : RawForm Coordinates F (n + 1)) x ≠ 0 := hx
  have hxd : x ∈ liftedDomain U := by
    by_contra h
    exact hxne (Form.outside (differential ρ hU n w).val h)
  have hp : ContinuousAt coordinateProjection x := coordinateProjection_continuousOn.continuousAt
    (isOpen_positiveCoordinates.mem_nhds hxd.1)
  have hnear : ∀ᶠ y in 𝓝 x, coordinateProjection y ∉ quotientSupport w :=
    hp.eventually (isClosed_closure.isOpen_compl.mem_nhds hq)
  have he : (w.val : RawForm Coordinates F n) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hnear] with y hy
    by_contra hn
    exact hy (subset_closure ⟨y, hn, rfl⟩)
  apply hxne
  change (d (liftedDomain_isOpen hU) n w.val : RawForm Coordinates F (n + 1)) x = 0
  rw [d_apply (liftedDomain_isOpen hU) _ hxd, he.extDeriv_eq]
  simp only [extDeriv, fderiv_zero]
  exact map_zero (alternatizeUncurryFinCLM ℝ Coordinates F (n := n))

end TernaryPoly.SmoothCoveringDeRham
