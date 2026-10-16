module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CoordinateDifferential

@[expose] public section


/-! Genuine form-valued algebraic compact-test currents and their exact finite coordinates. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts
open scoped Distributions

/-- An actual form-valued current is an algebraic linear map on actual scalar compact tests. -/
abbrev FormWeak (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates) :=
  𝓓(Ω, ℝ) →ₗ[ℝ] FormValue n k

/-- Actual finite form coordinates of a form-valued current. -/
def formWeakCoordinates (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n k Ω) (i : Index n k) : ScalarWeak Ω :=
  ((LinearMap.proj i).comp (coordinates n k).toLinearMap).comp W

/-- Reassemble an actual form-valued current from its scalar compact-test coordinate currents. -/
def formWeakOfCoordinates (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (w : Index n k → ScalarWeak Ω) : FormWeak n k Ω :=
  (coordinates n k).symm.toLinearMap.comp (LinearMap.pi w)

@[simp] theorem formWeakCoordinates_apply (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n k Ω) (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    formWeakCoordinates n k Ω W i φ = coordinates n k (W φ) i := rfl

@[simp] theorem formWeakOfCoordinates_apply (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (w : Index n k → ScalarWeak Ω) (φ : 𝓓(Ω, ℝ)) :
    formWeakOfCoordinates n k Ω w φ = (coordinates n k).symm (fun i => w i φ) := rfl

/-- Scalar coordinate extraction after reconstruction is exactly the original current family. -/
theorem formWeakCoordinates_ofCoordinates (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (w : Index n k → ScalarWeak Ω) :
    formWeakCoordinates n k Ω (formWeakOfCoordinates n k Ω w) = w := by
  funext i
  apply LinearMap.ext
  intro φ
  change (coordinates n k ((coordinates n k).symm (fun i => w i φ))) i = w i φ
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The actual finite coordinates faithfully reconstruct every form-valued current. -/
theorem formWeakOfCoordinates_coordinates (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n k Ω) :
    formWeakOfCoordinates n k Ω (formWeakCoordinates n k Ω W) = W := by
  apply LinearMap.ext
  intro φ
  change (coordinates n k).symm (coordinates n k (W φ)) = W φ
  exact ContinuousLinearEquiv.symm_apply_apply _ _

/-- The genuine form-valued algebraic current induced by a Hilbert form in a genuine chart. -/
def chartHilbertFormCurrent (n k : ℕ) (S : SymmetricSpacePositive.Space)
    (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (SymmetricSpaceCovering.quotientChart S).target)
    (u : PolynomialFormHilbert.Hilbert n k) : FormWeak n k Ω :=
  formWeakOfCoordinates n k Ω (fun i => coordinateHilbertCurrent n k S Ω hΩ i u)

end TernaryPoly.PolynomialFormWeakSmooth
