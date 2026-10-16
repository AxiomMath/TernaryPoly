module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Forms

@[expose] public section



/-! The torsion-free tensor connection gives the genuine covariant exterior derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

/-- The actual tangent connection as a continuous bilinear map. -/
def tangentBilinearConnection (x : Coordinates) : Coordinates →L[ℝ] Coordinates →L[ℝ] Coordinates :=
  (show Coordinates →ₗ[ℝ] Coordinates →L[ℝ] Coordinates from
    { toFun := tangentEndomorphism x
      map_add' u v := by
        apply ContinuousLinearMap.ext
        intro w
        exact tangentConnection_add_left x u v w
      map_smul' c u := by
        apply ContinuousLinearMap.ext
        intro v
        exact tangentConnection_smul_left x u v c }).toContinuousLinearMap

@[simp] theorem tangentBilinearConnection_apply (x u v : Coordinates) :
    tangentBilinearConnection x u v = tangentConnection x u v := rfl

def tangentFormDerivative (n k : ℕ) (x : Coordinates) (a : FormValue n k) : Coordinates →L[ℝ] FormValue n k :=
  (a.fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ Coordinates)).comp (tangentBilinearConnection x)

@[simp] theorem tangentFormDerivative_apply (n k : ℕ) (x u : Coordinates) (a : FormValue n k) :
    tangentFormDerivative n k x a u = tangentFormAction n k x u a := rfl

/-- Actual torsion-freeness removes all tangent-slot terms after alternation, in every degree. -/
theorem alternatize_tangentFormDerivative (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n k) : alternatizeUncurryFin (tangentFormDerivative n k x a) = 0 := by
  apply alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
  intro u v
  exact tangentConnection_symmetric x hx u v

/-- The complete tensor covariant derivative, bundled in its genuine tangent direction. -/
def covariantFormLinearDerivative (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) :
    Coordinates →L[ℝ] FormValue n k :=
  fderiv ℝ w x - symmetricFormDerivative n k x (w x) - tangentFormDerivative n k x (w x)

theorem covariantFormLinearDerivative_apply (n k : ℕ) (w : Coordinates → FormValue n k)
    (x u : Coordinates) : covariantFormLinearDerivative n k w x u = covariantFormDerivative n k w x u := by
  apply ContinuousAlternatingMap.ext
  intro v
  change (fderiv ℝ w x u v - symmetricPart n x u (w x v)) - tangentFormAction n k x u (w x) v =
    (fderiv ℝ w x u v + connectionMatrix n x u (w x v)) - tangentFormAction n k x u (w x) v
  simp [connectionMatrix, sub_eq_add_neg]

/-- No omitted tangent connection survives in the genuine exterior covariant derivative. -/
theorem alternatize_covariantFormLinearDerivative (n k : ℕ) (w : Coordinates → FormValue n k)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    alternatizeUncurryFin (covariantFormLinearDerivative n k w x) = covariantExterior n k w x := by
  unfold covariantFormLinearDerivative
  change alternatizeUncurryFinCLM ℝ Coordinates (Coefficients n) (_ - _ - _) = _
  simp only [PolynomialFormCoordinates.clm_map_sub, alternatizeUncurryFinCLM_apply, alternatize_tangentFormDerivative n k x hx, sub_zero]
  rfl

end TernaryPoly.PolynomialFormConnection
