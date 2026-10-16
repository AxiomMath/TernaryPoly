module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.Rules

@[expose] public section


/-! The actual endomorphism covariant derivative acts on genuine polynomial-valued forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy
open SymmetricSpaceCharts SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

/-- Literal commutator correction on a varying coefficient endomorphism. -/
def coefficientOperatorDerivative (n : ℕ) (L : Coordinates → Coefficients n →L[ℝ] Coefficients n)
    (x u : Coordinates) : Coefficients n →L[ℝ] Coefficients n :=
  fderiv ℝ L x u + (connectionMatrix n x u).comp (L x) - (L x).comp (connectionMatrix n x u)

theorem covariantFormDerivative_coefficientFormMap (n k : ℕ)
    (L : Coordinates → Coefficients n →L[ℝ] Coefficients n) (w : Coordinates → FormValue n k)
    (x u : Coordinates) (hL : DifferentiableAt ℝ L x) (hw : DifferentiableAt ℝ w x) :
    covariantFormDerivative n k (fun y => coefficientFormMap (L y) k (w y)) x u =
      coefficientFormMap (L x) k (covariantFormDerivative n k w x u) +
        coefficientFormMap (coefficientOperatorDerivative n L x u) k (w x) := by
  simp only [covariantFormDerivative, fderiv_coefficientFormMap_apply n k L w x u hL hw,
    tangentFormAction_coefficientFormMap]
  apply ContinuousAlternatingMap.ext
  intro v
  change (L x) (fderiv ℝ w x u v) + (fderiv ℝ L x u) (w x v) +
      connectionMatrix n x u ((L x) (w x v)) - (L x) (tangentFormAction n k x u (w x) v) =
    (L x) (fderiv ℝ w x u v + connectionMatrix n x u (w x v) - tangentFormAction n k x u (w x) v) +
      ((fderiv ℝ L x u) (w x v) + connectionMatrix n x u ((L x) (w x v)) -
        (L x) (connectionMatrix n x u (w x v)))
  rw [map_sub, map_add]
  abel

theorem fderiv_coefficient_operator_apply (n : ℕ) (L : Coordinates → Coefficients n →L[ℝ] Coefficients n)
    (x u : Coordinates) (hL : DifferentiableAt ℝ L x) (p : Coefficients n) :
    fderiv ℝ (fun y => L y p) x u = fderiv ℝ L x u p := by
  have h := fderiv_clm_apply (𝕜 := ℝ) (c := L) (u := fun _ : Coordinates => p) (x := x)
    (by convert! hL using 1) (differentiableAt_const p)
  have he := congrArg (fun A => A u) h
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] using he

/-- The geometric parallelism of Ψ is the actual coefficient-operator derivative rule. -/
theorem coefficientOperatorDerivative_symmetricPart (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) :
    coefficientOperatorDerivative n (fun y => symmetricPart n y v) x u =
      symmetricPart n x (tangentConnection x u v) := by
  have hL := (((contDiffOn_symmetricPart n v x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  apply ContinuousLinearMap.ext
  intro p
  have h := symmetricPart_parallel n x hx u v p
  rw [symmetricCovariantDerivative, fderiv_coefficient_operator_apply n _ x u hL p] at h
  exact sub_eq_zero.mp h

end TernaryPoly.PolynomialFormConnection
