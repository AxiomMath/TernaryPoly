module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.VolumeGeometry

@[expose] public section


/-! The genuine inverse tangent metric derivative in the actual coordinate connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian
open scoped Matrix.Norms.Elementwise

theorem hasDerivAt_inverseGram_operator (x : Coordinates) (hx : x ∈ positiveCoordinates) (u : Coordinates) :
    HasDerivAt (fun t : ℝ => inverseGram (x + t • u)) (fderiv ℝ inverseGram x u) 0 := by
  have hd := (((contDiffOn_inverseGram x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_coordinateLine x u)
    (by simp only [zero_smul, add_zero])
  convert! h using 1

theorem inverseGramDerivative (x : Coordinates) (hx : x ∈ positiveCoordinates) (u : Coordinates) :
    fderiv ℝ inverseGram x u =
      -(tangentConnectionMatrix x u * inverseGram x + inverseGram x * (tangentConnectionMatrix x u).transpose) := by
  have hp := hasDerivAt_finite_matrix_product (hasDerivAt_coordinateGram_connection x hx u)
    (hasDerivAt_inverseGram_operator x hx u)
  have he : (fun _ : ℝ => (1 : Matrix (Fin 5) (Fin 5) ℝ)) =ᶠ[nhds 0]
      (fun t : ℝ => coordinateGram (x + t • u) * inverseGram (x + t • u)) := by
    filter_upwards [eventually_coordinateLine_positive x hx u] with t ht
    exact (Matrix.mul_nonsing_inv _
      ((coordinateGram (x + t • u)).isUnit_iff_isUnit_det.mp (coordinateGram_posDef (x + t • u) ht).isUnit)).symm
  have hz := (hp.congr_of_eventuallyEq he).unique (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin 5) (Fin 5) ℝ))
  simp only [zero_smul, add_zero] at hz
  have hi := (coordinateGram x).isUnit_iff_isUnit_det.mp (coordinateGram_posDef x hx).isUnit
  have hL : inverseGram x * coordinateGram x = 1 := Matrix.nonsing_inv_mul _ hi
  have hR : coordinateGram x * inverseGram x = 1 := Matrix.mul_nonsing_inv _ hi
  have h := congrArg (fun M => inverseGram x * M) hz
  simp only [mul_add, add_mul, mul_zero] at h
  have hfirst : inverseGram x * ((tangentConnectionMatrix x u).transpose * coordinateGram x * inverseGram x) =
      inverseGram x * (tangentConnectionMatrix x u).transpose := by
    simp only [mul_assoc, hR, mul_one]
  have hsecond : inverseGram x * (coordinateGram x * tangentConnectionMatrix x u * inverseGram x) =
      tangentConnectionMatrix x u * inverseGram x := by
    simp only [← mul_assoc, hL, one_mul]
  rw [hfirst, hsecond, ← mul_assoc, hL, one_mul] at h
  rw [add_comm (inverseGram x * (tangentConnectionMatrix x u).transpose)] at h
  exact eq_neg_of_add_eq_zero_right h

theorem hasDerivAt_inverseGram_connection (x : Coordinates) (hx : x ∈ positiveCoordinates) (u : Coordinates) :
    HasDerivAt (fun t : ℝ => inverseGram (x + t • u))
      (-(tangentConnectionMatrix x u * inverseGram x + inverseGram x * (tangentConnectionMatrix x u).transpose)) 0 := by
  rw [← inverseGramDerivative x hx u]
  exact hasDerivAt_inverseGram_operator x hx u

end TernaryPoly.PolynomialFormConnection
