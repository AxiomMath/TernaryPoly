module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.RealMetric

@[expose] public section

/-! Naturality of genuine exterior multiplication by the symmetric connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem symmetricExterior_real (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (a c : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k c) :
    (symmetricExterior n k (coordinateAction g x) a).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) (k + 1) (symmetricExterior n k x c) := by
  have hval (z : Fin k → Coordinates) :
      a (fun r => fderiv ℝ (coordinateAction g) x (z r)) = realCoefficientMap n g (c z) :=
    congrArg (fun F : FormValue n k => F z) ha
  apply ContinuousAlternatingMap.ext
  intro v
  change symmetricExterior n k (coordinateAction g x) a (fun r => fderiv ℝ (coordinateAction g) x (v r)) =
    realCoefficientMap n g (symmetricExterior n k x c v)
  rw [symmetricExterior_apply, symmetricExterior_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  change symmetricPart n (coordinateAction g x) (fderiv ℝ (coordinateAction g) x (v i))
    (a (fun r => fderiv ℝ (coordinateAction g) x (Fin.removeNth i v r))) = _
  rw [hval, symmetricPart_real n g hg x hx]

theorem linearMap_matrixAction (L : Coordinates →L[ℝ] Coordinates) :
    matrixAction (LinearMap.toMatrix' L.toLinearMap).transpose
      (fun i : Fin 5 => (Pi.single i 1 : Coordinates)) = fun i => L (Pi.single i 1) := by
  funext i
  ext j
  simp [matrixAction, LinearMap.toMatrix'_apply, Pi.single_apply]

/-- Frame change for the actual vector-valued metric contraction. -/
theorem symmetricContraction_frame (n k : ℕ) (y : Coordinates) (a : FormValue n (k + 1))
    (H : Matrix (Fin 5) (Fin 5) ℝ) (L : Coordinates →L[ℝ] Coordinates)
    (h : LinearMap.toMatrix' L.toLinearMap * H * (LinearMap.toMatrix' L.toLinearMap).transpose = inverseGram y) :
    symmetricContraction n k y a = ∑ i : Fin 5, ∑ j : Fin 5, H i j •
      coefficientFormMap (symmetricPart n y (L (Pi.single i 1))) k (a.curryLeft (L (Pi.single j 1))) := by
  have hc := bilinearContraction_action (contractionBilinear n k y a) H
    (LinearMap.toMatrix' L.toLinearMap).transpose
    (fun i : Fin 5 => (Pi.single i 1 : Coordinates)) (fun i : Fin 5 => (Pi.single i 1 : Coordinates))
  rw [linearMap_matrixAction, Matrix.transpose_transpose, h] at hc
  rw [symmetricContraction, ← hc]
  rfl

end TernaryPoly.PolynomialFormGeometricEnergy
