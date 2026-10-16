module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.VolumeDerivative
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Forms
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-! The actual coordinate density differentiates by the trace of the constructed tangent connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric SymmetricSpaceRiemannian
open scoped Matrix.Norms.Elementwise

/-- Matrix of the actual tangent connection in the coordinate basis. -/
def tangentConnectionMatrix (x u : Coordinates) : Matrix (Fin 5) (Fin 5) ℝ :=
  LinearMap.toMatrix' (tangentEndomorphism x u).toLinearMap

theorem hasDerivAt_coordinateGram_connection (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinateGram (x + t • u))
      ((tangentConnectionMatrix x u).transpose * coordinateGram x +
        coordinateGram x * tangentConnectionMatrix x u) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := hasDerivAt_tangentMetric_connection_constants x hx u (Pi.single i 1) (Pi.single j 1)
  have hL := congrFun (congrFun (LinearMap.BilinForm.toMatrix'_compLeft (coordinateBilin x)
    (tangentEndomorphism x u).toLinearMap) i) j
  have hR := congrFun (congrFun (LinearMap.BilinForm.toMatrix'_compRight (coordinateBilin x)
    (tangentEndomorphism x u).toLinearMap) i) j
  change coordinatePair x (tangentConnection x u (Pi.single i 1)) (Pi.single j 1) =
    ((tangentConnectionMatrix x u).transpose * coordinateGram x) i j at hL
  change coordinatePair x (Pi.single i 1) (tangentConnection x u (Pi.single j 1)) =
    (coordinateGram x * tangentConnectionMatrix x u) i j at hR
  rw [hL, hR] at h
  exact h

theorem hasDerivAt_coordinateGram_det_connection (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) :
    HasDerivAt (fun t : ℝ => (coordinateGram (x + t • u)).det)
      (2 * (coordinateGram x).det * (tangentConnectionMatrix x u).trace) 0 :=
  hasDerivAt_det_of_gram_variation 5 _ _ _ (hasDerivAt_coordinateGram_connection x hx u)
    (by simp)

/-- The genuine Riemannian volume density has logarithmic derivative equal to the tangent-connection trace. -/
theorem hasDerivAt_coordinateDensity_connection (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinateDensity (x + t • u))
      (coordinateDensity x * (tangentConnectionMatrix x u).trace) 0 := by
  have hp := (coordinateGram_posDef x hx).det_pos
  have h := (hasDerivAt_coordinateGram_det_connection x hx u).sqrt
    (show (coordinateGram (x + (0 : ℝ) • u)).det ≠ 0 by simpa using ne_of_gt hp)
  change HasDerivAt (fun t : ℝ => coordinateDensity (x + t • u))
    ((2 * (coordinateGram x).det * (tangentConnectionMatrix x u).trace) /
      (2 * Real.sqrt (coordinateGram (x + (0 : ℝ) • u)).det)) 0 at h
  convert! h using 1
  simp only [coordinateDensity, zero_smul, add_zero]
  have hs := Real.sq_sqrt hp.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp
  rw [hs]
  ring

end TernaryPoly.PolynomialFormConnection
