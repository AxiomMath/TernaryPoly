module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricActionDerivative
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricNormalization

@[expose] public section


/-! The actual differential of every GL3 action preserves the positive trace metric. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpacePositive SymmetricSpaceCharts
open scoped ContDiff Matrix.Norms.Elementwise

/-- Invariance uses the literal Fréchet derivative of the coordinate action. -/
theorem coordinatePair_fderiv_invariant (g : RealGL) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (v w : Coordinates) :
    coordinatePair (coordinateAction g x)
      (fderiv ℝ (coordinateAction g) x v) (fderiv ℝ (coordinateAction g) x w) =
      coordinatePair x v w := by
  unfold coordinatePair
  rw [reconstruct_coordinateAction g x hx, tangent_fderiv_coordinateAction g x hx v,
    tangent_fderiv_coordinateAction g x hx w, normalizationDerivative_apply,
    normalizationDerivative_apply]
  have htrace := ne_of_gt (conjugate_positive g (reconstruct x) hx).trace_pos
  obtain ⟨S, hS⟩ := (show (reconstruct x).PosDef from hx).isUnit
  rw [← hS] at htrace ⊢
  simpa [SymmetricSpacePositive.normalize, conjugate] using
    tangentPair_normalized_congruence g S (tangentMatrix v) (tangentMatrix w)
      (conjugate g (S : Mat)).trace⁻¹ (inv_ne_zero htrace)
      (-(conjugate g (S : Mat)).trace⁻¹ * (conjugate g (tangentMatrix v)).trace)
      (-(conjugate g (S : Mat)).trace⁻¹ * (conjugate g (tangentMatrix w)).trace)

end TernaryPoly.SymmetricSpaceTraceMetric
