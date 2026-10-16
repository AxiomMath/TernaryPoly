module

public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.LocalClasses
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanBallLocal
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A positive-radius closed ball contained in another has its center in the larger open ball. -/
theorem center_mem_ball_of_closedBall_subset (x y : E) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (h : Metric.closedBall y s ⊆ Metric.closedBall x r) : y ∈ Metric.ball x r := by
  have h' := interior_mono h
  rw [interior_closedBall y (ne_of_gt hs), interior_closedBall x (ne_of_gt hr)] at h'
  exact h' (Metric.mem_ball_self hs)

/-- The actual relative pair map restricts a class supported on a larger ball to a smaller ball. -/
def ballRestriction (x : E) (r : ℝ) (y : E) (s : ℝ)
    (h : Metric.closedBall y s ⊆ Metric.closedBall x r) :
    ballRelativeChains x r ⟶ ballRelativeChains y s :=
  relativeMap (ContinuousMap.id E) (exterior x r) (exterior y s)
    (fun _ hz hy => hz (h hy))

/-- The exact relative chain projection square for restriction between nested closed balls. -/
theorem ballRestriction_projection (x : E) (r : ℝ) (y : E) (s : ℝ)
    (h : Metric.closedBall y s ⊆ Metric.closedBall x r) :
    cokernel.π (inclusion (exterior x r)) ≫ ballRestriction x r y s h =
      cokernel.π (inclusion (exterior y s)) := by
  simp [ballRestriction, relativeMap, cokernel.map, RationalSingularAugmentation.chainMap]

/-- Restriction followed by the actual point map equals the direct point map from the larger ball. -/
theorem ballRestriction_pointMap (x : E) (r : ℝ) (y : E) (s : ℝ)
    (h : Metric.closedBall y s ⊆ Metric.closedBall x r) (z : E) (hz : z ∈ Metric.closedBall y s) :
    ballRestriction x r y s h ≫ ballPointMap y s z hz = ballPointMap x r z (h hz) := by
  rw [ballRestriction, ballPointMap, ballPointMap]
  erw [RationalRelativeExcision.relativeMap_comp]
  rfl

/-- Actual restriction between nested positive-radius closed balls preserves the canonical classes. -/
theorem ballRestriction_generator (n : ℕ) (x y : EuclideanSpace ℝ (Fin (n+2)))
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (h : Metric.closedBall y s ⊆ Metric.closedBall x r) :
    homologyMap (ballRestriction x r y s h) (n+2) (ballGenerator n x r hr) =
      ballGenerator n y s hs := by
  apply ballGenerator_unique n y s hs
  change (homologyMap (ballRestriction x r y s h) (n+2) ≫
    homologyMap (ballPointMap y s y (Metric.mem_closedBall_self hs.le)) (n+2)) _ = _
  rw [← homologyMap_comp, ballRestriction_pointMap]
  exact ballGenerator_at_point n x r hr y (center_mem_ball_of_closedBall_subset x y r s hr hs h)

end TernaryPoly.EuclideanBallLocal
