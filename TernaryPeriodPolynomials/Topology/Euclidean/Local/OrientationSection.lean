module

public import TernaryPeriodPolynomials.Topology.Rational.Local.Orientation
public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.Local

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanLocalHomology
open CategoryTheory HomologicalComplex TopologicalSpace RationalLocalOrientation

/-- The chosen Euclidean local generators are represented simultaneously on neighborhoods
by genuine closed-ball relative classes. -/
theorem localGenerator_locallyRepresented (n : ℕ) :
    LocallyRepresented (n+2) (localGenerator n) := by
  intro x
  refine ⟨⟨Metric.ball x 1,Metric.isOpen_ball⟩,Metric.closedBall x 1,
    Metric.mem_ball_self (by norm_num),Metric.ball_subset_closedBall,
    EuclideanBallLocal.ballGenerator n x 1 (by norm_num),?_⟩
  intro y hy hK
  exact EuclideanBallLocal.ballGenerator_at_point n x 1 (by norm_num) y hy

/-- The actual Euclidean homological orientation includes nonzero point classes and genuine
local relative-class representatives. -/
def euclideanOrientation (n : ℕ) : Orientation (n+2) (EuclideanSpace ℝ (Fin (n+2))) where
  generator := localGenerator n
  nonzero := localGenerator_ne_zero n
  locallyRepresented := localGenerator_locallyRepresented n

end TernaryPoly.EuclideanLocalHomology
