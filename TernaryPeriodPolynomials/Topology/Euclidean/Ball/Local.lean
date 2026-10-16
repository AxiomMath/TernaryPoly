module

public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.LocalNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanBallLocal
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular EuclideanLocalHomology

/-- The literal closed-ball relative complex maps quasi-isomorphically to the center's local complex,
and has no homology outside the Euclidean dimension. -/
theorem closedBallRelativeHomology (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2)))
    (r : ℝ) (hr : 0 < r) :
    QuasiIso (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) ∧
      ∀ k, k ≠ n+2 → IsZero ((relativeChains (Metric.closedBall x r)ᶜ).homology k) :=
  ⟨ballPointMap_center_quasiIso x r hr, fun k hk => ballHomology_isZero n k x r hr hk⟩

/-- A unique actual rational closed-ball fundamental class gives the fixed Euclidean local generator
at every interior point, under the literal identity map of pairs. -/
theorem closedBallRelativeFundamentalClass (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2)))
    (r : ℝ) (hr : 0 < r) :
    ∃! c : (relativeChains (Metric.closedBall x r)ᶜ).homology (n+2),
      ∀ (y : EuclideanSpace ℝ (Fin (n+2))) (hy : y ∈ Metric.ball x r),
        homologyMap (relativeMap (ContinuousMap.id _) (Metric.closedBall x r)ᶜ {y}ᶜ
          (exterior_avoids x y r (Metric.ball_subset_closedBall hy))) (n+2) c =
            localGenerator n y :=
  existsUnique_ballGenerator n x r hr

end TernaryPoly.EuclideanBallLocal
