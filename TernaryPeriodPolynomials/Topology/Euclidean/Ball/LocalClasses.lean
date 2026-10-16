module

public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.LocalCompatibility

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanBallLocal
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular
open EuclideanLocalHomology

/-- The actual closed-ball relative fundamental class is the unique lift of the canonical center generator. -/
def ballGenerator (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (hr : 0 < r) :
    (ballRelativeChains x r).homology (n+2) :=
  (ballHomologyIso x r hr (n+2)).inv (localGenerator n x)

/-- The actual point map at the center sends the closed-ball class to the fixed local generator. -/
theorem ballGenerator_center (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (hr : 0 < r) :
    homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) (n+2)
      (ballGenerator n x r hr) = localGenerator n x := by
  rw [← ballHomologyIso_hom x r hr (n+2)]
  simp [ballGenerator]

/-- The center value determines the actual closed-ball class uniquely. -/
theorem ballGenerator_unique (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (hr : 0 < r)
    (c : (ballRelativeChains x r).homology (n+2))
    (hc : homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) (n+2) c =
      localGenerator n x) : c = ballGenerator n x r hr := by
  apply (ModuleCat.mono_iff_injective (ballHomologyIso x r hr (n+2)).hom).mp inferInstance
  rw [ballHomologyIso_hom, hc, ballGenerator_center]

/-- The actual closed-ball relative fundamental class is nonzero. -/
theorem ballGenerator_ne_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (hr : 0 < r) :
    ballGenerator n x r hr ≠ 0 := by
  intro h
  have he := ballGenerator_center n x r hr
  rw [h, map_zero] at he
  exact localGenerator_ne_zero n x he.symm

/-- The actual closed-ball class has the canonical local value at every interior point.
The equality uses the explicit centering homotopy on the entire exterior. -/
theorem ballGenerator_at_point (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin (n+2))) (hy : y ∈ Metric.ball x r) :
    homologyMap (ballPointMap x r y (Metric.ball_subset_closedBall hy)) (n+2)
      (ballGenerator n x r hr) = localGenerator n y := by
  apply (ModuleCat.mono_iff_injective (localTopAtIso n y).hom).mp inferInstance
  have h := ballPointMap_homology_translation x r hr y hy (n+1) (by omega)
  have hh := congrArg (fun f => f ≫ (localTopIso n).hom) h
  have hmaps :
      homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) (n+2) ≫
          (localTopAtIso n x).hom =
        homologyMap (ballPointMap x r y (Metric.ball_subset_closedBall hy)) (n+2) ≫
          (localTopAtIso n y).hom := by
    simpa [localTopAtIso, Category.assoc] using hh
  have hv := congrArg (fun f => f (ballGenerator n x r hr)) hmaps
  change (localTopAtIso n x).hom
      (homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) (n+2)
        (ballGenerator n x r hr)) =
    (localTopAtIso n y).hom
      (homologyMap (ballPointMap x r y (Metric.ball_subset_closedBall hy)) (n+2)
        (ballGenerator n x r hr)) at hv
  rw [ballGenerator_center] at hv
  simpa [localGenerator] using hv.symm

/-- The closed-ball class is characterized by its values at all actual interior points. -/
theorem existsUnique_ballGenerator (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (hr : 0 < r) :
    ∃! c : (ballRelativeChains x r).homology (n+2),
      ∀ (y : EuclideanSpace ℝ (Fin (n+2))) (hy : y ∈ Metric.ball x r),
        homologyMap (ballPointMap x r y (Metric.ball_subset_closedBall hy)) (n+2) c =
          localGenerator n y := by
  refine ⟨ballGenerator n x r hr, ballGenerator_at_point n x r hr, ?_⟩
  intro c hc
  exact ballGenerator_unique n x r hr c (hc x (Metric.mem_ball_self hr))

end TernaryPoly.EuclideanBallLocal
