module

public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.LocalHomology

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanBallLocal
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular
open RationalSingularAugmentation EuclideanLocalHomology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Translation from any point in the ball sends the actual exterior into punctured Euclidean space. -/
theorem exterior_translation_punctured (x y : E) (r : ℝ) (hy : y ∈ Metric.closedBall x r) :
    Set.MapsTo (Homeomorph.subRight y).toHomotopyEquiv.toFun (exterior x r) ({0}ᶜ : Set E) := by
  intro z hz
  have h := exterior_avoids x y r hy hz
  change z-y ≠ 0
  exact sub_ne_zero.mpr h

/-- The actual point map followed by canonical translation is the literal translated pair map. -/
theorem ballPointMap_translation (x : E) (r : ℝ) (y : E) (hy : y ∈ Metric.closedBall x r) :
    ballPointMap x r y hy ≫ (translateLocalIso d y).hom =
      relativeMap (Homeomorph.subRight y).toHomotopyEquiv.toFun (exterior x r) {0}ᶜ
        (exterior_translation_punctured x y r hy) := by
  rw [ballPointMap, translateLocalIso, relativeHomeomorphIso_hom]
  erw [RationalRelativeExcision.relativeMap_comp]
  rfl

/-- The explicit affine translation homotopy from centering at x to centering at y. -/
def centeringHomotopy (x y : E) :
    ContinuousMap.Homotopy (Homeomorph.subRight x).toHomotopyEquiv.toFun
      (Homeomorph.subRight y).toHomotopyEquiv.toFun where
  toFun p := p.2-x-(p.1 : ℝ) • (y-x)
  continuous_toFun := (continuous_snd.sub continuous_const).sub
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  map_zero_left z := by simp
  map_one_left z := by simp

/-- The whole translation homotopy stays punctured on the exterior when y is inside the open ball. -/
theorem centeringHomotopy_punctured (x y : E) (r : ℝ) (hy : y ∈ Metric.ball x r) :
    ∀ t z, z ∈ exterior x r → centeringHomotopy x y (t,z) ∈ ({0}ᶜ : Set E) := by
  intro t z hz
  have hz' := (mem_exterior x z r).mp hz
  have hy' : ‖y-x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  change z-x-(t : ℝ) • (y-x) ≠ 0
  intro he
  have he' : z-x = (t : ℝ) • (y-x) := sub_eq_zero.mp he
  have hn : ‖(t : ℝ) • (y-x)‖ ≤ ‖y-x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg _) t.property.2
  rw [← he'] at hn
  linarith

/-- On ball relative homology, all interior point projections agree after the canonical translations.
This is proved from the explicit puncture-preserving homotopy, not from dimensions. -/
theorem ballPointMap_homology_translation (x : E) (r : ℝ) (hr : 0 < r)
    (y : E) (hy : y ∈ Metric.ball x r) (k : ℕ) (hk : k ≠ 0) :
    homologyMap (ballPointMap x r x (Metric.mem_closedBall_self hr.le)) (k+1) ≫
        (translateLocalHomologyIso d x (k+1)).hom =
      homologyMap (ballPointMap x r y (Metric.ball_subset_closedBall hy)) (k+1) ≫
        (translateLocalHomologyIso d y (k+1)).hom := by
  change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
  rw [← homologyMap_comp, ← homologyMap_comp, ballPointMap_translation, ballPointMap_translation]
  exact relativeHomologyMap_eq_of_homotopy _ _ (exterior x r) {0}ᶜ
    (exterior_translation_punctured x x r (Metric.mem_closedBall_self hr.le))
    (exterior_translation_punctured x y r (Metric.ball_subset_closedBall hy))
    (centeringHomotopy x y) (centeringHomotopy_punctured x y r hy) k hk

end TernaryPoly.EuclideanBallLocal
