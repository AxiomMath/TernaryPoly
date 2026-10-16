module

public import TernaryPeriodPolynomials.Topology.Euclidean.Ball.Local
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanConvexLocal
open CategoryTheory HomologicalComplex RationalRelativeSingular EuclideanBallLocal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The complement of a set avoids every specified point of that set. -/
theorem complement_avoids (K : Set E) (x : E) (hx : x ∈ K) : Kᶜ ⊆ ({x}ᶜ : Set E) := by
  intro z hz he
  exact hz (he ▸ hx)

/-- An outward ray from a point of a convex set cannot reenter it after leaving. -/
theorem convex_outward_not_mem (K : Set E) (hK : Convex ℝ K) (x z : E) (hx : x ∈ K)
    (hz : z ∉ K) (a : ℝ) (ha : 1 ≤ a) : x + a • (z-x) ∉ K := by
  intro hw
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hainv : a⁻¹ ≤ 1 := (inv_le_one₀ hap).mpr ha
  have h := hK hx hw (sub_nonneg.mpr hainv) (inv_nonneg.mpr hap.le)
    (sub_add_cancel (1:ℝ) a⁻¹)
  have he : (1-a⁻¹) • x + a⁻¹ • (x+a • (z-x)) = z := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hap), one_smul]
    module
  exact hz (he ▸ h)

/-- Every compact set is contained in a closed ball of positive radius about any chosen center. -/
theorem compact_containing_ball (K : Set E) (hK : IsCompact K) (x : E) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall x R := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball x).mp hK.isBounded
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  exact hR.trans (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (le_max_left R 1)))

/-- The literal inclusion of the actual complement into the punctured ambient space. -/
def complementInclusion (K : Set E) (x : E) (hx : x ∈ K) : C((Kᶜ : Set E), ({x}ᶜ : Set E)) :=
  subspaceMap (ContinuousMap.id E) Kᶜ {x}ᶜ (complement_avoids K x hx)

/-- The exterior of a containing ball includes literally into the complement. -/
def exteriorToComplement (K : Set E) (x : E) (R : ℝ) (hKR : K ⊆ Metric.closedBall x R) :
    C(exterior x R, (Kᶜ : Set E)) :=
  ⟨fun z => ⟨z.val, fun hz => z.property (hKR hz)⟩, continuous_subtype_val.subtype_mk _⟩

/-- The explicit radial deformation remains outside any convex support containing its center. -/
def complementRadialHomotopy (K : Set E) (hK : Convex ℝ K) (x : E) (hx : x ∈ K)
    (R : ℝ) (hR : 0 < R) (hKR : K ⊆ Metric.closedBall x R) :
    ContinuousMap.Homotopy
      (((exteriorToComplement K x R hKR).comp (radialPush x R hR)).comp (complementInclusion K x hx))
      (ContinuousMap.id (Kᶜ : Set E)) where
  toFun p := ⟨x + (1+(1-(p.1 : ℝ))*R/‖p.2.val-x‖) • (p.2.val-x),
    convex_outward_not_mem K hK x p.2.val hx p.2.property _ (by
      have ht : 0 ≤ 1-(p.1 : ℝ) := sub_nonneg.mpr p.1.property.2
      have : 0 ≤ (1-(p.1 : ℝ))*R/‖p.2.val-x‖ := by positivity
      linarith)⟩
  continuous_toFun := (radial_continuous x R Kᶜ (complement_avoids K x hx)).subtype_mk _
  map_zero_left z := by ext; simp [exteriorToComplement, radialPush, complementInclusion, subspaceMap]
  map_one_left z := by ext; simp

/-- For any containing ball, the actual complement inclusion has the explicit outward radial inverse. -/
def boundedComplementHomotopyEquiv (K : Set E) (hK : Convex ℝ K) (x : E) (hx : x ∈ K)
    (R : ℝ) (hR : 0 < R) (hKR : K ⊆ Metric.closedBall x R) :
    ContinuousMap.HomotopyEquiv (Kᶜ : Set E) ({x}ᶜ : Set E) where
  toFun := complementInclusion K x hx
  invFun := (exteriorToComplement K x R hKR).comp (radialPush x R hR)
  left_inv := ⟨complementRadialHomotopy K hK x hx R hR hKR⟩
  right_inv := ⟨puncturedRadialHomotopy x R hR⟩

/-- The actual inclusion of a compact convex complement into any of its punctured point spaces
is a homotopy equivalence, including for lower-dimensional or singleton supports. -/
def complementHomotopyEquiv (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (x : E) (hx : x ∈ K) : ContinuousMap.HomotopyEquiv (Kᶜ : Set E) ({x}ᶜ : Set E) := by
  let R := (compact_containing_ball K hK x).choose
  have hR := (compact_containing_ball K hK x).choose_spec
  exact boundedComplementHomotopyEquiv K hconv x hx R hR.1 hR.2

/-- The forward map of the compact-convex equivalence is the literal inclusion. -/
theorem complementHomotopyEquiv_toFun (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (x : E) (hx : x ∈ K) : (complementHomotopyEquiv K hK hconv x hx).toFun =
      complementInclusion K x hx := rfl

end TernaryPoly.EuclideanConvexLocal
