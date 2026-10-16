module

public import TernaryPeriodPolynomials.Topology.Euclidean.Local.OrientationNaturality
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanBallLocal
open CategoryTheory HomologicalComplex ContractibleSingularHomology RationalRelativeSingular
open scoped unitInterval

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual open exterior of the closed Euclidean ball. -/
abbrev exterior (x : E) (r : ℝ) : Set E := (Metric.closedBall x r)ᶜ

/-- Membership in the exterior is the strict radial norm inequality. -/
theorem mem_exterior (x z : E) (r : ℝ) : z ∈ exterior x r ↔ r < ‖z-x‖ := by
  simp [exterior, Metric.mem_closedBall, dist_eq_norm]

/-- Every exterior point is different from the center. -/
theorem exterior_subset_punctured (x : E) (r : ℝ) (hr : 0 < r) :
    exterior x r ⊆ ({x}ᶜ : Set E) := by
  intro z hz
  have h := (mem_exterior x z r).mp hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro he
  subst z
  simp only [sub_self, norm_zero] at h
  linarith

/-- The exact norm of the outward radial homotopy at parameter t. -/
theorem radial_norm (x z : E) (r : ℝ) (hr : 0 ≤ r) (t : unitInterval) (hz : z ≠ x) :
    ‖(x + (1 + (1-(t : ℝ))*r/‖z-x‖) • (z-x))-x‖ = ‖z-x‖ + (1-(t : ℝ))*r := by
  have hn : 0 < ‖z-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have ht : 0 ≤ 1-(t : ℝ) := sub_nonneg.mpr t.property.2
  have he : x + (1 + (1-(t : ℝ))*r/‖z-x‖) • (z-x)-x =
      (1 + (1-(t : ℝ))*r/‖z-x‖) • (z-x) := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, one_mul,
    div_mul_cancel₀ _ (ne_of_gt hn)]

/-- The literal inclusion from the exterior to the punctured Euclidean space. -/
def exteriorInclusion (x : E) (r : ℝ) (hr : 0 < r) : C(exterior x r, ({x}ᶜ : Set E)) :=
  subspaceMap (ContinuousMap.id E) (exterior x r) {x}ᶜ (exterior_subset_punctured x r hr)

/-- The explicit outward radial inverse sends every punctured point outside the closed ball. -/
def radialPush (x : E) (r : ℝ) (hr : 0 < r) : C(({x}ᶜ : Set E), exterior x r) where
  toFun z := ⟨x + (1+r/‖z.val-x‖) • (z.val-x), by
    apply (mem_exterior x _ r).mpr
    have hz : z.val ≠ x := z.property
    have hn : 0 < ‖z.val-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have h := radial_norm x z.val r hr.le 0 hz
    have he : ‖x + (1+r/‖z.val-x‖) • (z.val-x)-x‖ = ‖z.val-x‖ + r := by simpa using h
    rw [he]
    linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hv : Continuous (fun z : ({x}ᶜ : Set E) => z.val-x) :=
      continuous_subtype_val.sub continuous_const
    have hn : Continuous (fun z : ({x}ᶜ : Set E) => ‖z.val-x‖) := hv.norm
    have hc : Continuous (fun z : ({x}ᶜ : Set E) => (1:ℝ)+r/‖z.val-x‖) :=
      continuous_const.add (continuous_const.div hn
        (fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)))
    exact continuous_const.add (hc.smul hv)

/-- The outward radial formula is jointly continuous wherever the center is excluded. -/
theorem radial_continuous (x : E) (r : ℝ) (S : Set E) (hS : S ⊆ ({x}ᶜ : Set E)) :
    Continuous (fun p : unitInterval × S =>
      x + (1+(1-(p.1 : ℝ))*r/‖p.2.val-x‖) • (p.2.val-x)) := by
  have hv : Continuous (fun p : unitInterval × S => p.2.val-x) :=
    (continuous_subtype_val.comp continuous_snd).sub continuous_const
  have ht : Continuous (fun p : unitInterval × S => (1:ℝ)-(p.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hc : Continuous (fun p : unitInterval × S => (1:ℝ)+(1-(p.1 : ℝ))*r/‖p.2.val-x‖) :=
    continuous_const.add ((ht.mul continuous_const).div hv.norm
      (fun p => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hS p.2.property))))
  exact continuous_const.add (hc.smul hv)

/-- The radial deformation stays in the actual exterior at every time. -/
theorem radial_exterior (x z : E) (r : ℝ) (hr : 0 < r) (t : unitInterval)
    (hz : z ∈ exterior x r) :
    x + (1+(1-(t : ℝ))*r/‖z-x‖) • (z-x) ∈ exterior x r := by
  apply (mem_exterior x _ r).mpr
  rw [radial_norm x z r hr.le t (exterior_subset_punctured x r hr hz)]
  have h := (mem_exterior x z r).mp hz
  have hnonneg : 0 ≤ (1-(t : ℝ))*r := mul_nonneg (sub_nonneg.mpr t.property.2) hr.le
  linarith

/-- The radial deformation stays punctured at every time. -/
theorem radial_punctured (x z : E) (r : ℝ) (hr : 0 < r) (t : unitInterval)
    (hz : z ≠ x) : x + (1+(1-(t : ℝ))*r/‖z-x‖) • (z-x) ≠ x := by
  intro he
  have hn := radial_norm x z r hr.le t hz
  rw [he, sub_self, norm_zero] at hn
  have hp : 0 < ‖z-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hnonneg : 0 ≤ (1-(t : ℝ))*r := mul_nonneg (sub_nonneg.mpr t.property.2) hr.le
  linarith

/-- The radial push followed by exterior inclusion deforms to the literal identity in the exterior. -/
def exteriorRadialHomotopy (x : E) (r : ℝ) (hr : 0 < r) :
    ContinuousMap.Homotopy ((radialPush x r hr).comp (exteriorInclusion x r hr))
      (ContinuousMap.id (exterior x r)) where
  toFun p := ⟨x + (1+(1-(p.1 : ℝ))*r/‖p.2.val-x‖) • (p.2.val-x),
    radial_exterior x p.2.val r hr p.1 p.2.property⟩
  continuous_toFun := (radial_continuous x r (exterior x r) (exterior_subset_punctured x r hr)).subtype_mk _
  map_zero_left z := by ext; simp [radialPush, exteriorInclusion, subspaceMap]
  map_one_left z := by ext; simp

/-- The actual inclusion followed by radial push deforms to the literal identity in the puncture. -/
def puncturedRadialHomotopy (x : E) (r : ℝ) (hr : 0 < r) :
    ContinuousMap.Homotopy ((exteriorInclusion x r hr).comp (radialPush x r hr))
      (ContinuousMap.id ({x}ᶜ : Set E)) where
  toFun p := ⟨x + (1+(1-(p.1 : ℝ))*r/‖p.2.val-x‖) • (p.2.val-x),
    radial_punctured x p.2.val r hr p.1 p.2.property⟩
  continuous_toFun := (radial_continuous x r ({x}ᶜ : Set E) (fun _ hz => hz)).subtype_mk _
  map_zero_left z := by ext; simp [radialPush, exteriorInclusion, subspaceMap]
  map_one_left z := by ext; simp

/-- The literal exterior-to-puncture inclusion is a genuine homotopy equivalence. -/
def exteriorHomotopyEquiv (x : E) (r : ℝ) (hr : 0 < r) :
    ContinuousMap.HomotopyEquiv (exterior x r) ({x}ᶜ : Set E) where
  toFun := exteriorInclusion x r hr
  invFun := radialPush x r hr
  left_inv := ⟨exteriorRadialHomotopy x r hr⟩
  right_inv := ⟨puncturedRadialHomotopy x r hr⟩

end TernaryPoly.EuclideanBallLocal
