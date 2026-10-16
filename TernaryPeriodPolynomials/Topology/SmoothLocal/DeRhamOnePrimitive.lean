module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamLowDegree

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set ContinuousAlternatingMap MeasureTheory
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Decode the alternating one-form as a continuous-linear-map-valued function. -/
def oneLinear (w : RawForm E F 1) : E → E →L[ℝ] F := fun x => oneEquiv.symm (w x)

theorem smooth_oneLinear {s : Set E} {w : RawForm E F 1}
    (hw : ContDiffOn ℝ ∞ w s) : ContDiffOn ℝ ∞ (oneLinear w) s :=
  (oneEquiv (E := E) (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hw

theorem oneEquiv_oneLinear (w : RawForm E F 1) :
    (fun x => oneEquiv (oneLinear w x)) = w := by
  funext x
  exact oneEquiv.apply_symm_apply _

variable [CompleteSpace F]

/-- The actual segment-integral primitive with base point `a`. -/
def segmentPrimitive (a : E) (w : RawForm E F 1) (x : E) : F :=
  curveIntegral (oneLinear w) (Path.segment a x)

theorem segmentPrimitive_hasFDerivAt {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    {w : RawForm E F 1} (hw : ContDiffOn ℝ ∞ w s)
    (hclosed : ∀ x ∈ s, extDeriv w x = 0) {a : E} (ha : a ∈ s)
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (segmentPrimitive a w) (oneLinear w x) x := by
  have hderiv (y : E) (hy : y ∈ s) :
      HasFDerivAt (oneLinear w) (fderiv ℝ (oneLinear w) y) y :=
    (((smooth_oneLinear hw) y hy).contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
      |>.hasFDerivAt
  have hsymm (y : E) (hy : y ∈ s) (u v : E) :
      fderiv ℝ (oneLinear w) y u v = fderiv ℝ (oneLinear w) y v u := by
    apply (extDeriv_oneEquiv_eq_zero_iff (oneLinear w) y).mp
    rw [oneEquiv_oneLinear]
    exact hclosed y hy
  exact (hc.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    (fun y hy => (hderiv y hy).hasFDerivWithinAt)
    (fun y hy u _ v _ => hsymm y hy u v) ha hx).hasFDerivAt (hs.mem_nhds hx)

theorem segmentPrimitive_smooth {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    {w : RawForm E F 1} (hw : ContDiffOn ℝ ∞ w s)
    (hclosed : ∀ x ∈ s, extDeriv w x = 0) {a : E} (ha : a ∈ s) :
    ContDiffOn ℝ ∞ (segmentPrimitive a w) s := by
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hs).mpr
  constructor
  · intro x hx
    exact (segmentPrimitive_hasFDerivAt hs hc hw hclosed ha hx).differentiableAt.differentiableWithinAt
  · apply (smooth_oneLinear hw).congr
    intro x hx
    exact (segmentPrimitive_hasFDerivAt hs hc hw hclosed ha hx).fderiv

/-- The smooth segment integral is an actual primitive in the chart de Rham complex. -/
theorem d_segmentPrimitive {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    (w : Form (F := F) s 1) (hclosed : d hs 1 w = 0) {a : E} (ha : a ∈ s) :
    ∃ f : E → F, ∃ hf : ContDiffOn ℝ ∞ f s,
      f = segmentPrimitive a (w : RawForm E F 1) ∧ d hs 0 (ofFunction f hf) = w := by
  have hd (x : E) (hx : x ∈ s) : extDeriv (w : RawForm E F 1) x = 0 := by
    have hp := congrArg (fun z : Form (F := F) s 2 => (z : RawForm E F 2) x) hclosed
    simpa only [d_apply hs _ hx, ZeroMemClass.coe_zero, Pi.zero_apply] using hp
  refine ⟨segmentPrimitive a (w : RawForm E F 1),
    segmentPrimitive_smooth hs hc (Form.smooth w) hd ha, rfl, ?_⟩
  apply Form.ext
  intro x hx
  rw [d_ofFunction hs _ _ hx, (segmentPrimitive_hasFDerivAt hs hc (Form.smooth w) hd ha hx).fderiv]
  exact oneEquiv.apply_symm_apply _

/-- Every closed smooth one-form on an open convex chart is exact, including the empty domain. -/
theorem poincare_one {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    (w : Form (F := F) s 1) (hclosed : d hs 1 w = 0) :
    ∃ z : Form (F := F) s 0, d hs 0 z = w := by
  rcases s.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · refine ⟨0, ?_⟩
    apply Form.ext
    simp [he]
  · obtain ⟨f, hf, _, hp⟩ := d_segmentPrimitive hs hc w hclosed ha
    exact ⟨ofFunction f hf, hp⟩

end TernaryPoly.SmoothLocalDeRham
