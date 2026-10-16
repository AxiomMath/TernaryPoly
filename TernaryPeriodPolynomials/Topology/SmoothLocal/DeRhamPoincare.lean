module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamHomotopy
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamOnePrimitive
public import Mathlib.Analysis.Convex.Star

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set Filter MeasureTheory ContinuousAlternatingMap
open scoped ContDiff Topology

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

theorem starConvex_subset_sliceDomain {s : Set E} {a : E} (hc : StarConvex ℝ a s) :
    s ⊆ sliceDomain (radialDomain a s) := by
  intro x hx t ht
  exact hc.add_smul_sub_mem hx ht.1 ht.2

theorem radialHomotopy_congr {s : Set E} {a : E} (hc : StarConvex ℝ a s)
    {w z : RawForm E F (n + 1)} (he : EqOn w z s) :
    EqOn (radialHomotopy a w) (radialHomotopy a z) s := by
  intro x hx
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only [radialIntegrand]
  rw [he (starConvex_subset_sliceDomain hc hx t (by simpa using ht))]

variable [FiniteDimensional ℝ E] [CompleteSpace F]

/-- Restrict the actual radial primitive to a star-convex open chart. -/
def homotopy {s : Set E} (hs : IsOpen s) (a : E) (hc : StarConvex ℝ a s) (n : ℕ) :
    Form (F := F) s (n + 1) →ₗ[ℝ] Form (F := F) s n where
  toFun w := restrictForm s (radialHomotopy a (w : RawForm E F (n + 1)))
    ((radialHomotopy_smooth hs a (Form.smooth w)).mono (starConvex_subset_sliceDomain hc))
  map_add' w z := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
    unfold radialHomotopy
    have he : (fun t => radialIntegrand a ((w : RawForm E F (n + 1)) + (z : RawForm E F (n + 1))) (x, t)) =
        (fun t => radialIntegrand a (w : RawForm E F (n + 1)) (x, t) + radialIntegrand a (z : RawForm E F (n + 1)) (x, t)) := by
      funext t
      simp [radialIntegrand, curryLeft_add, smul_add]
    rw [he]
    exact intervalIntegral.integral_add
      (radialIntegrand_intervalIntegrable a (Form.smooth w) (starConvex_subset_sliceDomain hc hx))
      (radialIntegrand_intervalIntegrable a (Form.smooth z) (starConvex_subset_sliceDomain hc hx))
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
    unfold radialHomotopy
    have he : (fun t => radialIntegrand a (c • (w : RawForm E F (n + 1))) (x, t)) =
        (fun t => c • radialIntegrand a w (x, t)) := by
      funext t
      simp only [radialIntegrand, Pi.smul_apply, curryLeft_smul, _root_.smul_apply]
      exact smul_comm _ _ _
    rw [he, intervalIntegral.integral_smul]

omit [CompleteSpace F] in
@[simp] theorem homotopy_apply {s : Set E} (hs : IsOpen s) (a : E) (hc : StarConvex ℝ a s)
    (w : Form (F := F) s (n + 1)) {x : E} (hx : x ∈ s) :
    (homotopy hs a hc n w : RawForm E F n) x = radialHomotopy a (w : RawForm E F (n + 1)) x := by
  simp [homotopy, hx]

/-- The chart complex has a genuine explicit contracting homotopy in every positive degree. -/
theorem d_homotopy_add_homotopy_d {s : Set E} (hs : IsOpen s) (a : E) (hc : StarConvex ℝ a s)
    (w : Form (F := F) s (n + 1)) :
    d hs n (homotopy hs a hc n w) + homotopy hs a hc (n + 1) (d hs (n + 1) w) = w := by
  apply Form.ext
  intro x hx
  change (d hs n (homotopy hs a hc n w) : RawForm E F (n + 1)) x +
    (homotopy hs a hc (n + 1) (d hs (n + 1) w) : RawForm E F (n + 1)) x = _
  rw [d_apply hs _ hx, homotopy_apply hs a hc _ hx]
  have he : (homotopy hs a hc n w : RawForm E F n) =ᶠ[𝓝 x]
      radialHomotopy a (w : RawForm E F (n + 1)) := by
    filter_upwards [hs.mem_nhds hx] with y hy using homotopy_apply hs a hc w hy
  rw [he.extDeriv_eq]
  rw [radialHomotopy_congr hc (fun y hy => d_apply hs w hy) hx]
  exact radial_homotopy_identity hs a (Form.smooth w) (starConvex_subset_sliceDomain hc hx)

/-- Every closed smooth positive-degree form on an open star-convex domain has the radial primitive. -/
theorem poincare_starConvex {s : Set E} (hs : IsOpen s) (a : E) (hc : StarConvex ℝ a s)
    (w : Form (F := F) s (n + 1)) (hclosed : d hs (n + 1) w = 0) :
    d hs n (homotopy hs a hc n w) = w := by
  simpa only [hclosed, _root_.map_zero, add_zero] using d_homotopy_add_homotopy_d hs a hc w

/-- The local Poincare lemma in all positive degrees on an open convex real chart. -/
theorem poincare_convex {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    (w : Form (F := F) s (n + 1)) (hclosed : d hs (n + 1) w = 0) :
    ∃ z : Form (F := F) s n, d hs n z = w := by
  rcases s.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · refine ⟨0, ?_⟩
    apply Form.ext
    simp [he]
  · exact ⟨homotopy hs a (hc.starConvex ha) n w, poincare_starConvex hs a (hc.starConvex ha) w hclosed⟩

/-- Exactness of the actual smooth de Rham differential complex in every positive degree. -/
theorem range_d_eq_ker_d {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s) (n : ℕ) :
    LinearMap.range (d (F := F) hs n) = LinearMap.ker (d hs (n + 1)) := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact d_squared hs n z
  · intro hw
    exact poincare_convex hs hc w hw

end TernaryPoly.SmoothLocalDeRham
