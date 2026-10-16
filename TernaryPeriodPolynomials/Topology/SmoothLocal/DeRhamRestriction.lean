module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamPoincare

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set Filter
open scoped ContDiff Topology

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- Restriction of actual smooth forms to a smaller chart domain. -/
def restrictTo {s t : Set E} (hts : t ⊆ s) (n : ℕ) :
    Form (F := F) s n →ₗ[ℝ] Form (F := F) t n where
  toFun w := restrictForm t (w : RawForm E F n) ((Form.smooth w).mono hts)
  map_add' w z := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem restrictTo_apply {s t : Set E} (hts : t ⊆ s) (w : Form (F := F) s n)
    {x : E} (hx : x ∈ t) :
    (restrictTo hts n w : RawForm E F n) x = (w : RawForm E F n) x := by
  simp [restrictTo, hx]

/-- Chart restriction commutes with the literal exterior differential. -/
theorem restrictTo_d {s t : Set E} (hs : IsOpen s) (ht : IsOpen t) (hts : t ⊆ s)
    (w : Form (F := F) s n) : restrictTo hts (n + 1) (d hs n w) = d ht n (restrictTo hts n w) := by
  apply Form.ext
  intro x hx
  rw [restrictTo_apply hts _ hx, d_apply hs _ (hts hx), d_apply ht _ hx]
  have he : (restrictTo hts n w : RawForm E F n) =ᶠ[𝓝 x] (w : RawForm E F n) := by
    filter_upwards [ht.mem_nhds hx] with y hy using restrictTo_apply hts w hy
  exact he.extDeriv_eq.symm

variable [FiniteDimensional ℝ E] [CompleteSpace F]

/-- Every point of an arbitrary open chart has a convex neighborhood with local smooth primitives
in every positive degree. -/
theorem local_poincare {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    ∃ r > (0 : ℝ), ∃ hball : Metric.ball x r ⊆ s,
      ∀ (n : ℕ) (w : Form (F := F) s (n + 1)), d hs (n + 1) w = 0 →
        ∃ z : Form (F := F) (Metric.ball x r) n,
          d Metric.isOpen_ball n z = restrictTo hball (n + 1) w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs x hx
  refine ⟨r, hr, hball, fun n w hw => ?_⟩
  apply poincare_convex Metric.isOpen_ball (convex_ball x r)
  rw [← restrictTo_d hs Metric.isOpen_ball hball, hw, _root_.map_zero]

end TernaryPoly.SmoothLocalDeRham
