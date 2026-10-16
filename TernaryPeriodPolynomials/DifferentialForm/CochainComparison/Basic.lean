module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.TriangleGreen

@[expose] public section


/-!
# Chart 1-forms: edge integrals, Stokes on affine triangles, and the fundamental theorem for 0-forms

Formalized by Claude Sonnet 5.5.
-/

open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormCochainBridge

open TernaryPoly.SmoothLocalDeRham
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A chart `1`-form as a field of continuous linear maps. -/
def lin1 (η : RawForm E F 1) : E → E →L[ℝ] F :=
  fun x => (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1) 0).symm (η x)

theorem apply_eq_lin1 (η : RawForm E F 1) (x : E) (v : Fin 1 → E) : η x v = lin1 η x (v 0) := by
  have h : η x = ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (lin1 η x) := by
    change η x = ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1) 0
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1) 0).symm (η x))
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [h]
  rfl

theorem lin1_const (η : RawForm E F 1) (x v : E) : lin1 η x v = η x (fun _ => v) := by
  rw [apply_eq_lin1]

theorem contDiffOn_lin1 {s : Set E} {η : RawForm E F 1} (h : ContDiffOn ℝ ∞ η s) :
    ContDiffOn ℝ 1 (lin1 η) s := by
  have := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1) 0).symm.contDiff.comp_contDiffOn
    (h.of_le (WithTop.coe_le_coe.mpr (by exact_mod_cast le_top) : (1 : WithTop ℕ∞) ≤ ∞))
  exact this

/-- The integral of a chart `1`-form along the segment `[x, y]`. -/
def segInt [CompleteSpace F] (η : RawForm E F 1) (x y : E) : F :=
  ∫ t in (0 : ℝ)..1, η (x + t • (y - x)) (fun _ => y - x)

theorem segInt_eq [CompleteSpace F] (η : RawForm E F 1) (x y : E) :
    segInt η x y = segmentIntegral (lin1 η) x y := by
  unfold segInt segmentIntegral
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [lin1_const]

theorem fderiv_apply_const (ℓ : E → E →L[ℝ] F) {x : E} (hℓ : DifferentiableAt ℝ ℓ x) (v w : E) :
    fderiv ℝ (fun y => ℓ y v) x w = fderiv ℝ ℓ x w v := by
  have h := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hℓ.hasFDerivAt
  have : (fun y => ℓ y v) = (ContinuousLinearMap.apply ℝ F v) ∘ ℓ := rfl
  rw [this, h.fderiv]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem removeNth_zero_pair (u v : E) : Fin.removeNth 0 ![u, v] = fun _ => v := by
  funext j
  fin_cases j
  simp [Fin.removeNth, Fin.succAbove]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem removeNth_one_pair (u v : E) : Fin.removeNth 1 ![u, v] = fun _ => u := by
  funext j
  fin_cases j
  simp [Fin.removeNth, Fin.succAbove]

/-- The chart differential of a `1`-form on a pair of vectors. -/
theorem d_one_apply_pair {s : Set E} (hs : IsOpen s) (η : Form (F := F) s 1) {x : E} (hx : x ∈ s)
    (u v : E) :
    (d hs 1 η : RawForm E F 2) x ![u, v] =
      fderiv ℝ (lin1 (η : RawForm E F 1)) x u v - fderiv ℝ (lin1 (η : RawForm E F 1)) x v u := by
  rw [d_apply hs η hx]
  have hd : DifferentiableAt ℝ (η : RawForm E F 1) x :=
    (((Form.smooth η) x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  rw [extDeriv_apply hd, Fin.sum_univ_two]
  have hl : DifferentiableAt ℝ (lin1 (η : RawForm E F 1)) x :=
    ((contDiffOn_lin1 (Form.smooth η)) x hx).contDiffAt (hs.mem_nhds hx) |>.differentiableAt (by simp)
  have e0 : (fun y => (η : RawForm E F 1) y (Fin.removeNth 0 ![u, v])) = fun y => lin1 (η : RawForm E F 1) y v := by
    funext y; rw [removeNth_zero_pair, lin1_const]
  have e1 : (fun y => (η : RawForm E F 1) y (Fin.removeNth 1 ![u, v])) = fun y => lin1 (η : RawForm E F 1) y u := by
    funext y; rw [removeNth_one_pair, lin1_const]
  rw [e0, e1, fderiv_apply_const _ hl, fderiv_apply_const _ hl]
  simp [sub_eq_add_neg]

/-- The triangle integral of a chart `2`-form over the affine triangle `[p₀, p₁, p₂]`. -/
def triInt [CompleteSpace F] (w2 : RawForm E F 2) (p₀ p₁ p₂ : E) : F :=
  ∫ q in stdTriangle, w2 (affTri p₀ p₁ p₂ q) ![p₁ - p₀, p₂ - p₀]

/-- **Stokes on an affine triangle for an exact chart form** `ω = dη`. -/
theorem triInt_d_one [CompleteSpace F] {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    (η : Form (F := F) s 1) {p₀ p₁ p₂ : E} (h₀ : p₀ ∈ s) (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) :
    triInt (d hs 1 η : RawForm E F 2) p₀ p₁ p₂ =
      segInt (η : RawForm E F 1) p₁ p₂ - segInt (η : RawForm E F 1) p₀ p₂ +
        segInt (η : RawForm E F 1) p₀ p₁ := by
  have hT : ∀ p ∈ stdTriangle, p₀ + p.1 • (p₁ - p₀) + p.2 • (p₂ - p₀) ∈ s := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    have : p₀ + a • (p₁ - p₀) + b • (p₂ - p₀) = (1 - a - b) • p₀ + a • p₁ + b • p₂ := by module
    rw [this]
    have key := hc.sum_mem (t := Finset.univ) (w := ![1 - a - b, a, b]) (z := ![p₀, p₁, p₂])
      (by intro i _; fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_three]; ring)
      (by intro i _; fin_cases i <;> simpa)
    simpa [Fin.sum_univ_three] using key
  have hst := stokes_affine_triangle (lin1 (η : RawForm E F 1)) s hs (contDiffOn_lin1 (Form.smooth η)) p₀ p₁ p₂ hT
  rw [segInt_eq, segInt_eq, segInt_eq, ← hst]
  unfold triInt
  refine setIntegral_congr_fun measurableSet_stdTriangle (fun p hp => ?_)
  have hpU := hT p hp
  have : affTri p₀ p₁ p₂ p = p₀ + p.1 • (p₁ - p₀) + p.2 • (p₂ - p₀) := rfl
  rw [this, d_one_apply_pair hs η hpU]

/-- The value function of a chart `0`-form. -/
abbrev val0 {s : Set E} (θ : Form (F := F) s 0) : E → F := toFunction θ

theorem lin1_d_zero {s : Set E} (hs : IsOpen s) (θ : Form (F := F) s 0) {x : E} (hx : x ∈ s) :
    lin1 (d hs 0 θ : RawForm E F 1) x = fderiv ℝ (val0 θ) x := by
  have h := d_ofFunction hs (toFunction θ) (smooth_toFunction θ) hx
  rw [ofFunction_toFunction] at h
  change (oneEquiv (E := E) (F := F)).symm ((d hs 0 θ : RawForm E F 1) x) = _
  rw [h]
  exact (oneEquiv (E := E) (F := F)).symm_apply_apply _

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem segment_mem {s : Set E} (hc : Convex ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ s := hc.add_smul_sub_mem hx hy ht

theorem integrable_segInt {s : Set E} (hc : Convex ℝ s) (η : Form (F := F) s 1) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) :
    IntervalIntegrable (fun t : ℝ => (η : RawForm E F 1) (x + t • (y - x)) (fun _ => y - x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  have hγ : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
  have h1 : ContinuousOn (fun t : ℝ => lin1 (η : RawForm E F 1) (x + t • (y - x)) (y - x)) (Icc 0 1) :=
    ((contDiffOn_lin1 (Form.smooth η)).continuousOn.comp hγ.continuousOn
      (fun t ht => segment_mem hc hx hy ht)).clm_apply continuousOn_const
  refine h1.congr (fun t _ => ?_)
  exact (lin1_const _ _ _).symm

/-- **The fundamental theorem of calculus for a chart `0`-form along a segment.** -/
theorem segInt_d_zero [CompleteSpace F] {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    (θ : Form (F := F) s 0) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    segInt (d hs 0 θ : RawForm E F 1) x y = val0 θ y - val0 θ x := by
  have hΘ : ContDiffOn ℝ 1 (val0 θ) s := (smooth_toFunction θ).of_le (by exact_mod_cast le_top)
  have hγ : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
  have hseg : ∀ t ∈ uIcc (0 : ℝ) 1, x + t • (y - x) ∈ s := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact segment_mem hc hx hy ht
  unfold segInt
  have e : ∀ t ∈ uIcc (0 : ℝ) 1, (d hs 0 θ : RawForm E F 1) (x + t • (y - x)) (fun _ => y - x) =
      fderiv ℝ (val0 θ) (x + t • (y - x)) (y - x) := fun t ht => by
    rw [← lin1_const, lin1_d_zero hs θ (hseg t ht)]
  rw [intervalIntegral.integral_congr e]
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => val0 θ (x + t • (y - x))) (fderiv ℝ (val0 θ) (x + t • (y - x)) (y - x)) t := by
    intro t ht
    have hpt := hseg t ht
    have h1 : HasFDerivAt (val0 θ) (fderiv ℝ (val0 θ) (x + t • (y - x))) (x + t • (y - x)) :=
      ((hΘ.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hpt)).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact h1.comp_hasDerivAt t h2
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ (val0 θ) (x + t • (y - x)) (y - x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hΘ.continuousOn_fderiv_of_isOpen hs (by simp)).comp hγ.continuousOn
      (fun t ht => segment_mem hc hx hy ht) |>.clm_apply continuousOn_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp

end TernaryPeriodPolynomials.Argument.FormCochainBridge
