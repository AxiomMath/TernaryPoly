module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisStep

@[expose] public section


/-!
# Symmetries of the averaging, derivatives of invariant functions, multiplication by `x`

Formalized by Claude Sonnet 5.5.

* `avD_sym`, `qB_sym`, `qD_sym`: if `g` commutes with the translations along `v` and `u ∘ g = u`, then `avD u`, `qD u` are `g`-invariant too (lattice
  periodicity is preserved by the averages along the central direction, and along the directions that commute with the remaining lattice relations);
* `ddir_of_affine_invariant`, `ddir_translate`: a derivative of a function invariant under an affine map `φ = M + c` is invariant under `φ`
  after the substitution `w ↦ M w` (this is how the left-invariant fields commute with the lattice action);
* `qD_add_fun`, `avD_xmul`, `qD_xmul`: linearity and compatibility with multiplication by the first coordinate when `v` has vanishing first coordinate
  (needed for `X₂ = ∂_y + x ∂_z`).
-/


open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-! ### Symmetries commuting with the averaging direction -/

section Sym

variable (v : Pt) (r : ℝ)

omit [CompleteSpace W] in
/-- **A map commuting with the translations along `v` that fixes `u` fixes `avD u`.** -/
theorem avD_sym {u : Pt → W} (g : Pt → Pt) (hg : ∀ p (s : ℝ), g (p + s • v) = g p + s • v)
    (hu : ∀ p, u (g p) = u p) (p : Pt) : avD v r u (g p) = avD v r u p := by
  unfold avD
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  show u (g p + (t * r) • v) = u (p + (t * r) • v)
  rw [← hg, hu]

omit [CompleteSpace W] in
theorem qB_sym {u : Pt → W} (g : Pt → Pt) (hg : ∀ p (s : ℝ), g (p + s • v) = g p + s • v)
    (hu : ∀ p, u (g p) = u p) (p : Pt) : qB v r u (g p) = qB v r u p := by
  unfold qB
  congr 2
  funext t
  show (t - 1 / 2 : ℝ) • u (g p + (t * r) • v) = (t - 1 / 2 : ℝ) • u (p + (t * r) • v)
  rw [← hg, hu]

omit [CompleteSpace W] in
theorem qD_sym {u : Pt → W} (g : Pt → Pt) (hg : ∀ p (s : ℝ), g (p + s • v) = g p + s • v)
    (hu : ∀ p, u (g p) = u p) (p : Pt) : qD v r u (g p) = qD v r u p := by
  have h1 := qB_sym v r g hg hu p
  have h2 := avD_sym v r (u := qB v r u) g hg (qB_sym v r g hg hu) p
  simp only [qD, Pi.sub_apply, h1, h2]

omit [CompleteSpace W] in
/-- A translation is such a symmetry. -/
theorem translation_commutes (c : Pt) : ∀ p (s : ℝ), (fun q : Pt => q + c) (p + s • v) = (fun q : Pt => q + c) p + s • v := by
  intro p s; show p + s • v + c = p + c + s • v; abel

end Sym

/-! ### Derivatives of invariant functions -/

omit [CompleteSpace W] in
/-- **Derivative of a function invariant under an affine automorphism**: if `u ∘ φ = u` with `φ = M + c`, then
`(∂_{M w} u)(φ p) = (∂_w u)(p)`. -/
theorem ddir_of_affine_invariant {u : Pt → W} (hu : ContDiff ℝ ∞ u) (M : Pt →L[ℝ] Pt) (c : Pt)
    (hinv : ∀ p, u (M p + c) = u p) (w p : Pt) :
    ddir (M w) u (M p + c) = ddir w u p := by
  have hd : DifferentiableAt ℝ u (M p + c) := (hu.differentiable (by simp)).differentiableAt
  have hφ : HasFDerivAt (fun q : Pt => M q + c) M p := M.hasFDerivAt.add_const c
  have h := hd.hasFDerivAt.comp p hφ
  have e : (u ∘ fun q : Pt => M q + c) = u := funext hinv
  rw [e] at h
  have h' : fderiv ℝ u p = (fderiv ℝ u (M p + c)).comp M := h.fderiv
  show fderiv ℝ u (M p + c) (M w) = fderiv ℝ u p w
  rw [h']
  rfl

omit [CompleteSpace W] in
/-- A function invariant under a translation has a derivative invariant under it. -/
theorem ddir_translate {u : Pt → W} (hu : ContDiff ℝ ∞ u) (c : Pt) (hinv : ∀ p, u (p + c) = u p) (w p : Pt) :
    ddir w u (p + c) = ddir w u p := by
  have := ddir_of_affine_invariant hu (ContinuousLinearMap.id ℝ Pt) c (fun p => by simpa using hinv p) w p
  simpa using this

/-! ### Linearity and multiplication by the first coordinate -/

section Mul

variable (v : Pt) (r : ℝ)

omit [CompleteSpace W] in
theorem qB_add_fun {f g : Pt → W} (hf : Continuous f) (hg : Continuous g) :
    qB v r (f + g) = qB v r f + qB v r g := by
  funext p
  unfold qB
  have h1 : IntervalIntegrable (fun t : ℝ => (t - 1 / 2 : ℝ) • f (p + (t * r) • v)) volume 0 1 :=
    ((by fun_prop : Continuous fun t : ℝ => (t - 1 / 2 : ℝ)).smul (hf.comp (by fun_prop))).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t : ℝ => (t - 1 / 2 : ℝ) • g (p + (t * r) • v)) volume 0 1 :=
    ((by fun_prop : Continuous fun t : ℝ => (t - 1 / 2 : ℝ)).smul (hg.comp (by fun_prop))).intervalIntegrable 0 1
  simp only [Pi.add_apply, smul_add]
  rw [intervalIntegral.integral_add h1 h2, smul_add]

omit [CompleteSpace W] in
theorem qD_add_fun {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    qD v r (f + g) = qD v r f + qD v r g := by
  have hqf := qB_smooth v r hf
  have hqg := qB_smooth v r hg
  unfold qD
  rw [qB_add_fun v r hf.continuous hg.continuous, avD_add_fun v r hqf.continuous hqg.continuous]
  abel

omit [CompleteSpace W] in
theorem avD_xmul (hv : v.1 = 0) (f : Pt → W) :
    avD v r (fun p => p.1 • f p) = fun p => p.1 • avD v r f p := by
  funext p
  unfold avD
  have : ∀ t : ℝ, (p + (t * r) • v).1 • f (p + (t * r) • v) = p.1 • f (p + (t * r) • v) := by
    intro t; simp [hv]
  simp only [this]
  exact intervalIntegral.integral_smul p.1 _

omit [CompleteSpace W] in
theorem qB_xmul (hv : v.1 = 0) (f : Pt → W) :
    qB v r (fun p => p.1 • f p) = fun p => p.1 • qB v r f p := by
  funext p
  unfold qB
  have : ∀ t : ℝ, (t - 1 / 2 : ℝ) • ((p + (t * r) • v).1 • f (p + (t * r) • v)) =
      p.1 • ((t - 1 / 2 : ℝ) • f (p + (t * r) • v)) := by
    intro t; simp only [hv, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero]
    exact smul_comm _ _ _
  simp only [this]
  rw [intervalIntegral.integral_smul p.1 _, smul_comm]

omit [CompleteSpace W] in
theorem qD_xmul (hv : v.1 = 0) (f : Pt → W) :
    qD v r (fun p => p.1 • f p) = fun p => p.1 • qD v r f p := by
  unfold qD
  rw [qB_xmul v r hv, avD_xmul v r hv]
  funext p; simp [smul_sub]

end Mul

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
