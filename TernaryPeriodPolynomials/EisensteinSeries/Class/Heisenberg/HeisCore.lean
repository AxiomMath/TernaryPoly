module

public import Mathlib
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamParametricIntegral
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# Averaging over the Heisenberg nilmanifold: one-variable calculus, the invariant frame and the Cartan identity

Formalized by Claude Sonnet 5.5.

Coordinates `(x, y, z)` on `𝒩_R = {[[1,x,z],[0,1,y],[0,0,1]]}`, `p ∈ Pt = ℝ × ℝ × ℝ`.  The left-invariant coframe is `θ¹ = dx`, `θ² = dy`, `θ³ = dz - x dy`
(`dθ³ = -θ¹ ∧ θ²`), the dual left-invariant fields are `X₁ = ∂ₓ`, `X₂ = ∂_y + x ∂_z`, `X₃ = ∂_z` (`Xop`), `[X₁, X₂] = X₃`.

* `avD v r`, `qD v r`: the average of a function over one period `r` along the direction `v` and the (normalized) Bernoulli primitive
  `qD u` along `v`: for `r`-periodic smooth `u`, `∂_v (qD u) = u - avD u` (`ddir_qD_self`), `avD (qD u) = 0` (`avD_qD`), `qD (avD u) = 0`;
  both commute with every directional derivative (`ddir_avD`, `ddir_qD`) and with pointwise continuous linear maps (`avD_lin`, `qD_lin`).
  These are proved without Fourier series, from differentiation under the integral sign (`TernaryPoly.SmoothLocalDeRham.parameterIntegral_smooth`).
* `CartanData`, `Dop`: the exterior-algebra operators `ε_k`, `ι_k` (wedge/contraction with `θᵏ`), the constant part `𝔇` of the
  Chevalley-Eilenberg differential with coefficients, and `D = Σ_k ε_k X_k + 𝔇`.  `cartan_identity`: `D ι_j + ι_j D = X_j + Λ_j`, `Λ_j = [𝔇, ι_j]`.
* `StepSys`: the structure of one averaging step; `StepSys.Lop_Dop`: `L_j = X_j + Λ_j` commutes with `D` (from `D² = 0`).
-/

open scoped ContDiff
open TernaryPoly.SmoothLocalDeRham MeasureTheory Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

/-- Points of the Malcev (matrix) chart of the Heisenberg group. -/
abbrev Pt : Type := ℝ × ℝ × ℝ

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Directional derivative. -/
def ddir (w : Pt) (u : Pt → W) : Pt → W := fun p => fderiv ℝ u p w

omit [CompleteSpace W] in
/-- **Smoothness of a unit-interval parameter integral on the whole space.** -/
theorem contDiff_param {f : Pt × ℝ → W} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y : Pt => ∫ t in (0 : ℝ)..1, f (y, t)) := by
  have h := parameterIntegral_smooth (D := (Set.univ : Set (Pt × ℝ))) isOpen_univ hf.contDiffOn
  have e : sliceDomain (Set.univ : Set (Pt × ℝ)) = Set.univ := by
    ext x; simp [sliceDomain]
  rw [e] at h
  exact contDiffOn_univ.mp h

omit [CompleteSpace W] in
/-- **Differentiation under the integral sign.** -/
theorem fderiv_param {f : Pt × ℝ → W} (hf : ContDiff ℝ ∞ f) (p w : Pt) :
    fderiv ℝ (fun y : Pt => ∫ t in (0 : ℝ)..1, f (y, t)) p w =
      ∫ t in (0 : ℝ)..1, fderiv ℝ f (p, t) (w, 0) := by
  have h := hasFDerivAt_parameterIntegral (D := (Set.univ : Set (Pt × ℝ))) isOpen_univ
    hf.contDiffOn (x := p) (by simp [sliceDomain])
  rw [h.fderiv]
  have hc : Continuous (parameterDerivative f) :=
    continuousOn_univ.mp (parameterDerivative_smooth isOpen_univ hf.contDiffOn).continuousOn
  have hint : IntervalIntegrable (fun t => parameterDerivative f (p, t)) volume 0 1 :=
    (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  rfl

section Averages

variable (v : Pt) (r : ℝ)

/-- **The average over one period along the direction `v`** (period `r`): `(1/r) ∫₀^r u(p + s v) ds`. -/
def avD (u : Pt → W) : Pt → W := fun p => ∫ t in (0 : ℝ)..1, u (p + (t * r) • v)

/-- **The raw Bernoulli primitive along `v`**: `r ∫₀¹ (t - 1/2) u(p + t r v) dt`, a primitive of `u - avD u`
along `v` for `r`-periodic `u`. -/
def qB (u : Pt → W) : Pt → W :=
  fun p => r • ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • u (p + (t * r) • v)

/-- The shift map `(p, t) ↦ p + t r v`. -/
def shiftMap (q : Pt × ℝ) : Pt := q.1 + (q.2 * r) • v

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem shiftMap_contDiff : ContDiff ℝ ∞ (shiftMap v r) := by
  unfold shiftMap
  fun_prop

theorem hasFDerivAt_shiftMap (q : Pt × ℝ) :
    HasFDerivAt (shiftMap v r)
      ((ContinuousLinearMap.fst ℝ Pt ℝ) + (r • ContinuousLinearMap.snd ℝ Pt ℝ).smulRight v) q := by
  unfold shiftMap
  have h1 : HasFDerivAt (fun q : Pt × ℝ => q.1) (ContinuousLinearMap.fst ℝ Pt ℝ) q :=
    (ContinuousLinearMap.fst ℝ Pt ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : Pt × ℝ => q.2 * r) (r • ContinuousLinearMap.snd ℝ Pt ℝ) q := by
    simpa [mul_comm] using ((ContinuousLinearMap.snd ℝ Pt ℝ).hasFDerivAt).const_mul r
  exact h1.add (h2.smul_const v)

omit [CompleteSpace W] in
theorem fderiv_comp_shift {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p w : Pt) (t : ℝ) :
    fderiv ℝ (fun q : Pt × ℝ => u (shiftMap v r q)) (p, t) (w, 0) = fderiv ℝ u (p + (t * r) • v) w := by
  have hu' : DifferentiableAt ℝ u (shiftMap v r (p, t)) :=
    (hu.differentiable (by simp)).differentiableAt
  have h := hu'.hasFDerivAt.comp (p, t) (hasFDerivAt_shiftMap v r (p, t))
  have h' : fderiv ℝ (fun q : Pt × ℝ => u (shiftMap v r q)) (p, t) = _ := h.fderiv
  rw [h']
  simp [shiftMap]

end Averages

section Averages2

variable (v : Pt) (r : ℝ)

omit [CompleteSpace W] in
theorem avD_smooth {u : Pt → W} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (avD v r u) := by
  have hf : ContDiff ℝ ∞ (fun q : Pt × ℝ => u (shiftMap v r q)) := hu.comp (shiftMap_contDiff v r)
  exact contDiff_param hf

omit [CompleteSpace W] in
theorem qB_smooth {u : Pt → W} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (qB v r u) := by
  have hf : ContDiff ℝ ∞ (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ) • u (shiftMap v r q)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ))).smul
      (hu.comp (shiftMap_contDiff v r))
  exact (contDiff_param hf).const_smul r

omit [CompleteSpace W] in
/-- **`avD` commutes with directional derivatives.** -/
theorem ddir_avD {u : Pt → W} (hu : ContDiff ℝ ∞ u) (w : Pt) :
    ddir w (avD v r u) = avD v r (ddir w u) := by
  funext p
  have hf : ContDiff ℝ ∞ (fun q : Pt × ℝ => u (shiftMap v r q)) := hu.comp (shiftMap_contDiff v r)
  unfold ddir avD
  rw [show (fun y : Pt => ∫ t in (0 : ℝ)..1, u (y + (t * r) • v)) =
    (fun y : Pt => ∫ t in (0 : ℝ)..1, (fun q : Pt × ℝ => u (shiftMap v r q)) (y, t)) from rfl,
    fderiv_param hf]
  exact intervalIntegral.integral_congr (fun t _ => fderiv_comp_shift v r hu p w t)

omit [CompleteSpace W] in
/-- **`qB` commutes with directional derivatives.** -/
theorem ddir_qB {u : Pt → W} (hu : ContDiff ℝ ∞ u) (w : Pt) :
    ddir w (qB v r u) = qB v r (ddir w u) := by
  funext p
  have hf : ContDiff ℝ ∞ (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ) • u (shiftMap v r q)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ))).smul
      (hu.comp (shiftMap_contDiff v r))
  unfold ddir qB
  have hdiff : DifferentiableAt ℝ (fun y : Pt => ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • u (y + (t * r) • v)) p :=
    ((contDiff_param hf).differentiable (by simp)).differentiableAt
  rw [show (fun p : Pt => r • ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • u (p + (t * r) • v)) =
    r • (fun y : Pt => ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • u (y + (t * r) • v)) from rfl,
    fderiv_const_smul hdiff, smul_apply]
  rw [show (fun y : Pt => ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • u (y + (t * r) • v)) =
    (fun y : Pt => ∫ t in (0 : ℝ)..1, (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ) • u (shiftMap v r q)) (y, t))
    from rfl, fderiv_param hf]
  congr 1
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have hk : DifferentiableAt ℝ (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ)) (p, t) := by fun_prop
  have hg : DifferentiableAt ℝ (fun q : Pt × ℝ => u (shiftMap v r q)) (p, t) :=
    ((hu.comp (shiftMap_contDiff v r)).differentiable (by simp)).differentiableAt
  have h2 := fderiv_comp_shift v r hu p w t
  have h3 : fderiv ℝ (fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ)) (p, t) = ContinuousLinearMap.snd ℝ Pt ℝ := by
    rw [fderiv_sub_const]
    exact (ContinuousLinearMap.snd ℝ Pt ℝ).fderiv
  change (fderiv ℝ ((fun q : Pt × ℝ => (q.2 - 1 / 2 : ℝ)) • (fun q : Pt × ℝ => u (shiftMap v r q)))
    (p, t)) (w, 0) = _
  rw [fderiv_smul hk hg, h3]
  simp [h2]

end Averages2

section Periodic

variable (v : Pt) (r : ℝ)

/-- `u` is `r`-periodic along `v`. -/
def Per (u : Pt → W) : Prop := ∀ p, u (p + r • v) = u p

/-- `u` is invariant under translation along `v`. -/
def Inv (u : Pt → W) : Prop := ∀ (p : Pt) (t : ℝ), u (p + t • v) = u p

/-- **The normalized Bernoulli primitive along `v`**: `qD u = qB u - avD (qB u)` has average zero. -/
def qD (u : Pt → W) : Pt → W := qB v r u - avD v r (qB v r u)

omit [CompleteSpace W] in
theorem hasDerivAt_line {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p : Pt) (t : ℝ) :
    HasDerivAt (fun t : ℝ => u (p + (t * r) • v)) (r • fderiv ℝ u (p + (t * r) • v) v) t := by
  have hl : HasDerivAt (fun t : ℝ => p + (t * r) • v) (r • v) t := by
    have h1 : HasDerivAt (fun t : ℝ => t * r) r t := by simpa using (hasDerivAt_id t).mul_const r
    simpa using (h1.smul_const v).const_add p
  have := ((hu.differentiable (by simp)) (p + (t * r) • v)).hasFDerivAt.comp_hasDerivAt t hl
  rw [map_smul] at this
  exact this

omit [CompleteSpace W] in
theorem continuous_line {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p : Pt) :
    Continuous (fun t : ℝ => u (p + (t * r) • v)) :=
  hu.continuous.comp (by fun_prop)

omit [CompleteSpace W] in
theorem continuous_ddir_line {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p : Pt) :
    Continuous (fun t : ℝ => ddir v u (p + (t * r) • v)) := by
  have : Continuous (fun x : Pt => fderiv ℝ u x v) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  exact this.comp (by fun_prop)


/-- **Fundamental theorem of calculus along `v`.** -/
theorem integral_ddir_line {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p : Pt) :
    ∫ t in (0 : ℝ)..1, r • ddir v u (p + (t * r) • v) = u (p + r • v) - u p := by
  have h : ∫ t in (0 : ℝ)..1, r • fderiv ℝ u (p + (t * r) • v) v =
      u (p + ((1 : ℝ) * r) • v) - u (p + ((0 : ℝ) * r) • v) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_line v r hu p t)
      (((continuous_ddir_line v r hu p).const_smul r).intervalIntegrable 0 1)
  simpa [ddir] using h

/-- **The Bernoulli primitive**: for `r`-periodic smooth `u`, `∂_v (qB u) = u - avD u`. -/
theorem ddir_qB_self {u : Pt → W} (hu : ContDiff ℝ ∞ u) (hper : Per v r u) :
    ddir v (qB v r u) = fun p => u p - avD v r u p := by
  funext p
  rw [ddir_qB v r hu v]
  unfold qB avD
  set g : ℝ → W := fun t => u (p + (t * r) • v) with hg
  set D : ℝ → W := fun t => ddir v u (p + (t * r) • v) with hD
  have hgc : Continuous g := continuous_line v r hu p
  have hDc : Continuous D := continuous_ddir_line v r hu p
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (t - 1 / 2 : ℝ) • g t)
      ((1 : ℝ) • g t + (t - 1 / 2 : ℝ) • (r • D t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t - 1 / 2 : ℝ)) 1 t := by
      simpa using (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
    have h2 : HasDerivAt g (r • D t) t := hasDerivAt_line v r hu p t
    have := h1.smul h2
    rw [add_comm] at this
    exact this
  have hint : IntervalIntegrable (fun t : ℝ => (1 : ℝ) • g t + (t - 1 / 2 : ℝ) • (r • D t)) MeasureTheory.volume 0 1 :=
    (((continuous_const.smul hgc).add ((by fun_prop : Continuous fun t : ℝ => (t - 1 / 2 : ℝ)).smul
      (hDc.const_smul r)))).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  have hsplit : ∫ t in (0 : ℝ)..1, ((1 : ℝ) • g t + (t - 1 / 2 : ℝ) • (r • D t)) =
      (∫ t in (0 : ℝ)..1, g t) + ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • (r • D t) := by
    rw [intervalIntegral.integral_add]
    · simp
    · exact (continuous_const.smul hgc).intervalIntegrable 0 1
    · exact ((by fun_prop : Continuous fun t : ℝ => (t - 1 / 2 : ℝ)).smul
        (hDc.const_smul r)).intervalIntegrable 0 1
  have h1 : g 1 = u p := by
    simp only [hg, one_mul]; exact hper p
  have h0 : g 0 = u p := by simp [hg]
  have hr : r • ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • D t =
      ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • (r • D t) := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [smul_comm r]
  simp only [hD] at hr
  rw [hr]
  have : (∫ t in (0 : ℝ)..1, g t) + ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) • (r • D t) =
      (1 - 1 / 2 : ℝ) • g 1 - (0 - 1 / 2 : ℝ) • g 0 := by rw [← hsplit]; simpa using hFTC
  rw [h1, h0] at this
  have e : (1 - 1 / 2 : ℝ) • u p - (0 - 1 / 2 : ℝ) • u p = u p := by
    rw [← sub_smul]; norm_num
  rw [e] at this
  rw [eq_sub_iff_add_eq, add_comm]
  exact this


theorem avD_ddir_self {u : Pt → W} (hu : ContDiff ℝ ∞ u) (hper : Per v r u) (hr : r ≠ 0) :
    avD v r (ddir v u) = fun _ => (0 : W) := by
  funext p
  unfold avD
  have h := integral_ddir_line v r hu p
  rw [hper p, sub_self, intervalIntegral.integral_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hr

omit [CompleteSpace W] in
theorem avD_inv {u : Pt → W} (hper : Per v r u) (hr : r ≠ 0) : Inv v (avD v r u) := by
  intro p s
  unfold avD
  have hper' : Function.Periodic (fun t : ℝ => u (p + (t * r) • v)) 1 := by
    intro t
    have : p + ((t + 1) * r) • v = (p + (t * r) • v) + r • v := by
      rw [add_mul, one_mul, add_smul]; abel
    simp only [this]; exact hper _
  have h := hper'.intervalIntegral_add_eq (s / r) 0
  rw [zero_add] at h
  have e1 : ∫ t in (0 : ℝ)..1, u (p + s • v + (t * r) • v) =
      ∫ t in (0 : ℝ)..1, (fun t : ℝ => u (p + (t * r) • v)) (t + s / r) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show u (p + s • v + (t * r) • v) = u (p + ((t + s / r) * r) • v)
    congr 1
    rw [add_mul, div_mul_cancel₀ _ hr, add_smul]; abel
  have e2 := intervalIntegral.integral_comp_add_right (fun t : ℝ => u (p + (t * r) • v)) (a := 0) (b := 1) (s / r)
  rw [zero_add, add_comm 1 (s / r)] at e2
  rw [e1, e2, h]

theorem avD_of_inv {g : Pt → W} (hg : Inv v g) : avD v r g = g := by
  funext p
  unfold avD
  simp [hg p]

theorem qB_of_inv {g : Pt → W} (hg : Inv v g) : qB v r g = fun _ => (0 : W) := by
  funext p
  unfold qB
  have : ∀ t : ℝ, (t - 1 / 2 : ℝ) • g (p + (t * r) • v) = (t - 1 / 2 : ℝ) • g p :=
    fun t => by rw [hg p]
  simp only [this]
  have h0 : ∫ t in (0 : ℝ)..1, (t - 1 / 2 : ℝ) = 0 := by
    simp [intervalIntegral.integral_sub]
  rw [intervalIntegral.integral_smul_const (f := fun t : ℝ => (t - 1 / 2 : ℝ)) (g p), h0]
  simp

omit [CompleteSpace W] in
theorem ddir_of_inv {g : Pt → W} (hg : ContDiff ℝ ∞ g) (hinv : Inv v g) : ddir v g = fun _ => (0 : W) := by
  funext p
  have h := hasDerivAt_line v 1 hg p 0
  have hc : (fun t : ℝ => g (p + (t * 1) • v)) = fun _ => g p := by
    funext t; simp [hinv p t]
  rw [hc] at h
  have := h.unique (hasDerivAt_const (0 : ℝ) (g p))
  simpa [ddir] using this

omit [CompleteSpace W] in
theorem qB_per {u : Pt → W} (hper : Per v r u) : Per v r (qB v r u) := by
  intro p
  unfold qB
  congr 2
  funext t
  have : p + r • v + (t * r) • v = (p + (t * r) • v) + r • v := by abel
  rw [this, hper]

omit [CompleteSpace W] in
theorem avD_per {u : Pt → W} (hper : Per v r u) : Per v r (avD v r u) := by
  intro p
  unfold avD
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have : p + r • v + (t * r) • v = (p + (t * r) • v) + r • v := by abel
  rw [this, hper]

omit [CompleteSpace W] in
theorem qD_per {u : Pt → W} (hper : Per v r u) : Per v r (qD v r u) := by
  intro p
  have h1 := qB_per v r hper p
  have h2 := avD_per v r (qB_per v r hper) p
  simp only [qD, Pi.sub_apply, h1, h2]

omit [CompleteSpace W] in
theorem qD_smooth {u : Pt → W} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (qD v r u) :=
  (qB_smooth v r hu).sub (avD_smooth v r (qB_smooth v r hu))

omit [CompleteSpace W] in
theorem ddir_sub {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : Pt) :
    ddir w (f - g) = ddir w f - ddir w g := by
  funext p
  have hd1 := (hf.differentiable (by simp)).differentiableAt (x := p)
  have hd2 := (hg.differentiable (by simp)).differentiableAt (x := p)
  show fderiv ℝ (f - g) p w = fderiv ℝ f p w - fderiv ℝ g p w
  rw [fderiv_sub hd1 hd2]
  rfl

omit [CompleteSpace W] in
theorem avD_sub {f g : Pt → W} (hf : Continuous f) (hg : Continuous g) :
    avD v r (f - g) = avD v r f - avD v r g := by
  funext p
  unfold avD
  have h1 : IntervalIntegrable (fun t : ℝ => f (p + (t * r) • v)) MeasureTheory.volume 0 1 :=
    (hf.comp (by fun_prop)).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t : ℝ => g (p + (t * r) • v)) MeasureTheory.volume 0 1 :=
    (hg.comp (by fun_prop)).intervalIntegrable 0 1
  exact intervalIntegral.integral_sub h1 h2

omit [CompleteSpace W] in
theorem ddir_qD {u : Pt → W} (hu : ContDiff ℝ ∞ u) (w : Pt) :
    ddir w (qD v r u) = qD v r (ddir w u) := by
  have hq := qB_smooth v r hu
  have ha := avD_smooth v r hq
  unfold qD
  rw [ddir_sub hq ha, ddir_qB v r hu w, ddir_avD v r hq w, ddir_qB v r hu w]

theorem avD_qD {u : Pt → W} (hu : ContDiff ℝ ∞ u) (hper : Per v r u) (hr : r ≠ 0) :
    avD v r (qD v r u) = fun _ => (0 : W) := by
  have hq := qB_smooth v r hu
  have hinv := avD_inv v r (qB_per v r hper) hr
  unfold qD
  rw [avD_sub v r hq.continuous (avD_smooth v r hq).continuous, avD_of_inv v r hinv]
  funext p; simp

theorem ddir_qD_self {u : Pt → W} (hu : ContDiff ℝ ∞ u) (hper : Per v r u) (hr : r ≠ 0) :
    ddir v (qD v r u) = fun p => u p - avD v r u p := by
  have hq := qB_smooth v r hu
  have ha := avD_smooth v r hq
  have hinv := avD_inv v r (qB_per v r hper) hr
  unfold qD
  rw [ddir_sub hq ha, ddir_qB_self v r hu hper, ddir_of_inv v ha hinv]
  funext p; simp

theorem qD_of_inv {g : Pt → W} (hg : Inv v g) : qD v r g = fun _ => (0 : W) := by
  unfold qD
  rw [qB_of_inv v r hg]
  funext p
  simp [avD]




/-! ### Pointwise continuous linear maps commute with the averaging operators -/

section Linear

variable (L : W →L[ℝ] W) (v : Pt) (r : ℝ)

/-- Pointwise application of a continuous linear map of the coefficient space. -/
def lin (L : W →L[ℝ] W) (u : Pt → W) : Pt → W := fun p => L (u p)

omit [CompleteSpace W] in
theorem lin_add (u w : Pt → W) : lin L (u + w) = lin L u + lin L w := by
  funext p; simp [lin]

omit [CompleteSpace W] in
theorem lin_smul (c : ℝ) (u : Pt → W) : lin L (c • u) = c • lin L u := by
  funext p; simp [lin]

omit [CompleteSpace W] in
theorem lin_contDiff {u : Pt → W} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (lin L u) :=
  L.contDiff.comp hu

theorem avD_lin {u : Pt → W} (hu : Continuous u) : avD v r (lin L u) = lin L (avD v r u) := by
  funext p
  unfold avD lin
  have : IntervalIntegrable (fun t : ℝ => u (p + (t * r) • v)) MeasureTheory.volume 0 1 :=
    (hu.comp (by fun_prop)).intervalIntegrable 0 1
  exact ContinuousLinearMap.intervalIntegral_comp_comm L this

theorem qB_lin {u : Pt → W} (hu : Continuous u) : qB v r (lin L u) = lin L (qB v r u) := by
  funext p
  unfold qB lin
  have : IntervalIntegrable (fun t : ℝ => (t - 1 / 2 : ℝ) • u (p + (t * r) • v)) MeasureTheory.volume 0 1 :=
    ((by fun_prop : Continuous fun t : ℝ => (t - 1 / 2 : ℝ)).smul (hu.comp (by fun_prop))).intervalIntegrable 0 1
  rw [map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm L this]
  simp [map_smul]

theorem qD_lin {u : Pt → W} (hu : ContDiff ℝ ∞ u) : qD v r (lin L u) = lin L (qD v r u) := by
  have hq := qB_smooth v r hu
  unfold qD
  rw [qB_lin L v r hu.continuous, avD_lin L v r hq.continuous]
  funext p
  simp [lin]

end Linear


/-! ### The left-invariant frame and the Chevalley-Eilenberg differential -/

section Frame

/-- The coordinate vectors of the Malcev chart. -/
def e1 : Pt := (1, 0, 0)
def e2 : Pt := (0, 1, 0)
def e3 : Pt := (0, 0, 1)

/-- **The left-invariant vector fields** of the Heisenberg group in matrix coordinates `(x, y, z)`
(`[[1, x, z], [0, 1, y], [0, 0, 1]]`): `X₁ = ∂ₓ`, `X₂ = ∂_y + x ∂_z`, `X₃ = ∂_z`, with `[X₁, X₂] = X₃`. -/
def Xop : Fin 3 → (Pt → W) → (Pt → W)
  | 0 => fun u => ddir e1 u
  | 1 => fun u p => ddir e2 u p + p.1 • ddir e3 u p
  | 2 => fun u => ddir e3 u

omit [CompleteSpace W] in
theorem ddir_lin (L : W →L[ℝ] W) {u : Pt → W} (hu : ContDiff ℝ ∞ u) (w : Pt) :
    ddir w (lin L u) = lin L (ddir w u) := by
  funext p
  have hd := (hu.differentiable (by simp)).differentiableAt (x := p)
  have h := L.hasFDerivAt.comp p hd.hasFDerivAt
  show fderiv ℝ (fun x => L (u x)) p w = L (fderiv ℝ u p w)
  have h' : fderiv ℝ (L ∘ u) p = L.comp (fderiv ℝ u p) := h.fderiv
  exact congrArg (fun A => A w) h'

omit [CompleteSpace W] in
theorem Xop_lin (L : W →L[ℝ] W) {u : Pt → W} (hu : ContDiff ℝ ∞ u) (k : Fin 3) :
    Xop k (lin L u) = lin L (Xop k u) := by
  fin_cases k
  · exact ddir_lin L hu e1
  · funext p
    show ddir e2 (lin L u) p + p.1 • ddir e3 (lin L u) p = L (ddir e2 u p + p.1 • ddir e3 u p)
    rw [ddir_lin L hu e2, ddir_lin L hu e3]
    simp [lin]
  · exact ddir_lin L hu e3

/-- **Cartan data**: the exterior algebra operators `ε_j` (wedge with `θʲ`), `ι_j` (contraction), the constant
differential `𝔇` of the Chevalley-Eilenberg complex with coefficients, and nilpotency of the Lie derivatives
`Λ_j = [𝔇, ι_j]`. -/
structure CartanData (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] where
  eps : Fin 3 → W →L[ℝ] W
  iot : Fin 3 → W →L[ℝ] W
  D0 : W →L[ℝ] W
  cartan : ∀ j k, (eps k).comp (iot j) + (iot j).comp (eps k) = if j = k then 1 else 0
  nilpotent : ∃ K : ℕ, ∀ j, ((iot j).comp D0 + D0.comp (iot j)) ^ K = 0

variable (T : CartanData W)

/-- **The Lie derivative on constants** `Λ_j = ι_j 𝔇 + 𝔇 ι_j`. -/
def CartanData.Lam (j : Fin 3) : W →L[ℝ] W := (T.iot j).comp T.D0 + T.D0.comp (T.iot j)

/-- **The differential** `D = Σ_k ε_k X_k + 𝔇` on functions with values in the cochain space. -/
def Dop (u : Pt → W) : Pt → W := (∑ k, lin (T.eps k) (Xop k u)) + lin T.D0 u

omit [CompleteSpace W] in
/-- **Cartan's identity** `D ι_j + ι_j D = X_j + Λ_j`. -/
theorem cartan_identity {u : Pt → W} (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    Dop T (lin (T.iot j) u) + lin (T.iot j) (Dop T u) = Xop j u + lin (T.Lam j) u := by
  funext p
  have hX : ∀ k, Xop k (lin (T.iot j) u) = lin (T.iot j) (Xop k u) := fun k => Xop_lin _ hu k
  simp only [Pi.add_apply, Dop, hX, Finset.sum_apply]
  simp only [lin, Pi.add_apply, Finset.sum_apply]
  rw [map_add, map_sum]
  have key : ∀ k, T.eps k (T.iot j (Xop k u p)) + T.iot j (T.eps k (Xop k u p)) =
      if j = k then Xop k u p else 0 := by
    intro k
    have := congrArg (fun A : W →L[ℝ] W => A (Xop k u p)) (T.cartan j k)
    simp only [add_apply, ContinuousLinearMap.comp_apply] at this
    rw [this]; split_ifs <;> simp
  have hsum : ∑ k, (T.eps k (T.iot j (Xop k u p)) + T.iot j (T.eps k (Xop k u p))) = Xop j u p := by
    simp only [key]
    simp
  calc ∑ k, T.eps k (T.iot j (Xop k u p)) + T.D0 (T.iot j (u p)) +
        (∑ k, T.iot j (T.eps k (Xop k u p)) + T.iot j (T.D0 (u p)))
      = (∑ k, (T.eps k (T.iot j (Xop k u p)) + T.iot j (T.eps k (Xop k u p)))) +
        (T.D0 (T.iot j (u p)) + T.iot j (T.D0 (u p))) := by
        rw [Finset.sum_add_distrib]; abel
    _ = _ := by
        rw [hsum]
        simp [CartanData.Lam]; abel

end Frame


/-! ### Linearity of the averages -/

omit [CompleteSpace W] in
theorem avD_add_fun (v : Pt) (r : ℝ) {f g : Pt → W} (hf : Continuous f) (hg : Continuous g) :
    avD v r (f + g) = avD v r f + avD v r g := by
  funext p
  unfold avD
  have h1 : IntervalIntegrable (fun t : ℝ => f (p + (t * r) • v)) MeasureTheory.volume 0 1 :=
    (hf.comp (by fun_prop)).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t : ℝ => g (p + (t * r) • v)) MeasureTheory.volume 0 1 :=
    (hg.comp (by fun_prop)).intervalIntegrable 0 1
  exact intervalIntegral.integral_add h1 h2

omit [CompleteSpace W] in
theorem avD_sum_fun (v : Pt) (r : ℝ) {ι : Type} (s : Finset ι) (f : ι → Pt → W)
    (hf : ∀ i, Continuous (f i)) : avD v r (∑ i ∈ s, f i) = ∑ i ∈ s, avD v r (f i) := by
  funext p
  unfold avD
  simp only [Finset.sum_apply]
  exact intervalIntegral.integral_finsetSum (fun i _ => (((hf i).comp (by fun_prop)).intervalIntegrable 0 1))

omit [CompleteSpace W] in
theorem avD_smul_fun (v : Pt) (r : ℝ) (c : ℝ) (f : Pt → W) : avD v r (c • f) = c • avD v r f := by
  funext p
  unfold avD
  exact intervalIntegral.integral_smul c _

omit [CompleteSpace W] in
theorem ddir_add {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : Pt) :
    ddir w (f + g) = ddir w f + ddir w g := by
  funext p
  have hd1 := (hf.differentiable (by simp)).differentiableAt (x := p)
  have hd2 := (hg.differentiable (by simp)).differentiableAt (x := p)
  show fderiv ℝ (f + g) p w = fderiv ℝ f p w + fderiv ℝ g p w
  rw [fderiv_add hd1 hd2]
  rfl

omit [CompleteSpace W] in
theorem Xop_add {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin 3) :
    Xop k (f + g) = Xop k f + Xop k g := by
  fin_cases k
  · exact ddir_add hf hg e1
  · funext p
    show ddir e2 (f + g) p + p.1 • ddir e3 (f + g) p = (ddir e2 f p + p.1 • ddir e3 f p) + (ddir e2 g p + p.1 • ddir e3 g p)
    rw [ddir_add hf hg e2, ddir_add hf hg e3]
    simp only [Pi.add_apply, smul_add]
    abel
  · exact ddir_add hf hg e3

omit [CompleteSpace W] in
theorem lin_zero_fun (L : W →L[ℝ] W) : lin L (0 : Pt → W) = 0 := by
  funext p; simp [lin]

omit [CompleteSpace W] in
theorem lin_add_fun (L : W →L[ℝ] W) (u w : Pt → W) : lin L (u + w) = lin L u + lin L w := by
  funext p; simp [lin]

omit [CompleteSpace W] in
theorem Dop_add (T : CartanData W) {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    Dop T (f + g) = Dop T f + Dop T g := by
  unfold Dop
  simp only [Xop_add hf hg, lin_add_fun, Finset.sum_add_distrib]
  abel


/-- **A step of the averaging**: a space of functions `Cin`, the direction `v` and period `r` of the average, and the
structural facts used in the homotopy `D h + h D = 1 - A`. -/
structure StepSys (T : CartanData W) where
  Cin : Submodule ℝ (Pt → W)
  Cout : Submodule ℝ (Pt → W)
  outLe : Cout ≤ Cin
  v : Pt
  r : ℝ
  j : Fin 3
  hr : r ≠ 0
  smooth : ∀ u ∈ Cin, ContDiff ℝ ∞ u
  per : ∀ u ∈ Cin, Per v r u
  closedX : ∀ u ∈ Cin, ∀ k, Xop k u ∈ Cin
  closedLin : ∀ u ∈ Cin, ∀ L : W →L[ℝ] W, lin L u ∈ Cin
  closedQ : ∀ u ∈ Cin, qD v r u ∈ Cin
  avOut : ∀ u ∈ Cin, avD v r u ∈ Cout
  xdir : ∀ u ∈ Cin, Xop j u = ddir v u
  Xq : ∀ u ∈ Cin, ∀ k, Xop k (qD v r u) = qD v r (Xop k u)
  Xa : ∀ u ∈ Cin, ∀ k, Xop k (avD v r u) = avD v r (Xop k u)
  D2 : ∀ u ∈ Cin, Dop T (Dop T u) = 0

section Alg

variable {T : CartanData W} (S : StepSys T)

omit [CompleteSpace W] in
theorem StepSys.Dop_mem {u : Pt → W} (hu : u ∈ S.Cin) : Dop T u ∈ S.Cin := by
  unfold Dop
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => S.closedLin _ (S.closedX u hu k) _)
    (S.closedLin u hu _)

theorem StepSys.avD_Dop {u : Pt → W} (hu : u ∈ S.Cin) :
    Dop T (avD S.v S.r u) = avD S.v S.r (Dop T u) := by
  have hX : ∀ k, Continuous (lin (T.eps k) (Xop k u)) := fun k =>
    (lin_contDiff _ (S.smooth _ (S.closedX u hu k))).continuous
  have hD0 : Continuous (lin T.D0 u) := (lin_contDiff _ (S.smooth u hu)).continuous
  have hsum : Continuous (∑ k, lin (T.eps k) (Xop k u)) := by
    have := continuous_finsetSum Finset.univ (fun k _ => hX k)
    simpa [← Finset.sum_apply] using this
  unfold Dop
  rw [avD_add_fun S.v S.r hsum hD0,
    avD_sum_fun S.v S.r _ _ hX, avD_lin T.D0 S.v S.r (S.smooth u hu).continuous]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [avD_lin (T.eps k) S.v S.r (S.smooth _ (S.closedX u hu k)).continuous, S.Xa u hu k]

/-- The Lie-derivative operator `L_j = X_j + Λ_j`. -/
def StepSys.Lop (u : Pt → W) : Pt → W := Xop S.j u + lin (T.Lam S.j) u

omit [CompleteSpace W] in
theorem StepSys.Lop_eq {u : Pt → W} (hu : u ∈ S.Cin) :
    S.Lop u = Dop T (lin (T.iot S.j) u) + lin (T.iot S.j) (Dop T u) :=
  (cartan_identity T (S.smooth u hu) S.j).symm

omit [CompleteSpace W] in
theorem StepSys.Lop_Dop {u : Pt → W} (hu : u ∈ S.Cin) : S.Lop (Dop T u) = Dop T (S.Lop u) := by
  have h1 := S.Lop_eq hu
  have h2 := S.Lop_eq (S.Dop_mem hu)
  have hiu : lin (T.iot S.j) u ∈ S.Cin := S.closedLin u hu _
  have hDu : Dop T u ∈ S.Cin := S.Dop_mem hu
  have hD2u := S.D2 u hu
  have hD2iu := S.D2 _ hiu
  have e1 : Dop T (S.Lop u) = Dop T (lin (T.iot S.j) (Dop T u)) := by
    rw [h1]
    have : Dop T (Dop T (lin (T.iot S.j) u) + lin (T.iot S.j) (Dop T u)) =
        Dop T (Dop T (lin (T.iot S.j) u)) + Dop T (lin (T.iot S.j) (Dop T u)) :=
      Dop_add T (S.smooth _ (S.Dop_mem hiu)) (S.smooth _ (S.closedLin _ hDu _))
    rw [this, hD2iu, zero_add]
  have e2 : S.Lop (Dop T u) = Dop T (lin (T.iot S.j) (Dop T u)) := by
    rw [h2, hD2u, lin_zero_fun, add_zero]
  rw [e1, e2]

end Alg

end Periodic

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
