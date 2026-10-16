module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamHomotopy
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamContraction

@[expose] public section


/-!
# Cartan's homotopy formula for a translation

The Lie derivative along a translation of the fiber is `d ι + ι d`.

* `extDeriv_insert_const`: for a constant vector `a`, `d(ι_a w) + ι_a(dw) = ∂_a w` (Mathlib normalization
  of `extDeriv`, from `alternatize_insert`).
* `extDeriv_paramIntegral`: `d` commutes with an interval integral over a smooth parameter.
* `cartan_raw`: with `cartanRaw a W x = ∫₀¹ ι_a W(x + s a) ds`,
  `d(cartanRaw a W) + cartanRaw a (dW) = W(· + a) - W` on an open set stable under the translations
  `x ↦ x + s a`, `s ∈ [0,1]`.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly.SmoothLocalDeRham Set MeasureTheory ContinuousAlternatingMap
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

section General

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- **Cartan's formula for a constant vector field**: `d(ι_a w) + ι_a(dw) = ∂_a w`. -/
theorem extDeriv_insert_const {w : RawForm E F (k + 1)} {y : E} (hw : DifferentiableAt ℝ w y)
    (a : E) :
    extDeriv (fun z => (w z).curryLeft a) y + (extDeriv w y).curryLeft a = fderiv ℝ w y a := by
  unfold extDeriv
  have hc : HasFDerivAt (fun z => (w z).curryLeft a) ((insertCLM a).comp (fderiv ℝ w y)) y :=
    (insertCLM (E := E) (F := F) (n := k) a).hasFDerivAt.comp y hw.hasFDerivAt
  rw [hc.fderiv]
  exact alternatize_insert (fderiv ℝ w y) a

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem pd_intervalIntegrable {D : Set (E × ℝ)} (hD : IsOpen D) (f : E × ℝ → E [⋀^Fin k]→L[ℝ] F)
    (hf : ContDiffOn ℝ ∞ f D) {x : E} (hx : x ∈ sliceDomain D) :
    IntervalIntegrable (fun t => parameterDerivative f (x, t)) volume 0 1 := by
  exact ((parameterDerivative_smooth hD hf).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hx).intervalIntegrable_of_Icc zero_le_one

/-- **`d` commutes with an interval integral over a smooth parameter.** -/
theorem extDeriv_paramIntegral {D : Set (E × ℝ)} (hD : IsOpen D) (f : E × ℝ → E [⋀^Fin k]→L[ℝ] F)
    (hf : ContDiffOn ℝ ∞ f D) {x : E} (hx : x ∈ sliceDomain D) :
    extDeriv (fun y => ∫ t in (0:ℝ)..1, f (y, t)) x =
      ∫ t in (0:ℝ)..1, extDeriv (fun y => f (y, t)) x := by
  unfold extDeriv
  rw [(hasFDerivAt_parameterIntegral hD hf hx).fderiv]
  unfold alternatizeUncurryFin
  rw [← (alternatizeUncurryFinCLM ℝ E F (n := k)).intervalIntegral_comp_comm
    (pd_intervalIntegrable hD f hf hx)]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [(parameterDerivative_hasFDerivAt hD hf (hx t (by simpa using ht))).fderiv]

/-- The Cartan primitive along the segment `[x, x + a]`: `∫₀¹ ι_a W (x + s a) ds`. -/
def cartanRaw (a : E) (W : RawForm E F (k + 1)) (x : E) : E [⋀^Fin k]→L[ℝ] F :=
  ∫ s in (0:ℝ)..1, (W (x + s • a)).curryLeft a

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem extDeriv_comp_add_const (W : RawForm E F k) (c : E) {x : E} :
    extDeriv (fun y => W (y + c)) x = extDeriv W (x + c) := by
  unfold extDeriv
  rw [fderiv_comp_add_right]

variable {U : Set E}

omit [FiniteDimensional ℝ E] in
theorem cartan_domain_open (hU : IsOpen U) (a : E) :
    IsOpen {p : E × ℝ | p.1 + p.2 • a ∈ U} :=
  hU.preimage (by fun_prop)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem contDiffOn_cartan_integrand (a : E) {W : RawForm E F (k + 1)}
    (hW : ContDiffOn ℝ ∞ W U) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => (W (p.1 + p.2 • a)).curryLeft a)
      {p : E × ℝ | p.1 + p.2 • a ∈ U} := by
  have h1 : ContDiffOn ℝ ∞ (fun p : E × ℝ => W (p.1 + p.2 • a))
      {p : E × ℝ | p.1 + p.2 • a ∈ U} :=
    hW.comp (by fun_prop : ContDiff ℝ ∞ (fun p : E × ℝ => p.1 + p.2 • a)).contDiffOn
      (fun p hp => hp)
  exact (insertCLM (E := E) (F := F) (n := k) a).contDiff.comp_contDiffOn h1

theorem cartan_raw (hU : IsOpen U) (a : E) (hUa : ∀ x ∈ U, ∀ s ∈ Icc (0:ℝ) 1, x + s • a ∈ U)
    {W : RawForm E F (k + 1)} (hW : ContDiffOn ℝ ∞ W U) {x : E} (hx : x ∈ U) :
    extDeriv (cartanRaw a W) x + cartanRaw a (extDeriv W) x = W (x + a) - W x := by
  have hD := cartan_domain_open hU a
  have hf := contDiffOn_cartan_integrand a hW
  have hxD : x ∈ sliceDomain {p : E × ℝ | p.1 + p.2 • a ∈ U} := fun s hs => hUa x hx s hs
  have h1 := extDeriv_paramIntegral hD _ hf hxD
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ W y := fun y hy =>
    ((hW y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  -- integrability of the two integrands
  have hi1 : IntervalIntegrable (fun t : ℝ => extDeriv (fun y => (W (y + t • a)).curryLeft a) x)
      volume 0 1 := by
    have hc : ContinuousOn (fun t => alternatizeUncurryFinCLM ℝ E F (n := k)
        (parameterDerivative (fun p : E × ℝ => (W (p.1 + p.2 • a)).curryLeft a) (x, t)))
        (Icc (0 : ℝ) 1) := by
      apply (alternatizeUncurryFinCLM ℝ E F (n := k)).continuous.comp_continuousOn
      exact (parameterDerivative_smooth hD hf).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hxD
    apply (hc.intervalIntegrable_of_Icc zero_le_one).congr
    intro t ht
    dsimp only
    unfold extDeriv
    rw [(parameterDerivative_hasFDerivAt hD hf (hxD t (by simpa using uIoc_subset_uIcc ht))).fderiv]
    rfl
  have hi2 : IntervalIntegrable (fun t : ℝ => (extDeriv W (x + t • a)).curryLeft a) volume 0 1 := by
    have hs := smooth_extDeriv hU hW
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    have hc := hs.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => x + t • a).continuousOn
        (fun t ht => hUa x hx t ht)
    exact (insertCLM (E := E) (F := F) (n := k + 1) a).continuous.comp_continuousOn hc
  unfold cartanRaw
  rw [h1, ← intervalIntegral.integral_add hi1 hi2]
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, extDeriv (fun y => (W (y + t • a)).curryLeft a) x +
      (extDeriv W (x + t • a)).curryLeft a = fderiv ℝ W (x + t • a) a := by
    intro t ht
    have hWd : DifferentiableAt ℝ (fun y => W (y + t • a)) x := by
      have := (hdiff _ (hUa x hx t ht)).comp x ((differentiableAt_id).add_const (t • a))
      exact this
    have := extDeriv_insert_const (w := fun y => W (y + t • a)) hWd a
    rw [extDeriv_comp_add_const, fderiv_comp_add_right] at this
    exact this
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => fderiv ℝ W (x + t • a) a)
    (fun t ht => hpt t (by simpa using ht))]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => W (x + t • a)) (f' := fun t => fderiv ℝ W (x + t • a) a) (a := (0:ℝ)) (b := 1)
    (fun t ht => by
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
      have hd := (hdiff _ (hUa x hx t ht')).hasFDerivAt
      have hp : HasDerivAt (fun t : ℝ => x + t • a) a t := by
        simpa using ((hasDerivAt_id t).smul_const a).const_add x
      have := hd.comp_hasDerivAt t hp
      exact this)
    (by
      refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
      have hc := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hW).2.continuousOn.comp
          (by fun_prop : Continuous fun t : ℝ => x + t • a).continuousOn
          (fun t ht => hUa x hx t ht)
      exact (ContinuousLinearMap.apply ℝ (E [⋀^Fin (k + 1)]→L[ℝ] F) a).continuous.comp_continuousOn hc)
  simpa using hftc

end General

end TernaryPeriodPolynomials.Argument.EisensteinClass
