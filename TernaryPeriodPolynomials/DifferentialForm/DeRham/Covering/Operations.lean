module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRham
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set ContinuousAlternatingMap SmoothLocalDeRham
open scoped ContDiff Topology

universe u
variable {D E F G X : Type u}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : ℕ}

/-- The genuine continuous linear operation on form coefficients. -/
def coefficientFormMap (L : F →L[ℝ] G) (n : ℕ) :
    (E [⋀^Fin n]→L[ℝ] F) →L[ℝ] (E [⋀^Fin n]→L[ℝ] G) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E F G (Fin n) L

@[simp] theorem coefficientFormMap_apply (L : F →L[ℝ] G) (w : E [⋀^Fin n]→L[ℝ] F) :
    coefficientFormMap L n w = L.compContinuousAlternatingMap w := rfl

def coefficientRaw (L : F →L[ℝ] G) (w : RawForm E F n) : RawForm E G n :=
  fun x => coefficientFormMap L n (w x)

theorem coefficientRaw_smooth {s : Set E} (L : F →L[ℝ] G)
    {w : RawForm E F n} (hw : ContDiffOn ℝ ∞ w s) :
    ContDiffOn ℝ ∞ (coefficientRaw L w) s := by
  exact (coefficientFormMap (E := E) L n).contDiff.comp_contDiffOn hw

theorem coefficient_alternatize (L : F →L[ℝ] G)
    (h : E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) :
    alternatizeUncurryFin ((coefficientFormMap L n).comp h) =
      coefficientFormMap L (n + 1) (alternatizeUncurryFin h) := by
  ext v
  simp [alternatizeUncurryFin_apply, coefficientFormMap]

/-- Exterior differentiation commutes with every continuous linear coefficient map. -/
theorem extDeriv_coefficientRaw (L : F →L[ℝ] G) {w : RawForm E F n} {x : E}
    (hw : DifferentiableAt ℝ w x) :
    extDeriv (coefficientRaw L w) x = coefficientFormMap L (n + 1) (extDeriv w x) := by
  have hd : HasFDerivAt (coefficientRaw L w) ((coefficientFormMap L n).comp (fderiv ℝ w x)) x := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (g := coefficientFormMap L n) (f := w) x
      (coefficientFormMap L n).hasFDerivAt hw.hasFDerivAt
  unfold extDeriv
  rw [hd.fderiv, coefficient_alternatize]

/-- Recover a form from its first-slot currying, with Mathlib's exact normalization. -/
theorem recover_curryLeft (w : E [⋀^Fin (n + 1)]→L[ℝ] F) :
    ((n + 1 : ℕ) : ℝ)⁻¹ • alternatizeUncurryFin w.curryLeft = w := by
  rw [alternatizeUncurryFin_curryLeft, ← Nat.cast_smul_eq_nsmul ℝ]
  exact inv_smul_smul₀ (by positivity) w

/-- Smoothness can be detected after currying the first alternating argument. -/
theorem smooth_of_curryLeft {s : Set X} {w : X → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hw : ContDiffOn ℝ ∞ (fun x => (w x).curryLeft) s) : ContDiffOn ℝ ∞ w s := by
  have h := ((alternatizeUncurryFinCLM ℝ E F (n := n)).contDiff.comp_contDiffOn hw).const_smul
    (((n + 1 : ℕ) : ℝ)⁻¹)
  exact h.congr (fun x _ => (recover_curryLeft (w x)).symm)

/-- Pullback of a varying alternating map along a varying linear map is smooth. -/
theorem smooth_compContinuousLinearMap [FiniteDimensional ℝ D] (n : ℕ)
    {s : Set X} {w : X → E [⋀^Fin n]→L[ℝ] F} {B : X → D →L[ℝ] E}
    (hw : ContDiffOn ℝ ∞ w s) (hB : ContDiffOn ℝ ∞ B s) :
    ContDiffOn ℝ ∞ (fun x => (w x).compContinuousLinearMap (B x)) s := by
  induction n with
  | zero =>
    let Z := (constOfIsEmptyLIE ℝ D F (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap
    let V := (constOfIsEmptyLIE ℝ E F (Fin 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have h : ContDiffOn ℝ ∞ (fun x => Z (V (w x))) s :=
      Z.contDiff.comp_contDiffOn (V.contDiff.comp_contDiffOn hw)
    apply h.congr
    intro x hx
    ext v
    simp only [Z, V, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      constOfIsEmptyLIE_apply, constOfIsEmptyLIE_symm_apply, compContinuousLinearMap_apply, constOfIsEmpty_apply]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    apply smooth_of_curryLeft
    apply contDiffOn_clm_apply.mpr
    intro v
    have hc : ContDiffOn ℝ ∞ (fun x => (w x).curryLeft) s := by
      let L : (E [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) :=
        (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n)).toContinuousLinearMap
      have hL := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        (E := E [⋀^Fin (n + 1)]→L[ℝ] F) (F := E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) L
      exact hL.comp_contDiffOn hw
    have hv := ih (hc.clm_apply (hB.clm_apply (contDiffOn_const (c := v))))
    exact hv.congr (fun x _ => curryLeft_compContinuousLinearMap (w x) (B x) v)

/-- The actual differential-form pullback in ordinary coordinates. -/
def pullRaw (f : D → E) (w : RawForm E F n) : RawForm D F n :=
  fun x => (w (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem pullRaw_smooth [FiniteDimensional ℝ D] {s : Set D} {t : Set E}
    (hs : IsOpen s) {f : D → E} {w : RawForm E F n}
    (hf : ContDiffOn ℝ ∞ f s) (hw : ContDiffOn ℝ ∞ w t) (hft : MapsTo f s t) :
    ContDiffOn ℝ ∞ (pullRaw f w) s := by
  exact smooth_compContinuousLinearMap n (hw.comp hf hft)
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hf).2

/-- Pullback naturality preserves Mathlib's literal exterior derivative. -/
theorem extDeriv_pullRaw {f : D → E} {w : RawForm E F n} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hw : DifferentiableAt ℝ w (f x)) :
    extDeriv (pullRaw f w) x = pullRaw f (extDeriv w) x :=
  extDeriv_pullback hw hf (by simp)

end TernaryPoly.SmoothCoveringDeRham
