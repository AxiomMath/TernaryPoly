module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamContraction
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

@[expose] public section

noncomputable section
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
namespace TernaryPoly.SmoothLocalDeRham
open Set Filter MeasureTheory ContinuousAlternatingMap
open scoped ContDiff Topology

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

def radialPoint (a : E) (p : E × ℝ) : E := a + p.2 • (p.1 - a)

theorem radialPoint_smooth (a : E) : ContDiff ℝ ∞ (radialPoint a) := by
  unfold radialPoint
  fun_prop

def radialDomain (a : E) (s : Set E) : Set (E × ℝ) := radialPoint a ⁻¹' s

theorem radialDomain_isOpen {s : Set E} (hs : IsOpen s) (a : E) : IsOpen (radialDomain a s) :=
  hs.preimage (radialPoint_smooth a).continuous

/-- The weighted radial integrand that lowers the form degree by one. -/
def radialIntegrand (a : E) (w : RawForm E F (n + 1)) (p : E × ℝ) : E [⋀^Fin n]→L[ℝ] F :=
  p.2 ^ n • (w (radialPoint a p)).curryLeft (p.1 - a)

theorem radialIntegrand_smooth {s : Set E} (a : E) {w : RawForm E F (n + 1)}
    (hw : ContDiffOn ℝ ∞ w s) : ContDiffOn ℝ ∞ (radialIntegrand a w) (radialDomain a s) := by
  let L : (E [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) :=
    (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n)).toContinuousLinearMap
  have hL : ContDiff ℝ ∞ L := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := E [⋀^Fin (n + 1)]→L[ℝ] F) (F := E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) L
  have hc : ContDiffOn ℝ ∞ (fun p => (w (radialPoint a p)).curryLeft) (radialDomain a s) := by
    exact hL.comp_contDiffOn (hw.comp (radialPoint_smooth a).contDiffOn (fun _ hp => hp))
  exact (contDiffOn_snd.pow n).smul (hc.clm_apply (contDiffOn_fst.sub contDiffOn_const))

/-- The actual all-degree radial homotopy operator on ambient representatives. -/
def radialHomotopy (a : E) (w : RawForm E F (n + 1)) : RawForm E F n :=
  fun x => ∫ t in (0 : ℝ)..1, radialIntegrand a w (x, t)

variable [FiniteDimensional ℝ E]

theorem radialHomotopy_smooth {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) :
    ContDiffOn ℝ ∞ (radialHomotopy a w) (sliceDomain (radialDomain a s)) :=
  parameterIntegral_smooth (radialDomain_isOpen hs a) (radialIntegrand_smooth a hw)

theorem radialHomotopy_hasFDerivAt {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E}
    (hx : x ∈ sliceDomain (radialDomain a s)) :
    HasFDerivAt (radialHomotopy a w)
      (∫ t in (0 : ℝ)..1, parameterDerivative (radialIntegrand a w) (x, t)) x :=
  hasFDerivAt_parameterIntegral (radialDomain_isOpen hs a) (radialIntegrand_smooth a hw) hx

end TernaryPoly.SmoothLocalDeRham
