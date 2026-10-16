module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Mobius

@[expose] public section


noncomputable section
open Complex Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod

/-- The actual Eichler transformation constant, computed at the interior base point i. -/
def slConstant {d : ℕ} (f : Forms d) (g : SL2) (v : Coordinates) : ℂ :=
  eichlerIntegral f (v 0) (v 1) (slMobius g I) -
    eichlerIntegral f (slCoordinates g⁻¹ v 0) (slCoordinates g⁻¹ v 1) I

/-- Chain rule for the genuine Eichler integral and every integral special-linear matrix. -/
theorem eichlerIntegral_sl_hasDerivAt {d : ℕ} (f : Forms d) (g : SL2) (v : Coordinates)
    {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w => eichlerIntegral f (v 0) (v 1) (slMobius g w))
      (periodIntegrand f (slCoordinates g⁻¹ v 0) (slCoordinates g⁻¹ v 1) z) z := by
  have h := (eichlerIntegral_hasDerivAt f (v 0) (v 1) _ (slMobius_im_pos g hz)).comp z
    (slMobius_hasDerivAt g hz)
  simpa only [Function.comp_def, periodIntegrand_slMobius f g v hz] using! h

/-- Exact arbitrary SL2(Z) transformation, with an explicit actual constant rather than an
assumed cocycle or endpoint value. -/
theorem eichlerIntegral_sl {d : ℕ} (f : Forms d) (g : SL2) (v : Coordinates)
    {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral f (v 0) (v 1) (slMobius g z) =
      eichlerIntegral f (slCoordinates g⁻¹ v 0) (slCoordinates g⁻¹ v 1) z + slConstant f g v := by
  have hF (w : ℂ) (hw : 0 < w.im) := eichlerIntegral_sl_hasDerivAt f g v hw
  have hG (w : ℂ) (hw : 0 < w.im) :=
    (eichlerIntegral_hasDerivAt f (slCoordinates g⁻¹ v 0) (slCoordinates g⁻¹ v 1) w hw).add_const (slConstant f g v)
  apply isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq (convex_halfSpace_im_gt 0).isPreconnected
    (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hG w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hF w hw).deriv.trans (hG w hw).deriv.symm) (x := I) (by simp) _ hz
  unfold slConstant
  ring

/-- The actual limit at the rational cusp represented by g's first column. -/
theorem eichlerIntegral_sl_axis_tendsto {d : ℕ} (f : Forms d) (g : SL2) (v : Coordinates) :
    Tendsto (fun t : ℝ => eichlerIntegral f (v 0) (v 1) (slMobius g (I*t))) atTop
      (𝓝 (slConstant f g v)) := by
  have h := (eichlerIntegral_axis_tendsto_infty f (slCoordinates g⁻¹ v 0)
    (slCoordinates g⁻¹ v 1)).add_const (slConstant f g v)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (eichlerIntegral_sl f g v (by simpa using ht)).symm

end TernaryPoly.BinaryCuspSymbol
