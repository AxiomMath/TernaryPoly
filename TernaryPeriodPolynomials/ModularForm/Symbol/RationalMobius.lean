module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Cocycle
public import TernaryPeriodPolynomials.ModularForm.Symbol.Shift
public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Geometry

@[expose] public section


noncomputable section
open Complex Matrix Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryCuspHeckeEndomorphism

/-- The actual rational matrix action, composed with the upper-half-plane coercion. -/
def rationalMobius (g : GL2) (z : ℂ) : ℂ := ((realify g • ofComplex z : ℍ) : ℂ)

@[simp] theorem realify_det (g : GL2) :
    (realify g).det.val = (g.det.val : ℝ) := by
  change (g.val.map (Rat.castHom ℝ)).det = (g.val.det : ℝ)
  exact (RingHom.map_det (Rat.castHom ℝ) g.val).symm

theorem rationalMobius_im_pos (g : GL2) (z : ℂ) : 0 < (rationalMobius g z).im :=
  (realify g • ofComplex z).im_pos

theorem rationalMobius_mul (g h : GL2) (z : ℂ) :
    rationalMobius (g*h) z = rationalMobius g (rationalMobius h z) := by
  simp only [rationalMobius, map_mul, mul_smul, ofComplex_apply]

theorem rationalMobius_fraction (g : GL2) (hg : 0 < g.det.val) {z : ℂ} (hz : 0 < z.im) :
    rationalMobius g z = ((g 0 0 : ℂ)*z+(g 0 1 : ℂ))/((g 1 0 : ℂ)*z+(g 1 1 : ℂ)) := by
  have hr : 0 < (realify g).det.val := by rw [realify_det]; exact_mod_cast hg
  rw [rationalMobius, coe_smul_of_det_pos hr, ofComplex_apply_of_im_pos hz]
  simp only [num, denom, realify_apply]
  push_cast
  rfl

@[simp] theorem slRational_det (g : SL2) : (slRational g).det.val = 1 := by
  change (g.val.map (Int.castRingHom ℚ)).det = 1
  calc
    _ = (g.val.det : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) g.val).symm
    _ = 1 := by rw [g.det_coe]; rfl

theorem rationalMobius_slRational (g : SL2) {z : ℂ} (hz : 0 < z.im) :
    rationalMobius (slRational g) z = slMobius g z := by
  rw [rationalMobius_fraction _ (by rw [slRational_det]; norm_num) hz]
  change ((((g 0 0 : ℤ) : ℚ) : ℂ)*z+(((g 0 1 : ℤ) : ℚ) : ℂ)) /
    ((((g 1 0 : ℤ) : ℚ) : ℂ)*z+(((g 1 1 : ℤ) : ℚ) : ℂ)) = _
  norm_cast

/-- Upper-triangular positive rational charts approach infinity along a fixed horizontal shift
and a positive rescaling of the imaginary axis. -/
theorem rationalMobius_upper_axis (g : GL2) (hg : 0 < g.det.val) (hc : g 1 0 = 0)
    {t : ℝ} (ht : 0 < t) :
    rationalMobius g (I*t) = ((g 0 1 / g 1 1 : ℚ) : ℂ) +
      I * (((g 0 0 / g 1 1 : ℚ) : ℝ)*t) := by
  rw [rationalMobius_fraction g hg (by simpa using ht), hc]
  push_cast
  simp only [zero_mul, zero_add]
  ring

theorem upper_ratio_pos (g : GL2) (hg : 0 < g.det.val) (hc : g 1 0 = 0) :
    0 < ((g 0 0 / g 1 1 : ℚ) : ℝ) := by
  have h := rationalMobius_im_pos g (I*(1 : ℝ))
  rw [rationalMobius_upper_axis g hg hc (by norm_num)] at h
  simpa using h

/-- Every positive upper-triangular rational approach has zero normalized primitive limit. -/
theorem eichlerIntegral_upper_axis_tendsto {d : ℕ} (f : Forms d) (v : Coordinates)
    (g : GL2) (hg : 0 < g.det.val) (hc : g 1 0 = 0) :
    Tendsto (fun t : ℝ => eichlerIntegral f (v 0) (v 1) (rationalMobius g (I*t))) atTop (𝓝 0) := by
  have hscale : Tendsto (fun t : ℝ => ((g 0 0/g 1 1 : ℚ) : ℝ)*t) atTop atTop :=
    Tendsto.const_mul_atTop (upper_ratio_pos g hg hc) tendsto_id
  have h := (eichlerIntegral_realShift_axis_tendsto_infty f (v 0) (v 1)
    ((g 0 1/g 1 1 : ℚ) : ℝ)).comp hscale
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [rationalMobius_upper_axis g hg hc ht]
  simp

end TernaryPoly.BinaryCuspSymbol
