module

public import TernaryPeriodPolynomials.ModularForm.Symbol.RationalMobius

@[expose] public section


noncomputable section
open Complex Matrix Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod

/-- A determinant-one integral chart followed by any positive upper-triangular rational chart
has the same actual normalized cusp value. -/
theorem eichlerIntegral_sl_upper_axis_tendsto {d : ℕ} (f : Forms d) (v : Coordinates)
    (g : SL2) (h : GL2) (hh : 0 < h.det.val) (hc : h 1 0 = 0) :
    Tendsto (fun t : ℝ => eichlerIntegral f (v 0) (v 1)
      (rationalMobius (slRational g*h) (I*t))) atTop (𝓝 (slConstant f g v)) := by
  have ht := (eichlerIntegral_upper_axis_tendsto f (slCoordinates g⁻¹ v) h hh hc).add_const
    (slConstant f g v)
  simp only [zero_add] at ht
  convert ht using 1
  funext t
  rw [rationalMobius_mul, rationalMobius_slRational _ (rationalMobius_im_pos h _),
    eichlerIntegral_sl f g v (rationalMobius_im_pos h _)]

/-- The determinant of the chart comparison with an integral SL2 chart is unchanged. -/
theorem slRational_inv_mul_det (g : SL2) (h : GL2) :
    ((slRational g)⁻¹*h).det.val = h.det.val := by
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, slRational_det, inv_one, one_mul]

/-- The actual endpoint along any positive rational chart compatible with a chosen integral
chart. The algebraic lower-left-zero condition is the exact cusp-equality condition. -/
theorem eichlerIntegral_chart_tendsto {d : ℕ} (f : Forms d) (v : Coordinates)
    (g : SL2) (h : GL2) (hh : 0 < h.det.val) (hc : ((slRational g)⁻¹*h) 1 0 = 0) :
    Tendsto (fun t : ℝ => eichlerIntegral f (v 0) (v 1) (rationalMobius h (I*t)))
      atTop (𝓝 (slConstant f g v)) := by
  have ht := eichlerIntegral_sl_upper_axis_tendsto f v g ((slRational g)⁻¹*h)
    (by rwa [slRational_inv_mul_det]) hc
  simpa only [mul_inv_cancel_left] using ht

end TernaryPoly.BinaryCuspSymbol
