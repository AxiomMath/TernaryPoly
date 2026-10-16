module

public import TernaryPeriodPolynomials.ModularForm.Eichler.Differential
public import TernaryPeriodPolynomials.ModularForm.Endpoint.Uniqueness

@[expose] public section

noncomputable section
open Complex MvPolynomial Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspPeriod

/-- Exact T-transformation of the actual infinity-normalized Eichler integral. -/
theorem eichlerIntegral_translate {d : ℕ} (f : Forms d) (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral f x y (z+1) = eichlerIntegral f (x-y) y z := by
  have hF (w : ℂ) (hw : 0 < w.im) :
      HasDerivAt (fun u => eichlerIntegral f x y (u+1)) (periodIntegrand f (x-y) y w) w := by
    have h := (eichlerIntegral_hasDerivAt f x y (w+1) (by simpa using hw)).comp w
      ((hasDerivAt_id w).add_const 1)
    simpa only [Function.comp_def, id_eq, mul_one, periodIntegrand_translate] using! h
  have hlim : Tendsto (fun t : ℝ => eichlerIntegral f x y (I*t+1)) atTop (𝓝 0) := by
    simpa only [add_comm] using eichlerIntegral_shift_axis_tendsto_infty f x y
  have h := primitive_difference_from_axis_limits _ _ _ 0 0 hF
    (eichlerIntegral_hasDerivAt f (x-y) y) hlim
    (eichlerIntegral_axis_tendsto_infty f (x-y) y) hz
  simpa using h

/-- Exact S-transformation of the actual normalized Eichler integral; its constant is the
actual finite Mellin polynomial, identified by the proved vertical endpoint theorem. -/
theorem eichlerIntegral_neg_inv {d : ℕ} (hd : Even d) (f : Forms d)
    (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral f x y (-1/z) =
      eichlerIntegral f (-y) x z - eval ![x,y] (period f) := by
  have hF (w : ℂ) (hw : 0 < w.im) :
      HasDerivAt (fun u => eichlerIntegral f x y (-1/u)) (periodIntegrand f (-y) x w) w := by
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw
    have hS : HasDerivAt (fun u : ℂ => -1/u) (1/w^2) w := by
      simpa [one_div, neg_div] using! ((hasDerivAt_id w).inv hw0).neg
    have h := (eichlerIntegral_hasDerivAt f x y (-1/w) (neg_inv_im_pos hw)).comp w hS
    simpa only [Function.comp_def, periodIntegrand_neg_inv hd f x y hw] using! h
  have h := primitive_difference_from_axis_limits _ _ _ (-eval ![x,y] (period f)) 0 hF
    (eichlerIntegral_hasDerivAt f (-y) x) (eichlerIntegral_inv_axis_tendsto_infty f x y)
    (eichlerIntegral_axis_tendsto_infty f (-y) x) hz
  simpa [sub_eq_add_neg] using h

end TernaryPoly.BinaryCuspPeriod
