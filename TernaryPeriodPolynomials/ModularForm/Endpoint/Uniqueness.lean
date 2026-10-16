module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Primitive

@[expose] public section


noncomputable section
open Complex Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspPeriod

/-- Equal holomorphic differentials on the connected upper half plane differ by the difference
of their actual vertical limits at infinity. -/
theorem primitive_difference_from_axis_limits (F G D : ℂ → ℂ) (a b : ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (D z) z)
    (hG : ∀ z : ℂ, 0 < z.im → HasDerivAt G (D z) z)
    (hFa : Tendsto (fun t : ℝ => F (I*t)) atTop (𝓝 a))
    (hGb : Tendsto (fun t : ℝ => G (I*t)) atTop (𝓝 b))
    {z : ℂ} (hz : 0 < z.im) : F z = G z + (a-b) := by
  obtain ⟨c, he⟩ := isOpen_upperHalfPlaneSet.exists_eq_add_of_deriv_eq
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hG w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hF w hw).deriv.trans (hG w hw).deriv.symm)
  have hevent : (fun t : ℝ => F (I*t)) =ᶠ[atTop] (fun t : ℝ => G (I*t)+c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact he (by simpa using ht)
  have hc : a = b+c := tendsto_nhds_unique hFa ((hGb.add_const c).congr' hevent.symm)
  have hcz : c = a-b := by linear_combination -hc
  simpa [hcz] using he hz

/-- Actual inversion of the vertical ray approaches the zero cusp. -/
theorem eichlerIntegral_inv_axis_tendsto_infty {d : ℕ} (f : Forms d) (x y : ℂ) :
    Tendsto (fun t : ℝ => eichlerIntegral f x y (-1/(I*t))) atTop
      (𝓝 (-MvPolynomial.eval ![x,y] (period f))) := by
  have h := (eichlerIntegral_axis_tendsto_zero f x y).comp tendsto_inv_atTop_nhdsGT_zero
  apply h.congr
  intro t
  change eichlerIntegral f x y (I*((t⁻¹ : ℝ) : ℂ)) = eichlerIntegral f x y (-1/(I*t))
  congr 1
  simp [div_eq_mul_inv, inv_I, mul_comm]

end TernaryPoly.BinaryCuspPeriod
