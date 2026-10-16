module

public import TernaryPeriodPolynomials.ModularForm.Eichler.Basic

@[expose] public section

noncomputable section
open Complex MvPolynomial Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspPeriod

/-- Simultaneous parameter negation fixes the actual even-degree differential. -/
theorem periodIntegrand_neg_neg {d : ℕ} (hd : Even d) (f : Forms d) (x y z : ℂ) :
    periodIntegrand f (-x) (-y) z = periodIntegrand f x y z := by
  unfold periodIntegrand
  rw [show z*(-y)-(-x) = -(z*y-x) by ring, hd.neg_pow]

/-- Simultaneous parameter negation fixes the normalized actual primitive in even degree. -/
theorem eichlerIntegral_neg_neg {d : ℕ} (hd : Even d) (f : Forms d) (x y z : ℂ)
    (hz : 0 < z.im) : eichlerIntegral f (-x) (-y) z = eichlerIntegral f x y z := by
  have hF (w : ℂ) (hw : 0 < w.im) :
      HasDerivAt (eichlerIntegral f (-x) (-y)) (periodIntegrand f x y w) w := by
    simpa only [periodIntegrand_neg_neg hd] using eichlerIntegral_hasDerivAt f (-x) (-y) w hw
  have h := primitive_difference_from_axis_limits _ _ _ 0 0 hF
    (eichlerIntegral_hasDerivAt f x y) (eichlerIntegral_axis_tendsto_infty f (-x) (-y))
    (eichlerIntegral_axis_tendsto_infty f x y) hz
  simpa using h

/-- The actual full period satisfies its S relation, from the actual S² cocycle. -/
theorem eval_period_S {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![-y,x] (period f) = -eval ![x,y] (period f) := by
  have h1 := eichlerIntegral_neg_inv hd f x y (z := I) (by simp)
  have h2 := eichlerIntegral_neg_inv hd f (-y) x (z := I) (by simp)
  simp only [neg_div, one_div, inv_I, neg_neg] at h1 h2
  rw [eichlerIntegral_neg_neg hd f x y I (by simp)] at h2
  linear_combination h1 + h2

/-- Literal action of ST on the upper half plane. -/
def stPoint (z : ℂ) : ℂ := -1/(z+1)

/-- ST preserves the actual analytic domain. -/
theorem stPoint_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (stPoint z).im :=
  neg_inv_im_pos (by simpa using hz)

/-- The genuine ST action has a length-three cycle through i. -/
theorem stPoint_cube_I : stPoint (stPoint (stPoint I)) = I := by
  norm_num [stPoint, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]

/-- Exact ST-transform of the actual primitive, obtained from the S and T identities. -/
theorem eichlerIntegral_ST {d : ℕ} (hd : Even d) (f : Forms d)
    (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral f x y (stPoint z) =
      eichlerIntegral f (-x-y) x z - eval ![x,y] (period f) := by
  rw [stPoint, eichlerIntegral_neg_inv hd f x y (by simpa using hz),
    eichlerIntegral_translate f (-y) x hz]
  congr 2
  ring

/-- The actual full Mellin period satisfies its order-three relation by the actual (ST)³ cycle. -/
theorem eval_period_ST {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x,y] (period f) + eval ![-x-y,x] (period f) +
      eval ![y,-x-y] (period f) = 0 := by
  have h1 := eichlerIntegral_ST hd f x y
    (stPoint_im_pos (stPoint_im_pos (by simp : 0 < I.im)))
  have h2 := eichlerIntegral_ST hd f (-x-y) x (stPoint_im_pos (by simp : 0 < I.im))
  have h3 := eichlerIntegral_ST hd f y (-x-y) (by simp : 0 < I.im)
  rw [stPoint_cube_I] at h1
  rw [show -(-x-y)-x = y by ring] at h2
  rw [show -y-(-x-y) = x by ring] at h3
  linear_combination h1 + h2 + h3

end TernaryPoly.BinaryCuspPeriod
