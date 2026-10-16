module

public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Primitive

@[expose] public section


noncomputable section
open Complex MeasureTheory
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- The actual complex line integral of the period differential along a finite straight segment. -/
def periodSegment {d : ℕ} (f : Forms d) (x y : ℂ) (a b : ℍ) : ℂ :=
  ∫ t : ℝ in 0..1,
    periodIntegrand f x y (AffineMap.lineMap (a : ℂ) (b : ℂ) t) * ((b : ℂ)-(a : ℂ))

/-- Every finite segment between upper-half-plane points stays in the holomorphy domain. -/
theorem segment_im_pos (a b : ℍ) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    0 < (AffineMap.lineMap (a : ℂ) (b : ℂ) t).im := by
  apply (convex_halfSpace_im_gt 0).lineMap_mem a.im_pos b.im_pos
  simpa using ht

/-- The finite segment integral is exactly the difference of values of any actual primitive. -/
theorem periodSegment_eq_primitive_sub {d : ℕ} (f : Forms d) (x y : ℂ)
    (F : ℂ → ℂ) (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodIntegrand f x y z) z)
    (a b : ℍ) : periodSegment f x y a b = F b - F a := by
  have hline : Continuous (fun t : ℝ => AffineMap.lineMap (a : ℂ) (b : ℂ) t) := by fun_prop
  have hc : ContinuousOn (fun t : ℝ =>
      periodIntegrand f x y (AffineMap.lineMap (a : ℂ) (b : ℂ) t) * ((b : ℂ)-(a : ℂ)))
      (Set.uIcc (0 : ℝ) 1) :=
    ((periodIntegrand_differentiableOn f x y).continuousOn.comp hline.continuousOn
      (fun t ht => segment_im_pos a b t ht)).mul continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => F (AffineMap.lineMap (a : ℂ) (b : ℂ) u))
        (periodIntegrand f x y (AffineMap.lineMap (a : ℂ) (b : ℂ) t) *
          ((b : ℂ)-(a : ℂ))) t := by
    have h := ((hF _ (segment_im_pos a b t ht)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := (a : ℂ)) (b := (b : ℂ)))
    simpa [Function.comp_def, mul_comm] using! h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [periodSegment] using he

/-- The actual finite triangular path identity, proved through the holomorphic primitive.
Passing its vertices to the cusps is deliberately not included in this finite statement. -/
theorem periodSegment_add {d : ℕ} (f : Forms d) (x y : ℂ) (a b c : ℍ) :
    periodSegment f x y a b + periodSegment f x y b c = periodSegment f x y a c := by
  obtain ⟨F, hF⟩ := exists_period_primitive f x y
  rw [periodSegment_eq_primitive_sub f x y F hF,
    periodSegment_eq_primitive_sub f x y F hF,
    periodSegment_eq_primitive_sub f x y F hF]
  ring

end TernaryPoly.BinaryCuspPeriod
