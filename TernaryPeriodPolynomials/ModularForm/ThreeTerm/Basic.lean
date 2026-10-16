module

public import TernaryPeriodPolynomials.ModularForm.Eichler.Relations
public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Projection
public import TernaryPeriodPolynomials.ModularForm.Period.Map

@[expose] public section


noncomputable section
open MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- The S relation twice gives simultaneous evenness of the actual full period. -/
theorem eval_period_neg_neg {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![-x,-y] (period f) = eval ![x,y] (period f) := by
  have h1 := eval_period_S hd f x y
  have h2 := eval_period_S hd f (-y) x
  linear_combination h2 - h1

/-- Standard full Manin equation in the literal (zY-X)^d convention. -/
theorem eval_period_manin {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x,y] (period f) - eval ![x-y,y] (period f) - eval ![x,y-x] (period f) = 0 := by
  have h := eval_period_ST hd f (x-y) y
  rw [show -(x-y)-y = -x by ring] at h
  have hn := eval_period_neg_neg hd f x (y-x)
  rw [show -(y-x) = x-y by ring] at hn
  have hs := eval_period_S hd f y (-x)
  simp only [neg_neg] at hs
  linear_combination -h + hn + hs

/-- The actual odd projection is exactly the symmetric part of the full period. -/
theorem two_mul_eval_oddPeriod_symm {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    2 * eval ![x,y] (oddPeriod f) = eval ![x,y] (period f) + eval ![y,x] (period f) := by
  rw [two_mul_eval_oddPeriod, eval_period_S hd f y x, sub_neg_eq_add]

/-- Symmetrizing the two actual full Manin equations preserves the full Manin equation. -/
theorem eval_oddPeriod_manin {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x,y] (oddPeriod f) - eval ![x-y,y] (oddPeriod f) -
      eval ![x,y-x] (oddPeriod f) = 0 := by
  have h1 := eval_period_manin hd f x y
  have h2 := eval_period_manin hd f y x
  have h3 := two_mul_eval_oddPeriod_symm hd f x y
  have h4 := two_mul_eval_oddPeriod_symm hd f (x-y) y
  have h5 := two_mul_eval_oddPeriod_symm hd f x (y-x)
  linear_combination (h1+h2+h3-h4-h5)/2

/-- The actual odd Mellin period satisfies the requested three-term equation at every evaluation. -/
theorem eval_oddPeriod_threeTerm {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x,y] (oddPeriod f) - eval ![x-y,y] (oddPeriod f) +
      eval ![x,x-y] (oddPeriod f) = 0 := by
  have h := eval_oddPeriod_manin hd f x y
  have hn := eval_oddPeriod_neg_second hd f x (x-y)
  rw [show -(x-y) = y-x by ring] at hn
  linear_combination h + hn

/-- Closure of the actual three-term defect for every full-level cusp form of even degree. -/
theorem threeTermDefect_eq_zero {d : ℕ} (hd : Even d) (f : Forms d) :
    threeTermDefect d f = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
  rw [threeTermDefect_apply, eval_add, eval_sub, eval_bind_binary, eval_bind_binary, map_zero]
  simp only [eval_sub, eval_X]
  rw [hv]
  exact eval_oddPeriod_threeTerm hd f (v 0) (v 1)

end TernaryPoly.BinaryCuspPeriod
