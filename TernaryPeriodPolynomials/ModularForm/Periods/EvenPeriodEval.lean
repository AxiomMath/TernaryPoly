module

public import TernaryPeriodPolynomials.ModularForm.Period.Basic
public import TernaryPeriodPolynomials.ModularForm.Period.Map
public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Symmetry
public import TernaryPeriodPolynomials.ModularForm.Eichler.Relations
public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Projection
public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Basic

@[expose] public section



/-!
# Eval-level even-period identities

The even-filtered Mellin period polynomial `evenPeriod f` (the symmetrization of `period f` under
negating the first variable) and the eval-level unfoldings of the `S`-action, the two axis-parity
facts, Manin's relation, and the three-term relation. These are exactly the eval-level shapes of
`TernaryPoly.Paper.PeriodRelations.two_term`/`three_term` for `evenPeriod f`; the lift to the
literal polynomial statements is in `EvenPeriodRelations.lean`.
-/

noncomputable section
open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CuspForms

open TernaryPoly.BinaryCuspPeriod

/-- The even-filtered Mellin period polynomial: the symmetrization of `period f` under
negating the first variable. Dual to `oddPeriod`. -/
def evenPeriod {d : ℕ} (f : Forms d) : MvPolynomial (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (period f + bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ) (period f))

theorem two_mul_eval_evenPeriod {d : ℕ} (f : Forms d) (x y : ℂ) :
    2 * eval ![x, y] (evenPeriod f) = eval ![x, y] (period f) + eval ![-x, y] (period f) := by
  rw [evenPeriod, MvPolynomial.smul_eq_C_mul, eval_mul, eval_C, eval_add, eval_bind_binary]
  simp only [eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, eval_neg]
  field_simp

theorem eval_evenPeriod_antisymm {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    2 * eval ![x, y] (evenPeriod f) = eval ![x, y] (period f) - eval ![y, x] (period f) := by
  rw [two_mul_eval_evenPeriod, eval_period_S hd f y x]
  ring

theorem eval_evenPeriod_S {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![-y, x] (evenPeriod f) = -eval ![x, y] (evenPeriod f) := by
  have h1 := eval_evenPeriod_antisymm hd f x y
  have h2 := eval_evenPeriod_antisymm hd f (-y) x
  have hs1 := eval_period_S hd f x y
  have hs2 := eval_period_S hd f (-y) (-x)
  rw [show (-(-x) : ℂ) = x by ring] at hs2
  have hnn := eval_period_neg_neg hd f y x
  linear_combination (h1 + h2 + hs1 - hs2 + hnn) / 2

theorem eval_evenPeriod_even_first {d : ℕ} (f : Forms d) (x y : ℂ) :
    eval ![-x, y] (evenPeriod f) = eval ![x, y] (evenPeriod f) := by
  have h1 := two_mul_eval_evenPeriod f x y
  have h2 := two_mul_eval_evenPeriod f (-x) y
  rw [neg_neg] at h2
  linear_combination (h2 - h1) / 2

theorem eval_evenPeriod_even_second {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x, -y] (evenPeriod f) = eval ![x, y] (evenPeriod f) := by
  have h1 := eval_evenPeriod_antisymm hd f x y
  have h2 := eval_evenPeriod_antisymm hd f x (-y)
  have hs1 := eval_period_S hd f x y
  have hs2 := eval_period_S hd f (-y) (-x)
  rw [show (-(-x) : ℂ) = x by ring] at hs2
  have hnn := eval_period_neg_neg hd f y x
  linear_combination (h2 - h1 - hs1 + hs2 - hnn) / 2

theorem eval_evenPeriod_manin {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x, y] (evenPeriod f) - eval ![x - y, y] (evenPeriod f) -
      eval ![x, y - x] (evenPeriod f) = 0 := by
  have h1 := eval_period_manin hd f x y
  have h2 := eval_period_manin hd f y x
  have h3 := eval_evenPeriod_antisymm hd f x y
  have h4 := eval_evenPeriod_antisymm hd f (x - y) y
  have h5 := eval_evenPeriod_antisymm hd f x (y - x)
  linear_combination (h1 - h2 + h3 - h4 - h5) / 2

theorem eval_evenPeriod_threeTerm {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x, y] (evenPeriod f) + eval ![-y, x - y] (evenPeriod f) +
      eval ![y - x, -x] (evenPeriod f) = 0 := by
  have hS1 := eval_evenPeriod_S hd f (x - y) y
  have hS2 := eval_evenPeriod_S hd f (-x) (x - y)
  rw [show -(x - y) = y - x by ring] at hS2
  have hM := eval_evenPeriod_manin hd f x y
  have hE2 := eval_evenPeriod_even_second hd f (-x) (y - x)
  rw [show -(y - x) = x - y by ring] at hE2
  have hE1 := eval_evenPeriod_even_first f x (y - x)
  linear_combination hS1 + hS2 + hM - hE2 - hE1

/-- The boundary-reflection fact: at the two axis points `(1,0)` and `(0,1)`, `evenPeriod f` takes
opposite values. Derived from `eval_evenPeriod_S` at `(0,-1)` and `eval_evenPeriod_even_second` at
`(0,1)`, with no further primitive input. -/
theorem eval_evenPeriod_boundary_reflection {d : ℕ} (hd : Even d) (f : Forms d) :
    eval ![1, 0] (evenPeriod f) = -eval ![0, 1] (evenPeriod f) := by
  have h1 := eval_evenPeriod_S hd f 0 (-1)
  have h2 := eval_evenPeriod_even_second hd f 0 1
  simp only [neg_neg] at h1
  linear_combination h1 - h2

end TernaryPeriodPolynomials.Argument.CuspForms
