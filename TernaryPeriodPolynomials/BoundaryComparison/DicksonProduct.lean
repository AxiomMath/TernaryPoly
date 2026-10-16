module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import Mathlib
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# The Dickson product identity (`mf:eq:product`)

Formalized by Claude Sonnet 5.5.

> Put `a = x+y+z`, `b = xy+xz+yz`, `c = xyz`, `c₊ = ab + c` ... Define
> `d₄ = a⁴+b²+ac`, `d₆ = a²b²+a³c+abc+c²`, `d₇ = ac(ab+c)`. These are the Dickson invariants of
> degrees four, six, and seven. Their invariance under invertible linear substitutions over `k`
> follows from the product identity
> `∏_{(v₁,v₂,v₃) ∈ k³} (T + v₁x + v₂y + v₃z) = T⁸ + d₄T⁴ + d₆T² + d₇T`.

Here `k = 𝔽₂`; the identity is an identity in `k[x,y,z][T]`, written with `Polynomial` over the
project's `TernaryPoly.CharTwoNorm.Poly`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.DicksonProduct

theorem prod_pi_fin_three {M : Type*} [CommMonoid M] (f : (Fin 3 → ZMod 2) → M) :
    ∏ v, f v = f ![0, 0, 0] * f ![0, 0, 1] * f ![0, 1, 0] * f ![0, 1, 1] *
      f ![1, 0, 0] * f ![1, 0, 1] * f ![1, 1, 0] * f ![1, 1, 1] := by
  have h : (Finset.univ : Finset (Fin 3 → ZMod 2)) =
      {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0],
        ![1, 1, 1]} := by decide +kernel
  rw [h]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_pair (by decide)]
  simp only [mul_assoc]

/-- **The Dickson product identity** (`mf:eq:product`):
`∏_{v ∈ 𝔽₂³} (T + v₁x + v₂y + v₃z) = T⁸ + d₄T⁴ + d₆T² + d₇T` in `𝔽₂[x,y,z][T]`. -/
theorem dickson_product :
    ∏ v : Fin 3 → ZMod 2,
        (Polynomial.X + Polynomial.C (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) :
          Polynomial Poly) =
      Polynomial.X ^ 8 + Polynomial.C d4 * Polynomial.X ^ 4 + Polynomial.C d6 * Polynomial.X ^ 2 +
        Polynomial.C d7 * Polynomial.X := by
  rw [prod_pi_fin_three]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_zero, map_one, zero_mul, one_mul, zero_add, add_zero,
    d4, d6, d7, a, b, c, cplus, map_add, map_mul, map_pow]
  have h2 : (2 : Polynomial Poly) = 0 := CharTwo.two_eq_zero
  set x : Polynomial Poly := Polynomial.C (MvPolynomial.X 0) with hx
  set y : Polynomial Poly := Polynomial.C (MvPolynomial.X 1) with hy
  set z : Polynomial Poly := Polynomial.C (MvPolynomial.X 2) with hz
  set T : Polynomial Poly := Polynomial.X with hT
  linear_combination (2*z*T^7 + 3*z^2*T^6 + 2*z^3*T^5 + 2*y*T^7 + 7*y*z*T^6 + 9*y*z^2*T^5 + 3*y*z^3*T^4 + y*z^4*T^3 + 3*y^2*T^6 + 9*y^2*z*T^5 + 6*y^2*z^2*T^4 + 4*y^2*z^3*T^3 + 2*y^3*T^5 + 3*y^3*z*T^4 + 4*y^3*z^2*T^3 + y^4*z*T^3 + 2*x*T^7 + 7*x*z*T^6 + 9*x*z^2*T^5 + 3*x*z^3*T^4 + x*z^4*T^3 + 7*x*y*T^6 + 21*x*y*z*T^5 + 15*x*y*z^2*T^4 + 10*x*y*z^3*T^3 + 9*x*y^2*T^5 + 15*x*y^2*z*T^4 + 19*x*y^2*z^2*T^3 + 3*x*y^3*T^4 + 10*x*y^3*z*T^3 + x*y^4*T^3 + 3*x^2*T^6 + 9*x^2*z*T^5 + 6*x^2*z^2*T^4 + 4*x^2*z^3*T^3 + 9*x^2*y*T^5 + 15*x^2*y*z*T^4 + 19*x^2*y*z^2*T^3 + 6*x^2*y^2*T^4 + 19*x^2*y^2*z*T^3 - x^2*y^2*z^2*T^2 - x^2*y^2*z^3*T + 4*x^2*y^3*T^3 - x^2*y^3*z^2*T + 2*x^3*T^5 + 3*x^3*z*T^4 + 4*x^3*z^2*T^3 + 3*x^3*y*T^4 + 10*x^3*y*z*T^3 + 4*x^3*y^2*T^3 - x^3*y^2*z^2*T + x^4*z*T^3 + x^4*y*T^3) * h2

end TernaryPeriodPolynomials.Argument.Statements.DicksonProduct
