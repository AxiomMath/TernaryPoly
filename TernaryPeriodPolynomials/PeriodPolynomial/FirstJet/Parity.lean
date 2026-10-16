module

public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Constant

@[expose] public section


open Polynomial
noncomputable section
namespace TernaryPoly
variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
/-- The two differential equations force oddness of the boundary first partial sum. -/
theorem firstJet_partial_odd (y : R) (p h H : Polynomial R)
    (hp : derivative p = -H)
    (hh : derivative h = H + H.comp (Polynomial.C y-Polynomial.X))
    (hd : derivative (taylor (-y) p-p-h) = 0) :
    H.comp (-Polynomial.X) = -H := by
  have hsum : taylor (-y) H + H.comp (Polynomial.C y-Polynomial.X) = 0 := by
    rw [map_sub, map_sub, derivative_taylor, hp, hh, map_neg] at hd
    apply neg_eq_zero.mp
    calc
      -(taylor (-y) H + H.comp (Polynomial.C y-Polynomial.X)) =
        -taylor (-y) H - -H - (H + H.comp (Polynomial.C y-Polynomial.X)) := by abel
      _ = 0 := hd
  have ht := congrArg (taylor y) hsum
  rw [map_add, map_zero, taylor_taylor, add_neg_cancel, taylor_zero] at ht
  have he : taylor y (H.comp (Polynomial.C y-Polynomial.X)) = H.comp (-Polynomial.X) := by
    rw [taylor_apply, comp_assoc]
    congr 1
    simp only [sub_comp, C_comp, X_comp]
    abel
  rw [he] at ht
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using ht)

/-- A primitive of an odd polynomial is even, regardless of its constant term. -/
theorem polynomial_even_of_derivative_odd (p : Polynomial R)
    (hp : (derivative p).comp (-Polynomial.X) = -derivative p) :
    p.comp (-Polynomial.X) = p := by
  apply polynomial_eq_of_derivative_eq_of_coeff_zero_eq
  · simp [derivative_comp, hp]
  · simp [coeff_zero_eq_eval_zero, eval_comp]

/-- The first-jet primitive has even parity in its integration variable. -/
theorem firstJet_primitive_even (y : R) (p h H : Polynomial R)
    (hp : derivative p = -H)
    (hh : derivative h = H + H.comp (Polynomial.C y-Polynomial.X))
    (hd : derivative (taylor (-y) p-p-h) = 0) :
    p.comp (-Polynomial.X) = p := by
  apply polynomial_even_of_derivative_odd
  rw [hp, neg_comp, firstJet_partial_odd y p h H hp hh hd]

end TernaryPoly
