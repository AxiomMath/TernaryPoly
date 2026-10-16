module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Difference
public import TernaryPeriodPolynomials.Polynomial.Integral
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section


open Polynomial
noncomputable section
namespace TernaryPoly
variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsDomain R]

omit [Algebra ℚ R] [IsDomain R] in
/-- The three translates telescope to one translation by three steps. -/
theorem taylor_three_difference (u : R) (q : Polynomial R) :
    taylor (-u) (q + taylor (-u) q + taylor (-(2*u)) q) -
      (q + taylor (-u) q + taylor (-(2*u)) q) = taylor (-(3*u)) q - q := by
  have h2 : -u + -u = -(2*u) := by ring
  have h3 : -u + -(2*u) = -(3*u) := by ring
  rw [map_add, map_add, taylor_taylor, taylor_taylor, h2, h3]
  abel

/-- The distribution identity for three steps, as an equality of finite operators. -/
theorem todd_three_mul (u : R) (p : Polynomial R) :
    todd (3*u) (p + taylor (-u) p + taylor (-(2*u)) p) =
      (3:R) • todd u p := by
  by_cases hu : u = 0
  · subst u
    simp only [mul_zero, neg_zero, taylor_zero, map_add]
    simp only [show (3:R) = 1+1+1 by ring, add_smul, one_smul]
  · obtain ⟨q, rfl⟩ := polynomial_derivative_surjective p
    have h : (-u) • todd (3*u)
        (derivative q + taylor (-u) (derivative q) + taylor (-(2*u)) (derivative q)) =
        (-u) • ((3:R) • todd u (derivative q)) := by
      calc
        _ = todd (3*u) ((-u) • derivative (q + taylor (-u) q + taylor (-(2*u)) q)) := by
          simp only [map_smul, map_add, derivative_taylor]
        _ = todd (3*u) (todd u (taylor (-u)
            (q + taylor (-u) q + taylor (-(2*u)) q) -
            (q + taylor (-u) q + taylor (-(2*u)) q))) := by rw [todd_difference]
        _ = todd u (todd (3*u) (taylor (-(3*u)) q - q)) := by
          rw [taylor_three_difference, todd_commute]
        _ = (-(3*u)) • todd u (derivative q) := by rw [todd_difference, map_smul]
        _ = _ := by rw [smul_smul]; congr 1; ring
    simp only [smul_eq_C_mul] at h ⊢
    exact mul_left_cancel₀ (by simpa using hu : C (-u) ≠ 0) h

end TernaryPoly
