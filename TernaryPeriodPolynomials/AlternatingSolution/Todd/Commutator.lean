module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Scaling
public import Mathlib.Tactic.LinearCombination

@[expose] public section

open Polynomial

noncomputable section
namespace TernaryPoly

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The commutator of the Todd operator with multiplication by the polynomial variable. -/
def toddXComm (u : R) (p : Polynomial R) : Polynomial R :=
  todd u (X * p) - X * todd u p

@[simp] theorem toddXComm_add (u : R) (p q : Polynomial R) :
    toddXComm u (p + q) = toddXComm u p + toddXComm u q := by
  simp only [toddXComm, mul_add, map_add]
  abel

@[simp] theorem toddXComm_sub (u : R) (p q : Polynomial R) :
    toddXComm u (p - q) = toddXComm u p - toddXComm u q := by
  simp only [toddXComm, mul_sub, map_sub]
  abel

@[simp] theorem toddXComm_smul (u r : R) (p : Polynomial R) :
    toddXComm u (r • p) = r • toddXComm u p := by
  simp only [toddXComm, mul_smul_comm, map_smul, smul_sub]

/-- At zero parameter the finite Todd operator is the identity. -/
@[simp] theorem todd_zero_parameter (p : Polynomial R) : todd (0 : R) p = p := by
  classical
  rw [todd_apply, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- The finite-difference identity commuted with multiplication by `X`. -/
theorem toddXComm_difference (u : R) (p : Polynomial R) :
    toddXComm u (taylor (-u) p - p) = u • (taylor (-u) (todd u p) - p) := by
  have ht : taylor (-u) (X * p) = X * taylor (-u) p + (-u) • taylor (-u) p := by
    simp only [taylor_mul, taylor_X, add_mul, smul_eq_C_mul]
  have hx := todd_difference u (X * p)
  rw [ht, map_sub, map_add, map_smul, derivative_mul, derivative_X, one_mul,
    smul_add] at hx
  have hd := todd_difference u p
  rw [map_sub] at hd
  rw [toddXComm, mul_sub, map_sub, map_sub, taylor_todd]
  simp only [smul_eq_C_mul, map_neg] at hx hd ⊢
  linear_combination hx - X * hd

variable [IsDomain R]

/-- The Todd commutator on a derivative, expressed entirely by finite operators. -/
theorem toddXComm_derivative (u : R) (p : Polynomial R) :
    toddXComm u (derivative p) =
      todd u p - taylor (-u) (todd u (todd u p)) := by
  by_cases hu : u = 0
  · subst u
    simp [toddXComm]
  · have hd : taylor (-u) (todd u p) - todd u p = (-u) • derivative p := by
      rw [taylor_todd, ← map_sub, todd_difference]
    have h := toddXComm_difference u (todd u p)
    rw [hd, toddXComm_smul] at h
    have he : u • toddXComm u (derivative p) =
        u • (todd u p - taylor (-u) (todd u (todd u p))) := by
      simp only [smul_sub, neg_smul] at h ⊢
      exact neg_injective (by simpa only [neg_sub] using h)
    simp only [smul_eq_C_mul] at he
    exact mul_left_cancel₀ (by simpa using hu : C u ≠ 0) he

/-- The all-degree scalar first-jet identity, expressed by canonical finite Todd operators. -/
theorem todd_scalar_firstJet (u : R) (p : Polynomial R) :
    -todd u p + (algebraMap ℚ R (1 / 3)) •
        toddXComm (3*u) (derivative (p + taylor (-u) p + taylor (-(2*u)) p)) +
      (-u) • derivative (taylor (-(2*u)) (todd (3*u) p)) =
      -taylor (-(2*u)) (todd (3*u) (todd u p)) := by
  have hthird : algebraMap ℚ R (1 / 3) * (3 : R) = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (1 / 3 : ℚ) * 3 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hcomm : (algebraMap ℚ R (1 / 3)) •
      toddXComm (3*u) (derivative (p + taylor (-u) p + taylor (-(2*u)) p)) =
      todd u p - taylor (-(3*u)) (todd (3*u) (todd u p)) := by
    rw [toddXComm_derivative, todd_three_mul, map_smul, map_smul]
    simp only [smul_sub, smul_smul, hthird, one_smul]
  have hstep : (-u) • derivative (taylor (-(2*u)) (todd (3*u) p)) =
      taylor (-(3*u)) (todd (3*u) (todd u p)) -
        taylor (-(2*u)) (todd (3*u) (todd u p)) := by
    calc
      _ = taylor (-(2*u)) ((-u) • derivative (todd (3*u) p)) := by
        rw [map_smul, derivative_taylor]
      _ = taylor (-(2*u)) (todd u (taylor (-u) (todd (3*u) p) - todd (3*u) p)) := by
        rw [todd_difference]
      _ = _ := by
        rw [map_sub, ← taylor_todd, map_sub, taylor_taylor]
        simp only [todd_commute u (3*u)]
        rw [show -(2*u) + -u = -(3*u) by ring]
  rw [hcomm, hstep]
  abel

end TernaryPoly
