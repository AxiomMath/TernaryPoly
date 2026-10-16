module

public import TernaryPeriodPolynomials.Polynomial.Integral
public import TernaryPeriodPolynomials.Polynomial.TaylorHasse
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Elimination of the constant first-jet mode

The scalar defect is zero from its explicit derivative equations and endpoint
antisymmetry. This lemma does not assume any geometric or ternary comparison.
-/

open Polynomial

noncomputable section

namespace TernaryPoly

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Explicit first-jet equations force the scalar defect to vanish in every degree. -/
theorem firstJet_constant_eq_zero (y : R) (p h H : Polynomial R)
    (hp : derivative p = -H) (hp0 : p.coeff 0 = 0)
    (hh : derivative h = H + H.comp (Polynomial.C y - Polynomial.X))
    (heval : h.eval y = -h.eval 0)
    (hd : derivative (taylor (-y) p - p - h) = 0) :
    taylor (-y) p - p - h = 0 := by
  have hsum : taylor (-y) H + H.comp (Polynomial.C y - Polynomial.X) = 0 := by
    rw [map_sub, map_sub, derivative_taylor, hp, hh, map_neg] at hd
    apply neg_eq_zero.mp
    calc
      -(taylor (-y) H + H.comp (Polynomial.C y - Polynomial.X)) =
          -taylor (-y) H - -H - (H + H.comp (Polynomial.C y - Polynomial.X)) := by abel
      _ = 0 := hd
  have htranslate :
      taylor y (H.comp (Polynomial.C y - Polynomial.X)) = H.comp (-Polynomial.X) := by
    rw [taylor_apply, comp_assoc]
    congr 1
    simp only [sub_comp, C_comp, X_comp]
    abel
  have hodd : H.comp (-Polynomial.X) = -H := by
    have ht := congrArg (taylor y) hsum
    rw [map_add, map_zero, taylor_taylor, add_neg_cancel, taylor_zero, htranslate] at ht
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using ht)
  have hpEven : p.comp (-Polynomial.X) = p := by
    apply polynomial_eq_of_derivative_eq_of_coeff_zero_eq
    · simp [derivative_comp, hp, hodd]
    · simp [coeff_zero_eq_eval_zero, eval_comp]
  have hpEval : p.eval (-y) = p.eval y := by
    have ht := congrArg (Polynomial.eval y) hpEven
    simpa only [eval_comp, eval_neg, eval_X] using ht
  let d : Polynomial R := taylor (-y) p - p - h
  have hdConst : d = Polynomial.C (d.coeff 0) := by
    apply polynomial_eq_of_derivative_eq_of_coeff_zero_eq
    · simpa only [derivative_C] using hd
    · simp
  have hpEval0 : p.eval 0 = 0 := by simpa only [← coeff_zero_eq_eval_zero] using hp0
  have hdEval0 : d.eval 0 = p.eval y - h.eval 0 := by
    dsimp [d]
    simp only [eval_sub, taylor_apply, eval_comp, eval_add, eval_X, eval_C,
      zero_add, hpEval, hpEval0, sub_zero]
  have hdEvalY : d.eval y = -(p.eval y - h.eval 0) := by
    dsimp [d]
    simp only [eval_sub, taylor_apply, eval_comp, eval_add, eval_X, eval_C,
      add_neg_cancel, hpEval0, heval]
    abel
  have hcEval : d.eval 0 = d.eval y := by rw [hdConst, eval_C, eval_C]
  have hneg : p.eval y - h.eval 0 = -(p.eval y - h.eval 0) := by
    rw [hdEval0, hdEvalY] at hcEval
    exact hcEval
  have htwo : (2 : ℚ) • (p.eval y - h.eval 0) = 0 := by
    simpa only [two_smul] using eq_neg_iff_add_eq_zero.mp hneg
  have hz : p.eval y - h.eval 0 = 0 := by
    have ht := congrArg (fun x : R => (2 : ℚ)⁻¹ • x) htwo
    simpa only [inv_smul_smul₀ (two_ne_zero : (2 : ℚ) ≠ 0), smul_zero] using ht
  change d = 0
  rw [hdConst]
  have hc0 : d.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero, hdEval0, hz]
  rw [hc0, map_zero]

end TernaryPoly
