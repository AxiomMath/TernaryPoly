module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Operator
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# Hecke recursion: composition of Hermite actions

Formalized by Claude Sonnet 5.5.

`coe_hnfAct` (coordinates of the Hermite action), `hnfAct_comp` (the product of two Hermite matrices acts as their product), `PerInv` (invariance under `z ↦ z + 1`), `perInv_reduce` (a product Hermite triple is reduced modulo the translation).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion

open Finset Matrix TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

/-- The coordinate of the Hermite action. -/
theorem coe_hnfAct {t : ℕ × ℕ × ℕ} (ha : 0 < t.1) (hd : 0 < t.2.2) (z : UpperHalfPlane) :
    ((hnfAct t z : UpperHalfPlane) : ℂ) = ((t.1 : ℂ) * (z : ℂ) + (t.2.1 : ℂ)) / (t.2.2 : ℂ) := by
  have hdet : (hnfMat t).det ≠ 0 := by
    rw [hnfMat_det]
    have h1 : (t.1 : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have h2 : (t.2.2 : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    exact mul_ne_zero h1 h2
  have hpos : 0 < (GeneralLinearGroup.mkOfDetNeZero (hnfMat t) hdet).det.val := by
    simp only [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.mkOfDetNeZero]
    change 0 < (hnfMat t).det
    rw [hnfMat_det]
    have h1 : (0 : ℝ) < t.1 := by exact_mod_cast ha
    have h2 : (0 : ℝ) < t.2.2 := by exact_mod_cast hd
    positivity
  rw [hnfAct_eq_of_det hdet, UpperHalfPlane.coe_smul_of_det_pos hpos]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, hnfMat, GeneralLinearGroup.mkOfDetNeZero]

theorem hnfAct_comp {s t : ℕ × ℕ × ℕ} (hsa : 0 < s.1) (hsd : 0 < s.2.2) (hta : 0 < t.1) (htd : 0 < t.2.2)
    (z : UpperHalfPlane) :
    hnfAct s (hnfAct t z) = hnfAct (s.1 * t.1, s.1 * t.2.1 + s.2.1 * t.2.2, s.2.2 * t.2.2) z := by
  apply UpperHalfPlane.ext
  rw [coe_hnfAct hsa hsd, coe_hnfAct hta htd, coe_hnfAct (Nat.mul_pos hsa hta) (Nat.mul_pos hsd htd)]
  have h1 : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have h2 : (t.2.2 : ℂ) ≠ 0 := by exact_mod_cast htd.ne'
  push_cast
  field_simp
  ring

/-- Invariance under `z ↦ z + 1`. -/
def PerInv (F : UpperHalfPlane → ℂ) : Prop := ∀ z, F (hnfAct (1, 1, 1) z) = F z

theorem hnfAct_zero (z : UpperHalfPlane) : hnfAct (1, 0, 1) z = z := by
  apply UpperHalfPlane.ext
  rw [coe_hnfAct (by norm_num) (by norm_num)]
  simp

theorem perInv_nat {F : UpperHalfPlane → ℂ} (hF : PerInv F) (q : ℕ) (z : UpperHalfPlane) :
    F (hnfAct (1, q, 1) z) = F z := by
  induction q with
  | zero => rw [hnfAct_zero]
  | succ q ih =>
    have h := hnfAct_comp (s := (1, 1, 1)) (t := (1, q, 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z
    simp only [one_mul, mul_one] at h
    rw [← h, hF, ih]

theorem perInv_reduce {F : UpperHalfPlane → ℂ} (hF : PerInv F) {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℕ)
    (z : UpperHalfPlane) : F (hnfAct (a, b, d) z) = F (hnfAct (a, b % d, d) z) := by
  have h := hnfAct_comp (s := (1, b / d, 1)) (t := (a, b % d, d)) (by norm_num) (by norm_num) ha hd z
  simp only [one_mul] at h
  rw [show b % d + b / d * d = b by rw [mul_comm]; exact Nat.mod_add_div b d] at h
  rw [← h, perInv_nat hF]

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
