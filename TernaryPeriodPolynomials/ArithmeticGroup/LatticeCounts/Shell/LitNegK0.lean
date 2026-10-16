module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0

@[expose] public section


/-!
# The K0 block of the reflected point

If `K0Spec r s t k A`, then `K0Spec r s (-t) (dC * k * dE) (dD * A * dD)`, where
`dD = diag(1,-1)`, `dC = diag(1,1,-1)`, `dE = diag(1,-1,1)`. The reason is the identity
`Lst s (-t) * toQ (dC * k * dE) = dEq * (Lst s t * toQ k) * dEq`: conjugation by `dEq` changes
the sign of the entries in the first two indices according to `dD`, and fixes the bottom row
except for the entry `(2,2)`, which is unchanged.
-/

open Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (Lst toQ K0Spec)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegK0

variable {p : ℕ} [Fact p.Prime]

/-- The sign `diag(1,-1)` on `2 × 2` blocks. -/
def dD : Matrix (Fin 2) (Fin 2) ℤ_[p] := !![1, 0; 0, -1]

/-- The sign `diag(1,1,-1)` on `3 × 3` matrices. -/
def dC : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- The sign `diag(1,-1,1)` on `3 × 3` matrices. -/
def dE : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The rational sign `diag(1,-1,1)`. -/
def dEq : Matrix (Fin 3) (Fin 3) ℚ_[p] := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The rational sign `diag(1,1,-1)`. -/
def dCq : Matrix (Fin 3) (Fin 3) ℚ_[p] := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

theorem toQ_mul (X Y : Matrix (Fin 3) (Fin 3) ℤ_[p]) : toQ (X * Y) = toQ X * toQ Y := by
  ext i j
  simp [toQ, Matrix.mul_apply, Fin.sum_univ_three]

/-- `Lst(s, -t)` is `dEq · Lst(s,t) · dCq` over `ℚ_[p]`. -/
theorem Lst_neg_eq (s t : ℚ_[p]) : Lst s (-t) = dEq * Lst s t * dCq := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lst, dEq, dCq, Matrix.mul_apply, Fin.sum_univ_three]

/-- The matrix identity behind the reflection of a K0 block. -/
theorem Lst_neg_toQ (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) :
    Lst s (-t) * toQ (dC * k * dE) = dEq * (Lst s t * toQ k) * dEq := by
  have hC : toQ (dC (p := p)) = dCq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toQ, dC, dCq]
  have hE : toQ (dE (p := p)) = dEq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toQ, dE, dEq]
  have hCC : dCq * dCq = (1 : Matrix (Fin 3) (Fin 3) ℚ_[p]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dCq, Matrix.mul_apply, Fin.sum_univ_three]
  rw [toQ_mul, toQ_mul, hC, hE, Lst_neg_eq]
  calc dEq * Lst s t * dCq * (dCq * toQ k * dEq)
      = dEq * Lst s t * (dCq * dCq) * toQ k * dEq := by
        simp only [mul_assoc]
    _ = dEq * (Lst s t * toQ k) * dEq := by
        rw [hCC]
        simp only [mul_one, mul_assoc]

/-- **Reflected K0 block.** `K0Spec` is preserved by `(t, A) ↦ (-t, dD A dD)`. -/
theorem K0Spec_neg {r : ℕ} {s t : ℚ_[p]} {k : Matrix (Fin 3) (Fin 3) ℤ_[p]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[p]} (h : K0Spec r s t k A) :
    K0Spec r s (-t) (dC * k * dE) (dD * A * dD) := by
  obtain ⟨hk, hA, hnorm, hent, h20, h21, h22⟩ := h
  have key := Lst_neg_toQ s t k
  generalize Lst s t * toQ k = M at key hent h20 h21 h22
  have e00 : M 0 0 = (A 0 0 : ℚ_[p]) := hent 0 0
  have e01 : M 0 1 = (A 0 1 : ℚ_[p]) := hent 0 1
  have e10 : M 1 0 = (A 1 0 : ℚ_[p]) := hent 1 0
  have e11 : M 1 1 = (A 1 1 : ℚ_[p]) := hent 1 1
  unfold K0Spec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hk]
    simp [dC, dE, Matrix.det_fin_three]
  · rw [Matrix.det_mul, Matrix.det_mul, hA]
    simp [dD, Matrix.det_fin_two]
  · intro j
    fin_cases j
    · convert hnorm 0 using 2
      simp [dD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    · have h1 : ‖-(s * (A 0 1 : ℚ_[p]) + t * (A 1 1 : ℚ_[p]))‖ ≤ 1 := by
        rw [norm_neg]
        exact hnorm 1
      convert h1 using 2
      simp [dD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      ring
  · intro i j
    rw [key]
    fin_cases i <;> fin_cases j <;>
      simp [dEq, dD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, e00, e01, e10, e11]
  · rw [key]
    simp [dEq, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h20]
  · rw [key]
    simp [dEq, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h21]
  · rw [key]
    simp [dEq, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h22]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegK0
