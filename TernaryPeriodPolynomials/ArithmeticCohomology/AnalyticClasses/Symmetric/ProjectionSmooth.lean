module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Symmetric.Projection

@[expose] public section


/-!
# Smoothness and invariance of the projection to the plane symmetric space

For an invertible real `3 × 3` matrix `y` the corner `S₂₂` of the Gram matrix `S = y yᵀ`, the
corner `M₁₁` of its Schur complement `M` and the determinant `det M = (det y)² / S₂₂` are
positive. Hence the radical coordinate `S_{·2} / S₂₂` and the Levi point
`(M₀₁ + i √det M) / M₁₁` are analytic (in particular `C^∞`) at `y`, and the Levi point lies in
the upper half plane. Both maps only see the Gram matrix, so they are invariant under
`y ↦ y k` for orthogonal `k` and under nonzero scalings `y ↦ c • y`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

/-! ### The Gram matrix and its Schur complement as functions of a symmetric matrix -/

/-- The radical coordinate `S_{·2} / S₂₂` of a `3 × 3` matrix `S`. -/
def radicalOf (S : Matrix (Fin 3) (Fin 3) ℝ) : Fin 2 → ℝ :=
  fun i => S i.castSucc 2 / S 2 2

/-- The Schur complement `S_{tl} - S_{·2} S_{·2}ᵀ / S₂₂` of a `3 × 3` matrix `S`. -/
def schurOf (S : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => S i.castSucc j.castSucc - S i.castSucc 2 * S j.castSucc 2 / S 2 2

theorem symmetricRadical_eq_radicalOf (y : Matrix (Fin 3) (Fin 3) ℝ) :
    symmetricRadical y = radicalOf (gramMatrix y) := rfl

theorem symmetricSchur_eq_schurOf (y : Matrix (Fin 3) (Fin 3) ℝ) :
    symmetricSchur y = schurOf (gramMatrix y) := rfl

theorem symmetricPoint_eq (y : Matrix (Fin 3) (Fin 3) ℝ) :
    symmetricPoint y = positivePoint (schurOf (gramMatrix y)) := rfl

theorem gramMatrix_apply (y : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    gramMatrix y a b = ∑ m, y a m * y b m := by
  simp only [gramMatrix, Matrix.mul_apply, Matrix.transpose_apply]

theorem gramMatrix_symm (y : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    gramMatrix y a b = gramMatrix y b a := by
  simp only [gramMatrix_apply, mul_comm]

/-- The Schur complement identity `det M · S₂₂ = det S` for a symmetric matrix `S`. -/
theorem schurOf_det_mul (S : Matrix (Fin 3) (Fin 3) ℝ) (h01 : S 1 0 = S 0 1)
    (h02 : S 2 0 = S 0 2) (h12 : S 2 1 = S 1 2) (pivot : S 2 2 ≠ 0) :
    (schurOf S).det * S 2 2 = S.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_three]
  simp only [schurOf, h01, h02, h12]
  simp only [Fin.isValue, Fin.castSucc_zero, Fin.castSucc_one]
  field_simp
  linear_combination (S 2 2 * S 0 2 * S 1 2 - S 2 2 ^ 2 * S 0 1) * h01

theorem gramMatrix_det (y : Matrix (Fin 3) (Fin 3) ℝ) : (gramMatrix y).det = y.det ^ 2 := by
  rw [gramMatrix, Matrix.det_mul, Matrix.det_transpose, sq]

/-! ### Positivity -/

theorem gramMatrix_two_two_pos {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    0 < gramMatrix y 2 2 := by
  rw [gramMatrix_apply, Fin.sum_univ_three]
  by_contra hle
  have h0 : y 2 0 = 0 := by nlinarith [sq_nonneg (y 2 0), sq_nonneg (y 2 1), sq_nonneg (y 2 2)]
  have h1 : y 2 1 = 0 := by nlinarith [sq_nonneg (y 2 0), sq_nonneg (y 2 1), sq_nonneg (y 2 2)]
  have h2 : y 2 2 = 0 := by nlinarith [sq_nonneg (y 2 0), sq_nonneg (y 2 1), sq_nonneg (y 2 2)]
  apply hy
  rw [Matrix.det_fin_three, h0, h1, h2]
  ring

/-- `M₁₁ · S₂₂ = S₁₁ S₂₂ - S₁₂²` is positive: Lagrange's identity and Laplace expansion. -/
theorem symmetricSchur_one_one_mul_pos {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    0 < gramMatrix y 1 1 * gramMatrix y 2 2 - gramMatrix y 1 2 ^ 2 := by
  have lagrange : gramMatrix y 1 1 * gramMatrix y 2 2 - gramMatrix y 1 2 ^ 2 =
      (y 1 0 * y 2 1 - y 1 1 * y 2 0) ^ 2 + (y 1 0 * y 2 2 - y 1 2 * y 2 0) ^ 2 +
        (y 1 1 * y 2 2 - y 1 2 * y 2 1) ^ 2 := by
    simp only [gramMatrix_apply, Fin.sum_univ_three]
    ring
  have laplace : y.det = y 0 0 * (y 1 1 * y 2 2 - y 1 2 * y 2 1) -
      y 0 1 * (y 1 0 * y 2 2 - y 1 2 * y 2 0) + y 0 2 * (y 1 0 * y 2 1 - y 1 1 * y 2 0) := by
    rw [Matrix.det_fin_three]
    ring
  rw [lagrange]
  by_contra hle
  have m01 : y 1 0 * y 2 1 - y 1 1 * y 2 0 = 0 := by
    nlinarith [sq_nonneg (y 1 0 * y 2 1 - y 1 1 * y 2 0), sq_nonneg (y 1 0 * y 2 2 - y 1 2 * y 2 0),
      sq_nonneg (y 1 1 * y 2 2 - y 1 2 * y 2 1)]
  have m02 : y 1 0 * y 2 2 - y 1 2 * y 2 0 = 0 := by
    nlinarith [sq_nonneg (y 1 0 * y 2 1 - y 1 1 * y 2 0), sq_nonneg (y 1 0 * y 2 2 - y 1 2 * y 2 0),
      sq_nonneg (y 1 1 * y 2 2 - y 1 2 * y 2 1)]
  have m12 : y 1 1 * y 2 2 - y 1 2 * y 2 1 = 0 := by
    nlinarith [sq_nonneg (y 1 0 * y 2 1 - y 1 1 * y 2 0), sq_nonneg (y 1 0 * y 2 2 - y 1 2 * y 2 0),
      sq_nonneg (y 1 1 * y 2 2 - y 1 2 * y 2 1)]
  apply hy
  rw [laplace, m01, m02, m12]
  ring

theorem symmetricSchur_one_one_pos {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    0 < symmetricSchur y 1 1 := by
  have pivot := gramMatrix_two_two_pos hy
  have key := symmetricSchur_one_one_mul_pos hy
  have e : symmetricSchur y 1 1 =
      (gramMatrix y 1 1 * gramMatrix y 2 2 - gramMatrix y 1 2 ^ 2) / gramMatrix y 2 2 := by
    simp only [symmetricSchur, Fin.isValue, Fin.castSucc_one]
    field_simp
  rw [e]
  exact div_pos key pivot

theorem symmetricSchur_det_eq {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    (symmetricSchur y).det = y.det ^ 2 / gramMatrix y 2 2 := by
  have pivot := gramMatrix_two_two_pos hy
  rw [← gramMatrix_det, ← schurOf_det_mul (gramMatrix y) (gramMatrix_symm y 1 0)
    (gramMatrix_symm y 2 0) (gramMatrix_symm y 2 1) pivot.ne', symmetricSchur_eq_schurOf,
    mul_div_cancel_right₀ _ pivot.ne']

theorem symmetricSchur_det_pos {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    0 < (symmetricSchur y).det := by
  rw [symmetricSchur_det_eq hy]
  exact div_pos (pow_pos (abs_pos.mpr hy) 2 |>.trans_eq (sq_abs _)) (gramMatrix_two_two_pos hy)

theorem positivePoint_eq_add (M : Matrix (Fin 2) (Fin 2) ℝ) :
    positivePoint M =
      ((M 0 1 / M 1 1 : ℝ) : ℂ) + Complex.I * ((Real.sqrt M.det / M 1 1 : ℝ) : ℂ) := by
  rw [positivePoint]
  push_cast
  ring

theorem positivePoint_re (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (positivePoint M).re = M 0 1 / M 1 1 := by
  rw [positivePoint_eq_add]
  simp

theorem positivePoint_im (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (positivePoint M).im = Real.sqrt M.det / M 1 1 := by
  rw [positivePoint_eq_add]
  simp

theorem positivePoint_im_pos {M : Matrix (Fin 2) (Fin 2) ℝ} (h11 : 0 < M 1 1) (hdet : 0 < M.det) :
    0 < (positivePoint M).im := by
  rw [positivePoint_im]
  exact div_pos (Real.sqrt_pos.mpr hdet) h11

/-- **The Levi point lies in the upper half plane.** -/
theorem symmetricPoint_im_pos {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    0 < (symmetricPoint y).im :=
  positivePoint_im_pos (symmetricSchur_one_one_pos hy) (symmetricSchur_det_pos hy)

/-! ### Smoothness -/

theorem contDiff_gramMatrix_apply (n : WithTop ℕ∞) (a b : Fin 3) :
    ContDiff ℝ n (fun y : Matrix (Fin 3) (Fin 3) ℝ => gramMatrix y a b) := by
  have e : ∀ i j : Fin 3, ContDiff ℝ n (fun y : Matrix (Fin 3) (Fin 3) ℝ => y i j) :=
    fun i j => contDiff_pi.mp (contDiff_pi.mp contDiff_id i) j
  simp only [gramMatrix_apply]
  exact ContDiff.sum fun m _ => (e a m).mul (e b m)

theorem contDiffAt_symmetricSchur_apply (n : WithTop ℕ∞) {y : Matrix (Fin 3) (Fin 3) ℝ}
    (hy : y.det ≠ 0) (i j : Fin 2) :
    ContDiffAt ℝ n (fun z => symmetricSchur z i j) y := by
  have g := fun a b => (contDiff_gramMatrix_apply n a b).contDiffAt (x := y)
  exact (g _ _).sub (((g _ _).mul (g _ _)).div (g 2 2) (gramMatrix_two_two_pos hy).ne')

theorem contDiffAt_symmetricRadical_of (n : WithTop ℕ∞) {y : Matrix (Fin 3) (Fin 3) ℝ}
    (hy : y.det ≠ 0) : ContDiffAt ℝ n symmetricRadical y := by
  have g := fun a b => (contDiff_gramMatrix_apply n a b).contDiffAt (x := y)
  exact contDiffAt_pi.mpr fun i => (g _ _).div (g 2 2) (gramMatrix_two_two_pos hy).ne'

theorem contDiffAt_symmetricPoint_of (n : WithTop ℕ∞) {y : Matrix (Fin 3) (Fin 3) ℝ}
    (hy : y.det ≠ 0) : ContDiffAt ℝ n symmetricPoint y := by
  have m := contDiffAt_symmetricSchur_apply n hy
  have h11 := (symmetricSchur_one_one_pos hy).ne'
  have det : ContDiffAt ℝ n (fun z => (symmetricSchur z).det) y := by
    simp only [Matrix.det_fin_two]
    exact ((m 0 0).mul (m 1 1)).sub ((m 0 1).mul (m 1 0))
  have re : ContDiffAt ℝ n (fun z => symmetricSchur z 0 1 / symmetricSchur z 1 1) y :=
    (m 0 1).div (m 1 1) h11
  have im : ContDiffAt ℝ n
      (fun z => Real.sqrt (symmetricSchur z).det / symmetricSchur z 1 1) y :=
    (det.sqrt (symmetricSchur_det_pos hy).ne').div (m 1 1) h11
  have e : symmetricPoint = fun z =>
      ((symmetricSchur z 0 1 / symmetricSchur z 1 1 : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (symmetricSchur z).det / symmetricSchur z 1 1 : ℝ) : ℂ) := by
    funext z
    exact positivePoint_eq_add _
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y re).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y im))

/-- **The radical coordinate is analytic on invertible matrices.** -/
theorem contDiffAt_symmetricRadical {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    ContDiffAt ℝ ⊤ symmetricRadical y :=
  contDiffAt_symmetricRadical_of ⊤ hy

/-- **The Levi point is analytic on invertible matrices.** -/
theorem contDiffAt_symmetricPoint {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    ContDiffAt ℝ ⊤ symmetricPoint y :=
  contDiffAt_symmetricPoint_of ⊤ hy

/-- **The radical coordinate is `C^∞` on invertible matrices.** -/
theorem contDiffAt_infty_symmetricRadical {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) symmetricRadical y :=
  contDiffAt_symmetricRadical_of _ hy

/-- **The Levi point is `C^∞` on invertible matrices.** -/
theorem contDiffAt_infty_symmetricPoint {y : Matrix (Fin 3) (Fin 3) ℝ} (hy : y.det ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) symmetricPoint y :=
  contDiffAt_symmetricPoint_of _ hy

/-! ### Invariances -/

theorem gramMatrix_mul_orthogonal (y : Matrix (Fin 3) (Fin 3) ℝ) {k : Matrix (Fin 3) (Fin 3) ℝ}
    (hk : kᵀ * k = 1) : gramMatrix (y * k) = gramMatrix y := by
  have hk' : k * kᵀ = 1 := mul_eq_one_comm.mp hk
  rw [gramMatrix, gramMatrix, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k,
    hk', Matrix.one_mul]

theorem symmetricRadical_mul_orthogonal (y : Matrix (Fin 3) (Fin 3) ℝ)
    {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    symmetricRadical (y * k) = symmetricRadical y := by
  rw [symmetricRadical_eq_radicalOf, symmetricRadical_eq_radicalOf, gramMatrix_mul_orthogonal y hk]

theorem symmetricSchur_mul_orthogonal (y : Matrix (Fin 3) (Fin 3) ℝ)
    {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    symmetricSchur (y * k) = symmetricSchur y := by
  rw [symmetricSchur_eq_schurOf, symmetricSchur_eq_schurOf, gramMatrix_mul_orthogonal y hk]

theorem symmetricPoint_mul_orthogonal (y : Matrix (Fin 3) (Fin 3) ℝ)
    {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    symmetricPoint (y * k) = symmetricPoint y := by
  rw [symmetricPoint, symmetricPoint, symmetricSchur_mul_orthogonal y hk]

theorem gramMatrix_smul (c : ℝ) (y : Matrix (Fin 3) (Fin 3) ℝ) :
    gramMatrix (c • y) = (c ^ 2) • gramMatrix y := by
  rw [gramMatrix, gramMatrix, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sq]

theorem symmetricRadical_smul {c : ℝ} (hc : c ≠ 0) (y : Matrix (Fin 3) (Fin 3) ℝ) :
    symmetricRadical (c • y) = symmetricRadical y := by
  funext i
  simp only [symmetricRadical, gramMatrix_smul, Matrix.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

theorem symmetricSchur_smul {c : ℝ} (hc : c ≠ 0) (y : Matrix (Fin 3) (Fin 3) ℝ) :
    symmetricSchur (c • y) = (c ^ 2) • symmetricSchur y := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  funext i j
  simp only [symmetricSchur, gramMatrix_smul, Matrix.smul_apply, smul_eq_mul]
  by_cases pivot : gramMatrix y 2 2 = 0
  · simp [pivot]
  · field_simp

/-- `positivePoint` is invariant under positive scalings. -/
theorem positivePoint_smul {c : ℝ} (hc : 0 < c) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    positivePoint (c • M) = positivePoint M := by
  have det : (c • M).det = c ^ 2 * M.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have root : Real.sqrt ((c • M).det) = c * Real.sqrt M.det := by
    rw [det, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [positivePoint, positivePoint, root]
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [show (c : ℂ) * (M 0 1 : ℂ) + Complex.I * ((c : ℂ) * (Real.sqrt M.det : ℂ)) =
      (c : ℂ) * ((M 0 1 : ℂ) + Complex.I * (Real.sqrt M.det : ℂ)) by ring]
  exact mul_div_mul_left _ _ hc'

theorem symmetricPoint_smul {c : ℝ} (hc : c ≠ 0) (y : Matrix (Fin 3) (Fin 3) ℝ) :
    symmetricPoint (c • y) = symmetricPoint y := by
  rw [symmetricPoint, symmetricPoint, symmetricSchur_smul hc,
    positivePoint_smul (by positivity)]

end TernaryPeriodPolynomials.AnalyticClasses
