module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Action
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs

@[expose] public section


/-!
# Translations and Levi matrices in plane coordinates (Appendix C.3, `ar:sec:series`)

The matrix `transMat v w` acts by the radical translation `u ↦ u + (v, w)`, the matrix
`diagMat A t` with `det A · t = 1` acts as the `leviMap A t` (Möbius action on `τ`), and the
triangular square root factors as `planeP p = transMat (u p) * diagMat (planeA p) (t p)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### Translations, Levi matrices and the triangular square root -/

theorem conj_apply (g G : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (g * G * g.transpose) i j = ∑ k, ∑ l, g i k * G k l * g j l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- The radical translation matrix `[[1, 0, v],[0, 1, w],[0, 0, 1]]`. -/
def transMat (v w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, v; 0, 1, w; 0, 0, 1]

/-- The Levi matrix `diag(A, t)`. -/
def diagMat (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, t]

/-- The binary block `A` of `planeP p`: `A = t^{-1/2} [[√y, x/√y],[0, 1/√y]]`. -/
def planeA (p : Fin 5 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt (p 3) / Real.sqrt (p 4), p 2 / (Real.sqrt (p 3) * Real.sqrt (p 4));
     0, 1 / (Real.sqrt (p 3) * Real.sqrt (p 4))]

theorem det_transMat (v w : ℝ) : (transMat v w).det = 1 := by
  simp [transMat, Matrix.det_fin_three]

theorem det_diagMat (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : (diagMat A t).det = A.det * t := by
  simp [diagMat, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem planeP_eq_mul (p : Fin 5 → ℝ) :
    planeP p = transMat (p 0) (p 1) * diagMat (planeA p) (p 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeP, transMat, diagMat, planeA, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem det_planeA {p : Fin 5 → ℝ} (hp : p ∈ Omega) : (planeA p).det * p 4 = 1 := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  simp [planeA, Matrix.det_fin_two, e3, e4, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le]
  field_simp

theorem planePoint_zero (G : Matrix (Fin 3) (Fin 3) ℝ) : planePoint G 0 = G 0 2 / G 2 2 := rfl
theorem planePoint_one' (G : Matrix (Fin 3) (Fin 3) ℝ) : planePoint G 1 = G 1 2 / G 2 2 := rfl
theorem planePoint_two (G : Matrix (Fin 3) (Fin 3) ℝ) : planePoint G 2 =
    (G 0 1 - G 0 2 * G 1 2 / G 2 2) / (G 1 1 - G 1 2 * G 1 2 / G 2 2) := rfl
theorem planePoint_three (G : Matrix (Fin 3) (Fin 3) ℝ) : planePoint G 3 =
    1 / (Real.sqrt (G 2 2) * (G 1 1 - G 1 2 * G 1 2 / G 2 2)) := rfl
theorem planePoint_four (G : Matrix (Fin 3) (Fin 3) ℝ) : planePoint G 4 = Real.sqrt (G 2 2) := rfl

theorem planeAct_transMat (v w : ℝ) {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    planeAct (transMat v w) p = p + ![v, w, 0, 0, 0] := by
  obtain ⟨hy, ht⟩ := hp
  have hy' : p 3 ≠ 0 := hy.ne'
  have ht' : p 4 ≠ 0 := ht.ne'
  set X := transMat v w * planeGram p * (transMat v w).transpose with hX
  have e22 : X 2 2 = p 4 ^ 2 := by
    rw [hX, conj_apply]; simp [transMat, planeGram, Fin.sum_univ_three]
  have e02 : X 0 2 = p 4 ^ 2 * (p 0 + v) := by
    rw [hX, conj_apply]; simp [transMat, planeGram, Fin.sum_univ_three]; ring
  have e12 : X 1 2 = p 4 ^ 2 * (p 1 + w) := by
    rw [hX, conj_apply]; simp [transMat, planeGram, Fin.sum_univ_three]; ring
  have e01 : X 0 1 = p 2 / (p 4 * p 3) + p 4 ^ 2 * (p 0 + v) * (p 1 + w) := by
    rw [hX, conj_apply]; simp [transMat, planeGram, Fin.sum_univ_three]; ring
  have e11 : X 1 1 = 1 / (p 4 * p 3) + p 4 ^ 2 * (p 1 + w) ^ 2 := by
    rw [hX, conj_apply]; simp [transMat, planeGram, Fin.sum_univ_three]; ring
  have hC : X 1 1 - X 1 2 * X 1 2 / X 2 2 = 1 / (p 4 * p 3) := by
    rw [e11, e12, e22]; field_simp; ring
  have hC01 : X 0 1 - X 0 2 * X 1 2 / X 2 2 = p 2 / (p 4 * p 3) := by
    rw [e01, e02, e12, e22]; field_simp; ring
  funext i
  fin_cases i
  · show planePoint X 0 = p 0 + v
    rw [planePoint_zero, e02, e22]; field_simp
  · show planePoint X 1 = p 1 + w
    rw [planePoint_one', e12, e22]; field_simp
  · show planePoint X 2 = p 2 + 0
    rw [planePoint_two, hC01, hC]; field_simp; ring
  · show planePoint X 3 = p 3 + 0
    rw [planePoint_three, hC, e22, Real.sqrt_sq ht.le]; field_simp; ring
  · show planePoint X 4 = p 4 + 0
    rw [planePoint_four, e22, Real.sqrt_sq ht.le]; ring

/-! ### Levi matrices act by the Möbius transformation of `leviMap` -/

theorem mobius_re_im (a b c d x y : ℝ) (hQ : 0 < (c * x + d) ^ 2 + (c * y) ^ 2) :
    ((((a : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) + b) /
        ((c : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) + d)).re =
      ((a * x + b) * (c * x + d) + a * c * y ^ 2) / ((c * x + d) ^ 2 + (c * y) ^ 2)) ∧
    ((((a : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) + b) /
        ((c : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) + d)).im =
      (a * d - b * c) * y / ((c * x + d) ^ 2 + (c * y) ^ 2)) := by
  have hw : (c : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) + d = ⟨c * x + d, c * y⟩ := by
    apply Complex.ext <;> simp
  have hz : (a : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) + b = ⟨a * x + b, a * y⟩ := by
    apply Complex.ext <;> simp
  have hQ' : (c * x + d) * (c * x + d) + c * y * (c * y) ≠ 0 := by
    have : (c * x + d) * (c * x + d) + c * y * (c * y) = (c * x + d) ^ 2 + (c * y) ^ 2 := by ring
    rw [this]; exact hQ.ne'
  rw [hw, hz]
  constructor
  · rw [Complex.div_re]
    simp only [Complex.normSq_mk]
    field_simp
  · rw [Complex.div_im]
    simp only [Complex.normSq_mk]
    field_simp
    ring

theorem planeAct_diag (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hdet : 0 < A.det) (ht : 0 < t)
    (hAt : A.det * t = 1) {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    planeAct (diagMat A t) p = leviMap A t p := by
  obtain ⟨hy, hT⟩ := hp
  have hy' : p 3 ≠ 0 := hy.ne'
  have hT' : p 4 ≠ 0 := hT.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = A.det := (Matrix.det_fin_two A).symm
  have hdt : A.det = t⁻¹ := by field_simp; exact hAt
  set a := A 0 0 with ha
  set b := A 0 1 with hb
  set c := A 1 0 with hc
  set d := A 1 1 with hd
  set X := diagMat A t * planeGram p * (diagMat A t).transpose with hX
  have e22 : X 2 2 = t ^ 2 * p 4 ^ 2 := by
    rw [hX, conj_apply]; simp [diagMat, planeGram, Fin.sum_univ_three]; ring
  have e02 : X 0 2 = t * p 4 ^ 2 * (a * p 0 + b * p 1) := by
    rw [hX, conj_apply]; simp [diagMat, planeGram, Fin.sum_univ_three, ha, hb]; ring
  have e12 : X 1 2 = t * p 4 ^ 2 * (c * p 0 + d * p 1) := by
    rw [hX, conj_apply]; simp [diagMat, planeGram, Fin.sum_univ_three, hc, hd]; ring
  have e01 : X 0 1 = a * c * (((p 2) ^ 2 + (p 3) ^ 2) / (p 4 * p 3) + (p 4) ^ 2 * (p 0) ^ 2) +
      (a * d + b * c) * (p 2 / (p 4 * p 3) + (p 4) ^ 2 * (p 0) * (p 1)) +
      b * d * (1 / (p 4 * p 3) + (p 4) ^ 2 * (p 1) ^ 2) := by
    rw [hX, conj_apply]; simp [diagMat, planeGram, Fin.sum_univ_three, ha, hb, hc, hd]; ring
  have e11 : X 1 1 = c * c * (((p 2) ^ 2 + (p 3) ^ 2) / (p 4 * p 3) + (p 4) ^ 2 * (p 0) ^ 2) +
      2 * c * d * (p 2 / (p 4 * p 3) + (p 4) ^ 2 * (p 0) * (p 1)) +
      d * d * (1 / (p 4 * p 3) + (p 4) ^ 2 * (p 1) ^ 2) := by
    rw [hX, conj_apply]; simp [diagMat, planeGram, Fin.sum_univ_three, hc, hd]; ring
  have hQpos : 0 < (c * p 2 + d) ^ 2 + (c * p 3) ^ 2 := by
    by_cases hc0 : c = 0
    · have : d ≠ 0 := by
        intro hd0
        rw [← hdet', hc0, hd0] at hdet; simp at hdet
      rw [hc0]; simp; positivity
    · have : 0 < (c * p 3) ^ 2 := by positivity
      nlinarith [sq_nonneg (c * p 2 + d)]
  have hQ : (c * p 2 + d) ^ 2 + (c * p 3) ^ 2 ≠ 0 := hQpos.ne'
  have hC : X 1 1 - X 1 2 * X 1 2 / X 2 2 =
      ((c * p 2 + d) ^ 2 + (c * p 3) ^ 2) / (p 4 * p 3) := by
    rw [e11, e12, e22]; field_simp; ring
  have hC01 : X 0 1 - X 0 2 * X 1 2 / X 2 2 =
      ((a * p 2 + b) * (c * p 2 + d) + a * c * p 3 ^ 2) / (p 4 * p 3) := by
    rw [e01, e02, e12, e22]; field_simp; ring
  obtain ⟨hre, him⟩ := mobius_re_im a b c d (p 2) (p 3) hQpos
  funext i
  fin_cases i
  · show planePoint X 0 = (a * p 0 + b * p 1) / t
    rw [planePoint_zero, e02, e22]; field_simp
  · show planePoint X 1 = (c * p 0 + d * p 1) / t
    rw [planePoint_one', e12, e22]; field_simp
  · show planePoint X 2 = _
    rw [planePoint_two, hC01, hC]
    show _ = (((a : ℂ) * seedTau p + b) / ((c : ℂ) * seedTau p + d)).re
    rw [seedTau, hre]
    field_simp
  · show planePoint X 3 = _
    rw [planePoint_three, hC, e22]
    show _ = (((a : ℂ) * seedTau p + b) / ((c : ℂ) * seedTau p + d)).im
    rw [seedTau, him]
    have hsq : Real.sqrt (t ^ 2 * p 4 ^ 2) = t * p 4 := by
      rw [← mul_pow]; exact Real.sqrt_sq (mul_pos ht hT).le
    rw [hsq]
    have : a * d - b * c = A.det := by rw [← hdet']
    rw [this, hdt]
    field_simp
  · show planePoint X 4 = t * p 4
    rw [planePoint_four, e22]
    rw [← mul_pow]; exact Real.sqrt_sq (mul_pos ht hT).le

end TernaryPeriodPolynomials.Argument.ConvergenceC4
