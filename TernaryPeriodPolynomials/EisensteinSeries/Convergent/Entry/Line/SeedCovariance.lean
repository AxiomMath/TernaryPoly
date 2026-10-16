module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Iwasawa
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityChart

@[expose] public section


/-!
# Line-face coordinates of `q G qᵀ` for `q` in the line parabolic

For `q = [[a, bᵀ], [0, C]]` and a positive Gram matrix `G`, the line-face coordinates of `q G qᵀ` are
`w' = (a w + b) C⁻¹` (`lineChart_lineConj_w`) and `τ' = (C₀₀τ + C₀₁)/(C₁₀τ + C₁₁)` for `det C > 0`
(`lineTau_lineConj`). Used for R3 of the ML4b reduction (Appendix C.5, `ar:sec:real`).

Written by Claude Opus 5.5.
-/

open MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

/-- The Möbius action `τ ↦ (C₀₀τ + C₀₁)/(C₁₀τ + C₁₁)`. -/
def mobius (C : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℂ) : ℂ :=
  ((C 0 0 : ℂ) * τ + C 0 1) / ((C 1 0 : ℂ) * τ + C 1 1)

/-- `q G qᵀ` for `q = [[a, bᵀ], [0, C]]`. -/
def lineConj (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  lineParabolic a b C * G * (lineParabolic a b C).transpose

private theorem lineConj_entries (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) :
    lineConj a b C G 0 1 = (a * G 0 1 + b 0 * G 1 1 + b 1 * G 1 2) * C 0 0 +
      (a * G 0 2 + b 0 * G 1 2 + b 1 * G 2 2) * C 0 1 ∧
    lineConj a b C G 0 2 = (a * G 0 1 + b 0 * G 1 1 + b 1 * G 1 2) * C 1 0 +
      (a * G 0 2 + b 0 * G 1 2 + b 1 * G 2 2) * C 1 1 ∧
    lineConj a b C G 1 1 = C 0 0 ^ 2 * G 1 1 + 2 * C 0 0 * C 0 1 * G 1 2 + C 0 1 ^ 2 * G 2 2 ∧
    lineConj a b C G 1 2 = C 0 0 * C 1 0 * G 1 1 + (C 0 0 * C 1 1 + C 0 1 * C 1 0) * G 1 2 +
      C 0 1 * C 1 1 * G 2 2 ∧
    lineConj a b C G 2 1 = C 0 0 * C 1 0 * G 1 1 + (C 0 0 * C 1 1 + C 0 1 * C 1 0) * G 1 2 +
      C 0 1 * C 1 1 * G 2 2 ∧
    lineConj a b C G 2 2 = C 1 0 ^ 2 * G 1 1 + 2 * C 1 0 * C 1 1 * G 1 2 + C 1 1 ^ 2 * G 2 2 := by
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have h20 : G 2 0 = G 0 2 := hG.apply 0 2
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  simp only [lineConj, lineParabolic, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h10, h20, h21] <;> ring

/-- The line radical coordinates of `q G qᵀ`: `w' = (a w + b) C⁻¹`. -/
theorem lineChart_lineConj_w (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : C.det ≠ 0) (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm)
    (hB : G 1 1 * G 2 2 - G 1 2 * G 2 1 ≠ 0) :
    lineChart (lineConj a b C G) 0 =
        ((a * lineChart G 0 + b 0) * C 1 1 - (a * lineChart G 1 + b 1) * C 1 0) / C.det ∧
      lineChart (lineConj a b C G) 1 =
        ((a * lineChart G 1 + b 1) * C 0 0 - (a * lineChart G 0 + b 0) * C 0 1) / C.det := by
  obtain ⟨e01, e02, e11, e12, e21, e22⟩ := lineConj_entries a b C G hG
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  rw [h21] at hB
  have hdC : C.det = C 0 0 * C 1 1 - C 0 1 * C 1 0 := Matrix.det_fin_two C
  have hB' : lineConj a b C G 1 1 * lineConj a b C G 2 2 -
      lineConj a b C G 1 2 * lineConj a b C G 2 1 = C.det ^ 2 * (G 1 1 * G 2 2 - G 1 2 ^ 2) := by
    rw [e11, e12, e21, e22, hdC]; ring
  have hB'ne : lineConj a b C G 1 1 * lineConj a b C G 2 2 -
      lineConj a b C G 1 2 * lineConj a b C G 2 1 ≠ 0 := by
    rw [hB']; exact mul_ne_zero (pow_ne_zero 2 hC) (by rw [← sq] at hB; simpa [sq] using hB)
  have hB2 : G 1 1 * G 2 2 - G 1 2 ^ 2 ≠ 0 := by rw [sq]; exact hB
  simp only [lineChart, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hB', h21, e01, e02, e12, e21, e22, e11, hdC]
  rw [hdC] at hC
  have hden : (C 0 0 * C 1 1 - C 0 1 * C 1 0) ^ 2 * (G 1 1 * G 2 2 - G 1 2 ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hC) hB2
  constructor <;> rw [div_eq_div_iff hden hC] <;> field_simp <;> ring

/-- The bottom-right entry of `q G qᵀ` is positive. -/
theorem lineConj_pos_22 (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : C.det ≠ 0) (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (h22 : 0 < G 2 2)
    (hB : 0 < G 1 1 * G 2 2 - G 1 2 * G 2 1) : 0 < lineConj a b C G 2 2 := by
  obtain ⟨-, -, -, -, -, e22⟩ := lineConj_entries a b C G hG
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  rw [h21] at hB
  have hdC : C.det = C 0 0 * C 1 1 - C 0 1 * C 1 0 := Matrix.det_fin_two C
  have key : lineConj a b C G 2 2 * G 2 2 =
      (C 1 0 * G 1 2 + C 1 1 * G 2 2) ^ 2 + C 1 0 ^ 2 * (G 1 1 * G 2 2 - G 1 2 * G 1 2) := by
    rw [e22]; ring
  have hpos : 0 < (C 1 0 * G 1 2 + C 1 1 * G 2 2) ^ 2 +
      C 1 0 ^ 2 * (G 1 1 * G 2 2 - G 1 2 * G 1 2) := by
    rcases eq_or_ne (C 1 0) 0 with h | h
    · have h11 : C 1 1 ≠ 0 := by
        intro h'
        apply hC
        rw [hdC, h, h']
        ring
      rw [h]
      have : 0 < (C 1 1 * G 2 2) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero h11 h22.ne')
      simpa using this
    · have : 0 < C 1 0 ^ 2 * (G 1 1 * G 2 2 - G 1 2 * G 1 2) := mul_pos (sq_pos_of_ne_zero h) hB
      positivity
  rw [← key] at hpos
  exact (mul_pos_iff_of_pos_right h22).mp hpos

/-- The line-face `τ` of `q G qᵀ` is the Möbius image of the `τ` of `G`. -/
theorem lineTau_lineConj (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : 0 < C.det) (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (h22 : 0 < G 2 2)
    (hB : 0 < G 1 1 * G 2 2 - G 1 2 * G 2 1) :
    lineTau (lineChart (lineConj a b C G)) = mobius C (lineTau (lineChart G)) := by
  have h22' := lineConj_pos_22 a b C hC.ne' G hG h22 hB
  obtain ⟨-, -, e11, e12, e21, e22⟩ := lineConj_entries a b C G hG
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  rw [h21] at hB
  have hdC : C.det = C 0 0 * C 1 1 - C 0 1 * C 1 0 := Matrix.det_fin_two C
  obtain ⟨s, hspos, hs2, hsdef⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = G 1 1 * G 2 2 - G 1 2 * G 1 2 ∧
      s = Real.sqrt (G 1 1 * G 2 2 - G 1 2 * G 1 2) :=
    ⟨_, Real.sqrt_pos.mpr hB, Real.sq_sqrt hB.le, rfl⟩
  have hB' : lineConj a b C G 1 1 * lineConj a b C G 2 2 -
      lineConj a b C G 1 2 * lineConj a b C G 2 1 =
        C.det ^ 2 * (G 1 1 * G 2 2 - G 1 2 * G 1 2) := by
    rw [e11, e12, e21, e22, hdC]; ring
  have hsq' : Real.sqrt (lineConj a b C G 1 1 * lineConj a b C G 2 2 -
      lineConj a b C G 1 2 * lineConj a b C G 2 1) = C.det * s := by
    rw [hB', Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC.le, ← hsdef]
  have hT : lineTau (lineChart (lineConj a b C G)) * (lineConj a b C G 2 2 : ℂ) =
      (lineConj a b C G 1 2 : ℂ) + Complex.I * ((C.det * s : ℝ) : ℂ) := by
    have hne : (lineConj a b C G 2 2 : ℂ) ≠ 0 := by exact_mod_cast h22'.ne'
    simp only [lineTau, lineChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons]
    rw [hsq']
    push_cast
    field_simp
  have hτ : lineTau (lineChart G) * (G 2 2 : ℂ) = (G 1 2 : ℂ) + Complex.I * (s : ℂ) := by
    have hne : (G 2 2 : ℂ) ≠ 0 := by exact_mod_cast h22.ne'
    simp only [lineTau, lineChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons, h21]
    rw [← hsdef]
    push_cast
    field_simp
  have hden : (C 1 0 : ℂ) * lineTau (lineChart G) + C 1 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp only [lineTau, lineChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons, h21, ← hsdef] at him hre
    simp only [Complex.ofReal_div, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.div_ofReal_im, Complex.ofReal_im, zero_div, Complex.I_re, mul_zero, Complex.I_im,
      Complex.div_ofReal_re, one_mul, zero_add, Complex.add_re, Complex.mul_re, zero_mul, sub_self,
      add_zero, Complex.zero_im, mul_eq_zero, div_eq_zero_iff, sub_zero, Complex.zero_re] at him hre
    have hc : C 1 0 = 0 := by
      rcases him with h0 | h0
      · exact h0
      · exact False.elim (h0.elim hspos.ne' h22.ne')
    rw [hc, zero_mul, zero_add] at hre
    apply hC.ne'
    rw [hdC, hc, hre]
    ring
  have hG22c : ((G 2 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h22.ne'
  have hG'22c : ((lineConj a b C G 2 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h22'.ne'
  rw [mobius, eq_div_iff hden]
  apply mul_right_cancel₀ (mul_ne_zero hG'22c hG22c)
  have hs2c : (s : ℂ) ^ 2 = ((G 1 1 : ℂ) * G 2 2 - G 1 2 * G 1 2) := by exact_mod_cast hs2
  calc lineTau (lineChart (lineConj a b C G)) * ((C 1 0 : ℂ) * lineTau (lineChart G) + C 1 1) *
        ((lineConj a b C G 2 2 : ℂ) * (G 2 2 : ℂ))
      = (lineTau (lineChart (lineConj a b C G)) * (lineConj a b C G 2 2 : ℂ)) *
          ((C 1 0 : ℂ) * (lineTau (lineChart G) * (G 2 2 : ℂ)) + C 1 1 * G 2 2) := by ring
    _ = ((lineConj a b C G 1 2 : ℂ) + Complex.I * ((C.det * s : ℝ) : ℂ)) *
          ((C 1 0 : ℂ) * ((G 1 2 : ℂ) + Complex.I * (s : ℂ)) + C 1 1 * G 2 2) := by rw [hT, hτ]
    _ = (lineConj a b C G 2 2 : ℂ) *
          ((C 0 0 : ℂ) * ((G 1 2 : ℂ) + Complex.I * (s : ℂ)) + C 0 1 * G 2 2) := by
        rw [e12, e22, hdC]
        push_cast
        linear_combination
          (((C 0 0 : ℂ) * C 1 1 - C 0 1 * C 1 0) * C 1 0 * Complex.I ^ 2) * hs2c +
          (((C 0 0 : ℂ) * C 1 1 - C 0 1 * C 1 0) * C 1 0 * ((G 1 1 : ℂ) * G 2 2 - G 1 2 * G 1 2)) *
            Complex.I_sq
    _ = ((C 0 0 : ℂ) * lineTau (lineChart G) + C 0 1) *
          ((lineConj a b C G 2 2 : ℂ) * (G 2 2 : ℂ)) := by
        rw [← hτ]; ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
