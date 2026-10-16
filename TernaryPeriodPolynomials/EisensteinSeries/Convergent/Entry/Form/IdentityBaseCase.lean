module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityBase
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# The form identity at the base point

`lineTangent_one`: the line-chart tangent at the identity is `(p₀₁, p₀₂, p₁₂, (p₁₁-p₂₂)/2, p₀₀/2)` for `p = V + Vᵀ`;
`lineFrameCoefficient_one`: hence the line seed's frame coefficient at `g = 1` is
`C(h(i) · linePair(V+Vᵀ, W+Wᵀ)) · (iZ - Y)ⁿ`.  `base_form_identity_coeff` combines it with `base_integral_coeff`:
for `h` holomorphic with the cusp decay and `n ≥ 3`, every polynomial coefficient of the seed's frame coefficient
at `L_{s,t}` is integrable over `ℝ²` and
`∫_{ℝ²} coeff_m ω̃_h(L_{s,t})(V,W) = c_∞ · coeff_m σ̃_h(1)(V,W)`, `c_∞ = -2πi/(n+1)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex MvPolynomial MeasureTheory TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

theorem gramCurve_one_deriv (V : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    HasDerivAt (fun ε => gramCurve 1 V ε i j) ((V + V.transpose) i j) 0 := by
  simpa using hasDerivAt_gramCurve 1 V i j

theorem gramCurve_one_zero (V : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    gramCurve 1 V 0 i j = if i = j then 1 else 0 := by
  rw [gramCurve_zero]; simp [Matrix.one_apply]

/-- The line-chart tangent at the identity: `dL_1 V = (p₀₁, p₀₂, p₁₂, (p₁₁ - p₂₂)/2, p₀₀/2)` for `p = V + Vᵀ`. -/
theorem lineTangent_one (V : Matrix (Fin 3) (Fin 3) ℝ) :
    lineTangent 1 V = ![(V + V.transpose) 0 1, (V + V.transpose) 0 2, (V + V.transpose) 1 2,
      ((V + V.transpose) 1 1 - (V + V.transpose) 2 2) / 2, (V + V.transpose) 0 0 / 2] := by
  set p := V + V.transpose with hp
  have hG := gramCurve_one_deriv V
  have h0 := gramCurve_one_zero V
  have e00 := h0 0 0
  have e01 := h0 0 1
  have e02 := h0 0 2
  have e10 := h0 1 0
  have e11 := h0 1 1
  have e12 := h0 1 2
  have e20 := h0 2 0
  have e21 := h0 2 1
  have e22 := h0 2 2
  simp at e00 e01 e02 e10 e11 e12 e20 e21 e22
  have hdet := ((hG 1 1).mul (hG 2 2)).sub ((hG 1 2).mul (hG 2 1))
  have hdet0 : (((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
        (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1) 0 ≠ 0 := by
    simp [e11, e22, e12, e21]
  have c0 : deriv (fun ε => lineChart (gramCurve 1 V ε) 0) 0 = p 0 1 := by
    have hN := ((hG 0 1).mul (hG 2 2)).sub ((hG 0 2).mul (hG 2 1))
    have hdiv := hN.div hdet hdet0
    have hfun : (fun ε => lineChart (gramCurve 1 V ε) 0) =
        ((((fun ε => gramCurve 1 V ε 0 1) * fun ε => gramCurve 1 V ε 2 2) -
          (fun ε => gramCurve 1 V ε 0 2) * fun ε => gramCurve 1 V ε 2 1) /
          (((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
            (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1)) := by
      funext ε; simp [lineChart]
    rw [hfun]
    refine (hdiv.congr_deriv ?_).deriv
    simp [e01, e02, e11, e12, e21, e22, hp]
  have c1 : deriv (fun ε => lineChart (gramCurve 1 V ε) 1) 0 = p 0 2 := by
    have hN := ((hG 0 2).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 2))
    have hdiv := hN.div hdet hdet0
    have hfun : (fun ε => lineChart (gramCurve 1 V ε) 1) =
        ((((fun ε => gramCurve 1 V ε 0 2) * fun ε => gramCurve 1 V ε 1 1) -
          (fun ε => gramCurve 1 V ε 0 1) * fun ε => gramCurve 1 V ε 1 2) /
          (((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
            (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1)) := by
      funext ε; simp [lineChart]
    rw [hfun]
    refine (hdiv.congr_deriv ?_).deriv
    simp [e01, e02, e11, e12, e21, e22, hp]
  have c2 : deriv (fun ε => lineChart (gramCurve 1 V ε) 2) 0 = p 1 2 := by
    have hdiv := (hG 1 2).div (hG 2 2) (by simp [e22])
    have hfun : (fun ε => lineChart (gramCurve 1 V ε) 2) =
        ((fun ε => gramCurve 1 V ε 1 2) / fun ε => gramCurve 1 V ε 2 2) := by
      funext ε; simp [lineChart]
    rw [hfun]
    refine (hdiv.congr_deriv ?_).deriv
    simp [e12, e22, hp]
  have c3 : deriv (fun ε => lineChart (gramCurve 1 V ε) 3) 0 = (p 1 1 - p 2 2) / 2 := by
    have hpos : (((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
        (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1) 0 ≠ 0 := hdet0
    have hs := hdet.sqrt hpos
    have hdiv := hs.div (hG 2 2) (by simp [e22])
    have hfun : (fun ε => lineChart (gramCurve 1 V ε) 3) =
        ((fun ε => Real.sqrt ((((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
          (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1) ε)) /
          fun ε => gramCurve 1 V ε 2 2) := by
      funext ε; simp [lineChart]
    rw [hfun]
    refine (hdiv.congr_deriv ?_).deriv
    simp [e11, e12, e21, e22, hp]
    ring
  have c4 : deriv (fun ε => lineChart (gramCurve 1 V ε) 4) 0 = p 0 0 / 2 := by
    have hN1 := ((hG 0 1).mul (hG 2 2)).sub ((hG 0 2).mul (hG 2 1))
    have hN2 := ((hG 0 2).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 2))
    have hq := (((hN1.mul (hG 0 1)).add (hN2.mul (hG 0 2)))).div hdet hdet0
    have hE := (hG 0 0).sub hq
    have hE0 : (fun ε => gramCurve 1 V ε 0 0) 0 - ((((((fun ε => gramCurve 1 V ε 0 1) *
        fun ε => gramCurve 1 V ε 2 2) - (fun ε => gramCurve 1 V ε 0 2) * fun ε => gramCurve 1 V ε 2 1) *
        (fun ε => gramCurve 1 V ε 0 1)) + (((fun ε => gramCurve 1 V ε 0 2) *
        fun ε => gramCurve 1 V ε 1 1) - (fun ε => gramCurve 1 V ε 0 1) *
        fun ε => gramCurve 1 V ε 1 2) * (fun ε => gramCurve 1 V ε 0 2)) /
        (((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
        (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1)) 0 ≠ 0 := by
      simp [e00, e01, e02, e11, e12, e21, e22]
    have hs := hE.sqrt hE0
    have hfun : (fun ε => lineChart (gramCurve 1 V ε) 4) =
        fun ε => Real.sqrt (((fun ε => gramCurve 1 V ε 0 0) -
          ((((((fun ε => gramCurve 1 V ε 0 1) * fun ε => gramCurve 1 V ε 2 2) -
          (fun ε => gramCurve 1 V ε 0 2) * fun ε => gramCurve 1 V ε 2 1) *
          (fun ε => gramCurve 1 V ε 0 1)) + (((fun ε => gramCurve 1 V ε 0 2) *
          fun ε => gramCurve 1 V ε 1 1) - (fun ε => gramCurve 1 V ε 0 1) *
          fun ε => gramCurve 1 V ε 1 2) * (fun ε => gramCurve 1 V ε 0 2)) /
          (((fun ε => gramCurve 1 V ε 1 1) * fun ε => gramCurve 1 V ε 2 2) -
          (fun ε => gramCurve 1 V ε 1 2) * fun ε => gramCurve 1 V ε 2 1))) ε) := by
      funext ε; simp [lineChart]
    rw [hfun]
    refine (hs.congr_deriv ?_).deriv
    simp [e00, e01, e02, e11, e12, e21, e22, hp]
  funext a
  unfold lineTangent
  fin_cases a
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4


theorem lineChart_one_gram :
    lineChart ((1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose) =
      ![0, 0, 0, 1, 1] := by
  rw [Matrix.transpose_one, mul_one]
  funext a
  fin_cases a <;> simp [lineChart]

/-- **The line seed's frame coefficient at the base point, for arbitrary directions.** -/
theorem lineFrameCoefficient_one (n : ℕ) (h : ℂ → ℂ) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    lineFrameCoefficient (lineSeedForm n h) 1 V W =
      C (h Complex.I * linePair (V + V.transpose) (W + W.transpose)) *
        (C Complex.I * X 2 - X 1) ^ n := by
  rw [lineFrameCoefficient, inv_one, rho_one, lineChart_one_gram]
  have hτ : lineTau ![0, 0, 0, 1, 1] = Complex.I := by simp [lineTau]
  have hsum : ∀ x y : Fin 5 → Fin 5 → ℂ, ∀ P : MvPolynomial (Fin 3) ℂ,
      ∑ a, ∑ b, (C (x a b) : MvPolynomial (Fin 3) ℂ) * (C (y a b) * P) = C (∑ a, ∑ b, x a b * y a b) * P := by
    intro x y P
    simp only [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum]
  simp only [lineSeedForm, hτ]
  rw [hsum]
  congr 2
  simp only [lineTangent_one, Fin.sum_univ_five, seedDTau, linePair,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring_nf


theorem coeff_lineForm_pow (n : ℕ) (m : Fin 3 →₀ ℕ) (hm : m.sum (fun _ k => k) = n) :
    ((C Complex.I * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).coeff m =
      (m.multinomial : ℂ) * xiPoly m 0 := by
  have hform : (C Complex.I * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) =
      C 0 * X 0 + C (-1) * X 1 + C Complex.I * X 2 := by
    simp; ring
  rw [hform, coeff_linForm_pow, ite_eq_left hm, xiPoly_zero]
  by_cases h0 : m 0 = 0
  · simp [h0]
  · simp [h0, zero_pow h0]

/-- **The base-point form identity, coefficientwise** (`g = 1`): for `h` holomorphic with the cusp decay and
`n ≥ 3`, `∫_{ℝ²} coeff_m ω̃_h(L_{s,t})(V,W) = c_∞ · coeff_m σ̃_h(1)(V,W)` with `c_∞ = -2πi/(n+1)`. -/
theorem base_form_identity_coeff (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (m : Fin 3 →₀ ℕ)
    (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    Integrable (fun st : ℝ × ℝ =>
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m) ∧
    ∫ st : ℝ × ℝ,
        (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        (lineFrameCoefficient (lineSeedForm n h) 1 V W).coeff m := by
  obtain ⟨hint, hval⟩ := base_integral_coeff n hn h hh M hM m hm V W
  refine ⟨hint, ?_⟩
  rw [hval, lineFrameCoefficient_one, MvPolynomial.coeff_C_mul, coeff_lineForm_pow n m hm]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
