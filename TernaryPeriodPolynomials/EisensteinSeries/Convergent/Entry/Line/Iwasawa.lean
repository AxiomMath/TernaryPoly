module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# The line-parabolic Iwasawa decomposition (R4 of the ML4b reduction)

The plane Levi element `diag(A, t)` (`planeLevi`), the line-parabolic element `[[a, bᵀ], [0, C]]`
(`lineParabolic`) and the line-radical translation `u(a, b)` (`radicalTranslate`), as real `3 × 3`
matrices; the two matrix identities `L_{s,t} u(a,b) = L_{s+a,t+b}` and
`L_{s,t} [[a, bᵀ], [0, C]] = diag(C, a) L_{s',t'}` behind the change of variables of the entry integral;
and the Iwasawa decomposition `g = q k` of every `g` with `0 < det g` with `q` in the line parabolic
(`a > 0`, `det C > 0`) and `k` orthogonal (`exists_lineParabolic_mul_orthogonal`), obtained from an upper
triangular Cholesky factor of `g gᵀ` (`exists_upperCholesky`). Step R4 of K's reduction of the form
identity of Appendix C.5 (`ar:sec:real`) to the base point.

Written by Claude Opus 5.5.
-/

open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument

/-- The plane Levi element `diag(A, t)`. -/
def planeLevi (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, t]

/-- The element `[[a, bᵀ], [0, C]]` of the line parabolic. -/
def lineParabolic (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, b 0, b 1; 0, C 0 0, C 0 1; 0, C 1 0, C 1 1]

/-- The line-radical translation `u(a, b)`. -/
def radicalTranslate (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, a, b; 0, 1, 0; 0, 0, 1]

/-- `L_{s,t} u(a,b) = L_{s+a,t+b}`. -/
theorem entryFrame_mul_radicalTranslate (s t a b : ℝ) :
    entryFrame s t * radicalTranslate a b = entryFrame (s + a) (t + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryFrame, radicalTranslate, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- `L_{s,t} [[a, bᵀ], [0, C]] = diag(C, a) L_{s',t'}` with
`(s', t') = ((b₀ + C₀₀ s + C₁₀ t) / a, (b₁ + C₀₁ s + C₁₁ t) / a)`. -/
theorem entryFrame_mul_lineParabolic (s t a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : a ≠ 0) :
    entryFrame s t * lineParabolic a b C =
      planeLevi C a *
        entryFrame ((b 0 + C 0 0 * s + C 1 0 * t) / a) ((b 1 + C 0 1 * s + C 1 1 * t) / a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryFrame, lineParabolic, planeLevi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp

/-- **Upper triangular Cholesky factor** of a symmetric `3 × 3` matrix with positive trailing principal
minors: `P = Q Qᵀ` with `Q` upper triangular with positive diagonal. -/
theorem exists_upperCholesky (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : Pᵀ = P)
    (hs : 0 < P 2 2) (hD : 0 < P 1 1 * P 2 2 - P 1 2 ^ 2) (hdet : 0 < P.det) :
    ∃ a b0 b1 c00 c01 c11 : ℝ, 0 < a ∧ 0 < c00 ∧ 0 < c11 ∧
      !![a, b0, b1; 0, c00, c01; 0, 0, c11] * (!![a, b0, b1; 0, c00, c01; 0, 0, c11])ᵀ = P := by
  have hsym : ∀ i j, P j i = P i j := fun i j => by
    simpa using congrFun (congrFun hP i) j
  have hDs : 0 < (P 1 1 * P 2 2 - P 1 2 ^ 2) / P 2 2 := div_pos hD hs
  have hα : 0 < P.det / (P 1 1 * P 2 2 - P 1 2 ^ 2) := div_pos hdet hD
  obtain ⟨c11, c11pos, c11sq⟩ : ∃ c : ℝ, 0 < c ∧ c ^ 2 = P 2 2 :=
    ⟨_, Real.sqrt_pos.mpr hs, Real.sq_sqrt hs.le⟩
  obtain ⟨c00, c00pos, c00sq⟩ : ∃ c : ℝ, 0 < c ∧ c ^ 2 = (P 1 1 * P 2 2 - P 1 2 ^ 2) / P 2 2 :=
    ⟨_, Real.sqrt_pos.mpr hDs, Real.sq_sqrt hDs.le⟩
  obtain ⟨a, apos, asq⟩ : ∃ c : ℝ, 0 < c ∧ c ^ 2 = P.det / (P 1 1 * P 2 2 - P 1 2 ^ 2) :=
    ⟨_, Real.sqrt_pos.mpr hα, Real.sq_sqrt hα.le⟩
  refine ⟨a, (P 0 1 - P 0 2 / c11 * (P 1 2 / c11)) / c00, P 0 2 / c11, c00, P 1 2 / c11, c11,
    apos, c00pos, c11pos, ?_⟩
  have hdetP := Matrix.det_fin_three P
  have e10 := hsym 0 1
  have e20 := hsym 0 2
  have e21 := hsym 1 2
  have c11ne := c11pos.ne'
  have c00ne := c00pos.ne'
  have hsne := hs.ne'
  have hDne := hD.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  · rw [show c11 ^ 4 = (c11 ^ 2) ^ 2 by ring, c11sq, c00sq, asq, hdetP, e10, e20, e21]
    field_simp
    ring
  · ring
  · rw [e10]; ring
  · rw [c00sq, c11sq]; field_simp; ring
  · exact e20.symm
  · exact e21.symm
  · exact c11sq

private theorem gram_apply (g : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (g * gᵀ) i j = g i 0 * g j 0 + g i 1 * g j 1 + g i 2 * g j 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- **R4 (Iwasawa decomposition for the line parabolic).** Every `g` with `0 < det g` is `q k` with
`q = [[a, bᵀ], [0, C]]`, `a > 0`, `det C > 0`, and `k` orthogonal. -/
theorem exists_lineParabolic_mul_orthogonal (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : 0 < g.det) :
    ∃ (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ),
      0 < a ∧ 0 < C.det ∧ k * k.transpose = 1 ∧ g = lineParabolic a b C * k := by
  have hdg := Matrix.det_fin_three g
  have hs : 0 < (g * gᵀ) 2 2 := by
    rw [gram_apply]
    by_contra hle
    rw [not_lt] at hle
    have h0 : g 2 0 ^ 2 = 0 := by linarith [sq_nonneg (g 2 0), sq_nonneg (g 2 1), sq_nonneg (g 2 2)]
    have h1 : g 2 1 ^ 2 = 0 := by linarith [sq_nonneg (g 2 0), sq_nonneg (g 2 1), sq_nonneg (g 2 2)]
    have h2 : g 2 2 ^ 2 = 0 := by linarith [sq_nonneg (g 2 0), sq_nonneg (g 2 1), sq_nonneg (g 2 2)]
    simp only [pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h0 h1 h2
    rw [hdg, h0, h1, h2] at hg
    simp at hg
  have hD : 0 < (g * gᵀ) 1 1 * (g * gᵀ) 2 2 - (g * gᵀ) 1 2 ^ 2 := by
    have e : (g * gᵀ) 1 1 * (g * gᵀ) 2 2 - (g * gᵀ) 1 2 ^ 2 =
        (g 1 1 * g 2 2 - g 1 2 * g 2 1) ^ 2 + (g 1 0 * g 2 2 - g 1 2 * g 2 0) ^ 2 +
          (g 1 0 * g 2 1 - g 1 1 * g 2 0) ^ 2 := by
      simp only [gram_apply]; ring
    rw [e]
    by_contra hle
    rw [not_lt] at hle
    have h0 : (g 1 1 * g 2 2 - g 1 2 * g 2 1) ^ 2 = 0 := by
      linarith [sq_nonneg (g 1 1 * g 2 2 - g 1 2 * g 2 1), sq_nonneg (g 1 0 * g 2 2 - g 1 2 * g 2 0),
        sq_nonneg (g 1 0 * g 2 1 - g 1 1 * g 2 0)]
    have h1 : (g 1 0 * g 2 2 - g 1 2 * g 2 0) ^ 2 = 0 := by
      linarith [sq_nonneg (g 1 1 * g 2 2 - g 1 2 * g 2 1), sq_nonneg (g 1 0 * g 2 2 - g 1 2 * g 2 0),
        sq_nonneg (g 1 0 * g 2 1 - g 1 1 * g 2 0)]
    have h2 : (g 1 0 * g 2 1 - g 1 1 * g 2 0) ^ 2 = 0 := by
      linarith [sq_nonneg (g 1 1 * g 2 2 - g 1 2 * g 2 1), sq_nonneg (g 1 0 * g 2 2 - g 1 2 * g 2 0),
        sq_nonneg (g 1 0 * g 2 1 - g 1 1 * g 2 0)]
    simp only [pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h0 h1 h2
    have : g.det = 0 := by
      rw [hdg]
      linear_combination g 0 0 * h0 - g 0 1 * h1 + g 0 2 * h2
    linarith
  have hdetP : 0 < (g * gᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    positivity
  obtain ⟨a, b0, b1, c00, c01, c11, ha, hc00, hc11, hQ⟩ :=
    exists_upperCholesky (g * gᵀ) (by rw [Matrix.transpose_mul, Matrix.transpose_transpose]) hs hD
      hdetP
  set Q : Matrix (Fin 3) (Fin 3) ℝ := !![a, b0, b1; 0, c00, c01; 0, 0, c11] with hQdef
  have hQL : Q = lineParabolic a ![b0, b1] !![c00, c01; 0, c11] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hunit : IsUnit Q.det := by
    rw [Matrix.det_fin_three]
    simp only [hQdef, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    simp only [isUnit_iff_ne_zero]
    ring_nf
    positivity
  refine ⟨a, ![b0, b1], !![c00, c01; 0, c11], Q⁻¹ * g, ha, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    nlinarith
  · rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc,
      Matrix.mul_assoc Q⁻¹ g, ← hQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mul, Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])]
  · rw [← hQL, Matrix.mul_nonsing_inv_cancel_left _ _ hunit]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
