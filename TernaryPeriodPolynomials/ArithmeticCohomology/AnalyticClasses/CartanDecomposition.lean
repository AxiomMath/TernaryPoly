module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeInterface

@[expose] public section


/-!
# The Cartan decomposition of `SL₂^±(ℝ)`

Every real `2 × 2` matrix `m` with `|det m| = 1` factors as `k₁ · diag(eˢ, e⁻ˢ) · k₂` with `k₁` and
`k₂` orthogonal. For a rotation `r_θ` the inner product of the two columns of `m r_θ` changes sign
between `θ = 0` and `θ = π / 2`, so at some angle the columns `v₁, v₂` are orthogonal; then
`m r_θ = k₁ · diag(‖v₁‖, ‖v₂‖)` with `k₁` orthogonal, and `‖v₁‖ ‖v₂‖ = |det m| = 1`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

/-- The element of `SL₂^±(ℝ)` given by an orthogonal matrix. -/
def orthogonalLevi (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.transpose * A = 1) : unimodularLevi :=
  ⟨⟨A, A.transpose, (Matrix.mul_eq_one_comm_of_card_eq (Fin 2) (Fin 2) ℝ rfl).mp hA, hA⟩, by
    change |A.det| = 1
    have square := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at square
    rcases mul_self_eq_one_iff.mp square with h | h <;> simp [h]⟩

theorem orthogonalLevi_val (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.transpose * A = 1) :
    ((orthogonalLevi A hA : unimodularLevi) : BinaryRealGL).val = A := rfl

theorem isOrthogonalLevi_orthogonalLevi (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.transpose * A = 1) : IsOrthogonalLevi (orthogonalLevi A hA) := hA

/-- An angle at which the columns of `m r_θ` are orthogonal. -/
theorem exists_angle_columns_orthogonal (p q r t : ℝ) :
    ∃ θ : ℝ, (p * Real.cos θ + q * Real.sin θ) * (q * Real.cos θ - p * Real.sin θ) +
      (r * Real.cos θ + t * Real.sin θ) * (t * Real.cos θ - r * Real.sin θ) = 0 := by
  set g : ℝ → ℝ := fun θ => (p * Real.cos θ + q * Real.sin θ) * (q * Real.cos θ - p * Real.sin θ) +
    (r * Real.cos θ + t * Real.sin θ) * (t * Real.cos θ - r * Real.sin θ)
  have continuous : Continuous g := by fun_prop
  have start : g 0 = p * q + r * t := by simp [g]
  have finish : g (Real.pi / 2) = -(p * q + r * t) := by simp [g]; ring
  have zero_mem : (0 : ℝ) ∈ Set.uIcc (g 0) (g (Real.pi / 2)) := by
    rw [start, finish, Set.mem_uIcc]
    rcases le_total 0 (p * q + r * t) with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  obtain ⟨θ, -, hθ⟩ := intermediate_value_uIcc continuous.continuousOn zero_mem
  exact ⟨θ, hθ⟩

/-- **The Cartan decomposition.** Every element of `SL₂^±(ℝ)` is `k₁ · diag(eˢ, e⁻ˢ) · k₂` with
`k₁` and `k₂` orthogonal. -/
theorem cartan_decomposition (m : unimodularLevi) :
    ∃ (k₁ k₂ : unimodularLevi) (s : ℝ), IsOrthogonalLevi k₁ ∧ IsOrthogonalLevi k₂ ∧
      m = k₁ * diagonalFlow s * k₂ := by
  set M := (m : BinaryRealGL).val
  have hdet : |M.det| = 1 := m.property
  obtain ⟨θ, hθ⟩ := exists_angle_columns_orthogonal (M 0 0) (M 0 1) (M 1 0) (M 1 1)
  set p := M 0 0
  set q := M 0 1
  set r := M 1 0
  set t := M 1 1
  set c := Real.cos θ
  set d := Real.sin θ
  have hcd : c ^ 2 + d ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  set x₀ := p * c + q * d
  set x₁ := r * c + t * d
  set y₀ := q * c - p * d
  set y₁ := t * c - r * d
  have orthogonal : x₀ * y₀ + x₁ * y₁ = 0 := hθ
  have determinant : (x₀ * y₁ - x₁ * y₀) ^ 2 = 1 := by
    have expand : x₀ * y₁ - x₁ * y₀ = M.det * (c ^ 2 + d ^ 2) := by
      rw [Matrix.det_fin_two]; ring
    rw [expand, hcd, mul_one, ← sq_abs, hdet, one_pow]
  have lagrange : (x₀ ^ 2 + x₁ ^ 2) * (y₀ ^ 2 + y₁ ^ 2) = 1 := by
    rw [← determinant]
    linear_combination (x₀ * y₀ + x₁ * y₁) * orthogonal
  set a := Real.sqrt (x₀ ^ 2 + x₁ ^ 2)
  set b := Real.sqrt (y₀ ^ 2 + y₁ ^ 2)
  have ha : a ^ 2 = x₀ ^ 2 + x₁ ^ 2 := Real.sq_sqrt (by positivity)
  have hb : b ^ 2 = y₀ ^ 2 + y₁ ^ 2 := Real.sq_sqrt (by positivity)
  have hab : a * b = 1 := by
    rw [← Real.sqrt_mul (by positivity), lagrange, Real.sqrt_one]
  have a_pos : 0 < a := by
    by_contra hn
    have zero : a = 0 := le_antisymm (not_lt.mp hn) (Real.sqrt_nonneg _)
    rw [zero, zero_mul] at hab
    exact zero_ne_one hab
  have a_ne : a ≠ 0 := a_pos.ne'
  have b_ne : b ≠ 0 := by rintro h; rw [h, mul_zero] at hab; exact zero_ne_one hab
  set s := Real.log a
  have exp_s : Real.exp s = a := Real.exp_log a_pos
  have exp_neg : Real.exp (-s) = b := by
    rw [Real.exp_neg, exp_s]
    exact inv_eq_of_mul_eq_one_right hab
  set K₁ : Matrix (Fin 2) (Fin 2) ℝ := !![x₀ / a, y₀ / b; x₁ / a, y₁ / b]
  set K₂ : Matrix (Fin 2) (Fin 2) ℝ := !![c, d; -d, c]
  have hK₁ : K₁.transpose * K₁ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [K₁, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.one_apply_eq, Matrix.one_apply_ne,
        ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true]
    · rw [show x₀ / a * (x₀ / a) + x₁ / a * (x₁ / a) = (x₀ ^ 2 + x₁ ^ 2) / a ^ 2 by ring, ← ha,
        div_self (pow_ne_zero 2 a_ne)]
    · rw [show x₀ / a * (y₀ / b) + x₁ / a * (y₁ / b) = (x₀ * y₀ + x₁ * y₁) / (a * b) by ring,
        orthogonal, zero_div]
    · rw [show y₀ / b * (x₀ / a) + y₁ / b * (x₁ / a) = (x₀ * y₀ + x₁ * y₁) / (a * b) by ring,
        orthogonal, zero_div]
    · rw [show y₀ / b * (y₀ / b) + y₁ / b * (y₁ / b) = (y₀ ^ 2 + y₁ ^ 2) / b ^ 2 by ring, ← hb,
        div_self (pow_ne_zero 2 b_ne)]
  have hK₂ : K₂.transpose * K₂ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [K₂, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.one_apply_eq, Matrix.one_apply_ne,
        ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true]
    · linear_combination hcd
    · ring
    · ring
    · linear_combination hcd
  refine ⟨orthogonalLevi K₁ hK₁, orthogonalLevi K₂ hK₂, s, hK₁, hK₂, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change M = K₁ * !![Real.exp s, 0; 0, Real.exp (-s)] * K₂
  rw [exp_s, exp_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [K₁, K₂, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, add_zero, zero_add]
  all_goals
    rw [div_mul_cancel₀ _ a_ne, div_mul_cancel₀ _ b_ne]
    simp only [x₀, x₁, y₀, y₁, p, q, r, t]
  · linear_combination (-M 0 0) * hcd
  · linear_combination (-M 0 1) * hcd
  · linear_combination (-M 1 0) * hcd
  · linear_combination (-M 1 1) * hcd

end TernaryPeriodPolynomials.AnalyticClasses
