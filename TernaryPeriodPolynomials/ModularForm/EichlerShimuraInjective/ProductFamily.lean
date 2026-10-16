module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Composition

@[expose] public section


/-!
# The holomorphic-times-antiholomorphic decomposition of `A`

`Aval_eq_holAnti`: `A = Σ uᵢ conj wᵢ` explicitly, and `∂_z A = |f|² (z - z̄)^{n+1}`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

/-- The index type of the holomorphic-times-antiholomorphic decomposition of the Petersson-type function. -/
abbrev ι0 (n : ℕ) := (Fin (n + 2) ⊕ Fin (n + 2)) ⊕ Unit

/-- The evaluation of a binary polynomial at `(z, 1)`. -/
def evalZ (P : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℂ := MvPolynomial.eval ![z, 1] P

theorem differentiable_evalZ (P : MvPolynomial (Fin 2) ℂ) : Differentiable ℂ (evalZ P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : evalZ (MvPolynomial.C a) = fun _ => a := by funext z; simp [evalZ]
    rw [e]; exact differentiable_const a
  | add p q hp hq =>
    have e : evalZ (p + q) = fun z => evalZ p z + evalZ q z := by funext z; simp [evalZ]
    rw [e]; exact hp.add hq
  | mul_X p i hp =>
    have e : evalZ (p * MvPolynomial.X i) = fun z => evalZ p z * (![z, 1] : Fin 2 → ℂ) i := by
      funext z; simp [evalZ]
    rw [e]
    refine hp.mul ?_
    fin_cases i
    · simp
    · simp

/-- The holomorphic factors. -/
def u0 (n : ℕ) (Gf : ℕ → ℂ → ℂ) : ι0 n → ℂ → ℂ
  | Sum.inl (Sum.inl j) => Gf j
  | _ => fun _ => 1

/-- The factors whose conjugates appear. -/
def w0 (n : ℕ) (f : ℂ → ℂ) (Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) : ι0 n → ℂ → ℂ
  | Sum.inl (Sum.inl j) => fun z => f z * (z ^ (n + 1 - j) * cc n j)
  | Sum.inl (Sum.inr j) => fun z => Gg j z * f z * (z ^ (n + 1 - j) * cc n j)
  | Sum.inr _ => fun z => f z * evalZ (MvPolynomial.map (starRingEnd ℂ) v) z

theorem Aval_eq_holAnti (n : ℕ) (f : ℂ → ℂ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    Aval n f Gf Gg v z = holAnti (u0 n Gf) (w0 n f Gg v) z := by
  unfold Aval Phi holAnti
  rw [Phi0_eq_sum]
  simp only [ι0, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, u0, w0]
  simp only [Fin.sum_univ_eq_sum_range (fun j => Gf j z * conj (f z * (z ^ (n + 1 - j) * cc n j))) (n + 2),
    Fin.sum_univ_eq_sum_range (fun j => 1 * conj (Gg j z * f z * (z ^ (n + 1 - j) * cc n j))) (n + 2)]
  have hv : conj (evalZ (MvPolynomial.map (starRingEnd ℂ) v) z) = MvPolynomial.eval ![conj z, 1] v := by
    unfold evalZ
    rw [eval_map_conj]
    simp only [Complex.conj_conj]
    have : (fun i => conj ((![z, 1] : Fin 2 → ℂ) i)) = ![conj z, 1] := by
      funext i; fin_cases i <;> simp
    rw [this]
  simp only [map_mul, conj_cc, map_pow, one_mul]
  rw [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hv]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, one_pow]
  ring


section Props

variable {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ} {v : MvPolynomial (Fin 2) ℂ}

theorem u0_diff (hGf : ∀ j z, 0 < z.im → HasDerivAt (Gf j) (f z * z ^ j) z) (i : ι0 n) :
    DifferentiableOn ℂ (u0 n Gf i) Uset := by
  rcases i with (j | j) | j
  · exact fun z hz => (hGf j z hz).differentiableAt.differentiableWithinAt
  · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem w0_diff (hf : DifferentiableOn ℂ f Uset)
    (hGg : ∀ j z, 0 < z.im → HasDerivAt (Gg j) (g z * z ^ j) z) (i : ι0 n) :
    DifferentiableOn ℂ (w0 n f Gg v i) Uset := by
  have hz : ∀ k : ℕ, DifferentiableOn ℂ (fun z : ℂ => z ^ k) Uset := fun k => (differentiable_id.pow k).differentiableOn
  rcases i with (j | j) | j
  · exact hf.mul ((hz _).mul (differentiableOn_const _))
  · have : DifferentiableOn ℂ (Gg j) Uset := fun z hz => (hGg j z hz).differentiableAt.differentiableWithinAt
    exact (this.mul hf).mul ((hz _).mul (differentiableOn_const _))
  · exact hf.mul (differentiable_evalZ _).differentiableOn

theorem holAntiD_w0 (hGf : ∀ j z, 0 < z.im → HasDerivAt (Gf j) (f z * z ^ j) z) {z : ℂ} (hz : 0 < z.im) :
    holAntiD (w0 n f Gg v) (fun i => deriv (u0 n Gf i)) z = (f z * conj (f z)) * (z - conj z) ^ (n + 1) := by
  unfold holAntiD
  simp only [ι0, Fintype.sum_sum_type, Finset.univ_unique, u0, w0, deriv_const, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j => deriv (Gf j) z * conj (f z * (z ^ (n + 1 - j) * cc n j))) (n + 2)]
  rw [show z - conj z = z + -conj z by ring, add_pow, Finset.mul_sum]
  rw [show n + 1 + 1 = n + 2 by rfl]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(hGf j z hz).deriv]
  simp only [map_mul, conj_cc, map_pow]
  unfold cc
  rw [neg_pow]
  ring

end Props

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
