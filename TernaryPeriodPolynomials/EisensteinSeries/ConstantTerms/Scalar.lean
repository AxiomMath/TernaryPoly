module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.FormPullback

@[expose] public section


/-!
# Scalar parts of the pulled-back seeds (Appendix C.3, `ar:sec:series`)

The seed `ω_h = h(τ) 𝓑ⁿ β ∧ dτ` is the product of the scalar two-form `h(τ) β ∧ dτ`
(`seedForm0`) and the `n`-th power of the linear polynomial `𝓑` (`seedLinear`). Hence the
polynomial-valued pullback `formPullback Φ (seedForm n h)` is the scalar pullback times
`seedLinear (Φ p) ^ n`, and the scalar pullback obeys the chain rule.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### Scalar parts of the pulled-back seeds -/

/-- The scalar coefficient `h(τ)(β ∧ dτ)(eₐ, e_b)` of the seed, so that
`seedForm n h p a b = C (seedForm0 h p a b) * seedLinear p ^ n`. -/
def seedForm0 (h : ℂ → ℂ) (p : Fin 5 → ℝ) (a b : Fin 5) : ℂ :=
  h (seedTau p) * (seedBeta p a * seedDTau b - seedBeta p b * seedDTau a)

theorem seedForm_eq_C_mul (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (a b : Fin 5) :
    seedForm n h p a b = C (seedForm0 h p a b) * seedLinear p ^ n := rfl

/-- The pullback of a complex-valued coefficient two-form by `Φ`. -/
def scalarPullback (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) : ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    ((fderiv ℝ Φ p (Pi.single i 1) a * fderiv ℝ Φ p (Pi.single j 1) b : ℝ) : ℂ) * ω (Φ p) a b

theorem formPullback_seedForm (n : ℕ) (h : ℂ → ℂ) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (seedForm n h) p i j =
      C (scalarPullback Φ (seedForm0 h) p i j) * seedLinear (Φ p) ^ n := by
  unfold formPullback scalarPullback
  simp only [seedForm_eq_C_mul, map_sum, Finset.sum_mul, map_mul, mul_assoc]

/-- The algebraic core of the scalar chain rule. -/
theorem comp_alg_scalar (u u' : Fin 5 → ℝ) (v : Fin 5 → Fin 5 → ℝ)
    (W : Fin 5 → Fin 5 → ℂ) :
    ∑ c : Fin 5, ∑ d : Fin 5,
        (((∑ a, u a * v a c) * (∑ b, u' b * v b d) : ℝ) : ℂ) * W c d =
      ∑ a : Fin 5, ∑ b : Fin 5, ((u a * u' b : ℝ) : ℂ) *
        ∑ c : Fin 5, ∑ d : Fin 5, ((v a c * v b d : ℝ) : ℂ) * W c d := by
  have e1 : ∀ c d : Fin 5, ((((∑ a, u a * v a c) * (∑ b, u' b * v b d) : ℝ)) : ℂ) * W c d =
      ∑ a : Fin 5, ∑ b : Fin 5, ((u a * u' b : ℝ) : ℂ) * (((v a c * v b d : ℝ) : ℂ) * W c d) := by
    intro c d
    rw [Finset.sum_mul_sum]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [e1, Finset.mul_sum]
  calc ∑ c : Fin 5, ∑ d : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5, ((u a * u' b : ℝ) : ℂ) *
        (((v a c * v b d : ℝ) : ℂ) * W c d)
      = ∑ c : Fin 5, ∑ a : Fin 5, ∑ d : Fin 5, ∑ b : Fin 5, ((u a * u' b : ℝ) : ℂ) *
        (((v a c * v b d : ℝ) : ℂ) * W c d) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5, ∑ b : Fin 5, ((u a * u' b : ℝ) : ℂ) *
        (((v a c * v b d : ℝ) : ℂ) * W c d) := Finset.sum_comm
    _ = ∑ a : Fin 5, ∑ c : Fin 5, ∑ b : Fin 5, ∑ d : Fin 5, ((u a * u' b : ℝ) : ℂ) *
        (((v a c * v b d : ℝ) : ℂ) * W c d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5, ((u a * u' b : ℝ) : ℂ) *
        (((v a c * v b d : ℝ) : ℂ) * W c d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem scalarPullback_comp (Φ₁ Φ₂ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ) (p : Fin 5 → ℝ)
    (h₁ : DifferentiableAt ℝ Φ₁ p) (h₂ : DifferentiableAt ℝ Φ₂ (Φ₁ p)) (i j : Fin 5) :
    scalarPullback (Φ₂ ∘ Φ₁) ω p i j = scalarPullback Φ₁ (scalarPullback Φ₂ ω) p i j := by
  have hD : ∀ (i c : Fin 5), fderiv ℝ (Φ₂ ∘ Φ₁) p (Pi.single i 1) c =
      ∑ a : Fin 5, fderiv ℝ Φ₁ p (Pi.single i 1) a * fderiv ℝ Φ₂ (Φ₁ p) (Pi.single a 1) c := by
    intro i c
    rw [fderiv_comp p h₂ h₁, ContinuousLinearMap.comp_apply]
    exact linear_apply_eq_sum (fderiv ℝ Φ₂ (Φ₁ p)) _ c
  unfold scalarPullback
  simp only [hD, Function.comp_apply]
  exact comp_alg_scalar (fun a => fderiv ℝ Φ₁ p (Pi.single i 1) a)
    (fun b => fderiv ℝ Φ₁ p (Pi.single j 1) b)
    (fun a c => fderiv ℝ Φ₂ (Φ₁ p) (Pi.single a 1) c) (fun c d => ω (Φ₂ (Φ₁ p)) c d)

/-- Crude bound of a scalar pullback. -/
theorem norm_scalarPullback_le (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) (N W : ℝ)
    (hN : ∀ c, |fderiv ℝ Φ p (Pi.single i 1) c| ≤ N ∧ |fderiv ℝ Φ p (Pi.single j 1) c| ≤ N)
    (hW : ∀ a b, ‖ω (Φ p) a b‖ ≤ W) :
    ‖scalarPullback Φ ω p i j‖ ≤ 25 * (N * N * W) := by
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN 0).1
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 0)
  unfold scalarPullback
  refine (norm_sum_le _ _).trans ?_
  have : ∀ a : Fin 5, ‖∑ b : Fin 5, ((fderiv ℝ Φ p (Pi.single i 1) a * fderiv ℝ Φ p (Pi.single j 1) b : ℝ) : ℂ)
      * ω (Φ p) a b‖ ≤ 5 * (N * N * W) := by
    intro a
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : Fin 5, ‖((fderiv ℝ Φ p (Pi.single i 1) a * fderiv ℝ Φ p (Pi.single j 1) b : ℝ) : ℂ)
          * ω (Φ p) a b‖ ≤ ∑ b : Fin 5, N * N * W := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (mul_le_mul (hN a).1 (hN b).2 (abs_nonneg _) hN0) (hW a b)
            (norm_nonneg _) (mul_nonneg hN0 hN0)
      _ = 5 * (N * N * W) := by simp
  calc ∑ a : Fin 5, ‖∑ b : Fin 5, ((fderiv ℝ Φ p (Pi.single i 1) a * fderiv ℝ Φ p (Pi.single j 1) b : ℝ) : ℂ)
        * ω (Φ p) a b‖ ≤ ∑ a : Fin 5, 5 * (N * N * W) := Finset.sum_le_sum fun a _ => this a
    _ = 25 * (N * N * W) := by simp; ring

end TernaryPeriodPolynomials.Argument.ConvergenceC4
