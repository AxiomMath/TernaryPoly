module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Pi

@[expose] public section


/-!
# Chain rule for the coefficient-matrix pullback `formPullback`

Paper: §C.3. For differentiable
maps `Φ₁, Φ₂` of the plane-coordinate space, the pullback of a polynomial-valued two-form by the
composite `Φ₂ ∘ Φ₁` is the pullback by `Φ₁` of the pullback by `Φ₂`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- A linear map on `Fin 5 → ℝ` applied to a vector is the sum of its values on the basis. -/
theorem linear_apply_eq_sum (L : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)) (v : Fin 5 → ℝ) (c : Fin 5) :
    L v c = ∑ a : Fin 5, v a * L (Pi.single a 1) c := by
  have e : ∀ x : Fin 5, (fun j : Fin 5 => if x = j then (1 : ℝ) else 0) = Pi.single x 1 := by
    intro x; funext j; simp [Pi.single_apply, eq_comm]
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]

/-- The algebraic core of the chain rule: reassociating a double sum of products of sums. -/
theorem comp_alg (u u' : Fin 5 → ℝ) (v : Fin 5 → Fin 5 → ℝ)
    (W : Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) :
    ∑ c : Fin 5, ∑ d : Fin 5,
        C ((((∑ a, u a * v a c) * (∑ b, u' b * v b d) : ℝ) : ℂ)) * W c d =
      ∑ a : Fin 5, ∑ b : Fin 5, C ((u a * u' b : ℝ) : ℂ) *
        ∑ c : Fin 5, ∑ d : Fin 5, C ((v a c * v b d : ℝ) : ℂ) * W c d := by
  have e1 : ∀ c d : Fin 5, (C (((((∑ a, u a * v a c) * (∑ b, u' b * v b d) : ℝ)) : ℂ)) *
      W c d : MvPolynomial (Fin 3) ℂ) =
      ∑ a : Fin 5, ∑ b : Fin 5, C ((u a * u' b : ℝ) : ℂ) * (C ((v a c * v b d : ℝ) : ℂ) * W c d) := by
    intro c d
    rw [Finset.sum_mul_sum]
    push_cast
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul]
    ring
  simp_rw [e1, Finset.mul_sum]
  calc ∑ c : Fin 5, ∑ d : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5, C ((u a * u' b : ℝ) : ℂ) *
        (C ((v a c * v b d : ℝ) : ℂ) * W c d)
      = ∑ c : Fin 5, ∑ a : Fin 5, ∑ d : Fin 5, ∑ b : Fin 5, C ((u a * u' b : ℝ) : ℂ) *
        (C ((v a c * v b d : ℝ) : ℂ) * W c d) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5, ∑ b : Fin 5, C ((u a * u' b : ℝ) : ℂ) *
        (C ((v a c * v b d : ℝ) : ℂ) * W c d) := Finset.sum_comm
    _ = ∑ a : Fin 5, ∑ c : Fin 5, ∑ b : Fin 5, ∑ d : Fin 5, C ((u a * u' b : ℝ) : ℂ) *
        (C ((v a c * v b d : ℝ) : ℂ) * W c d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5, C ((u a * u' b : ℝ) : ℂ) *
        (C ((v a c * v b d : ℝ) : ℂ) * W c d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem formPullback_comp (Φ₁ Φ₂ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (p : Fin 5 → ℝ)
    (h₁ : DifferentiableAt ℝ Φ₁ p) (h₂ : DifferentiableAt ℝ Φ₂ (Φ₁ p)) (i j : Fin 5) :
    formPullback (Φ₂ ∘ Φ₁) ω p i j = formPullback Φ₁ (formPullback Φ₂ ω) p i j := by
  have hD : ∀ (i c : Fin 5), fderiv ℝ (Φ₂ ∘ Φ₁) p (Pi.single i 1) c =
      ∑ a : Fin 5, fderiv ℝ Φ₁ p (Pi.single i 1) a * fderiv ℝ Φ₂ (Φ₁ p) (Pi.single a 1) c := by
    intro i c
    rw [fderiv_comp p h₂ h₁, ContinuousLinearMap.comp_apply]
    exact linear_apply_eq_sum (fderiv ℝ Φ₂ (Φ₁ p)) _ c
  unfold formPullback
  simp only [hD, Function.comp_apply]
  exact comp_alg (fun a => fderiv ℝ Φ₁ p (Pi.single i 1) a) (fun b => fderiv ℝ Φ₁ p (Pi.single j 1) b)
    (fun a c => fderiv ℝ Φ₂ (Φ₁ p) (Pi.single a 1) c)
    (fun c d => ω (Φ₂ (Φ₁ p)) c d)

end TernaryPeriodPolynomials.Argument.ConvergenceC4
