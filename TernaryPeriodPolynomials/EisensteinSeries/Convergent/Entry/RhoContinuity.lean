module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalAnalytic
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Seed

@[expose] public section


/-!
# Continuity of the coefficient action `ρ(g)` in `g`

The coefficients of a linear substitution depend continuously on the substituting matrix
(`continuousOn_coeff_substitute`), hence the coefficients of `ρ(g) Q` depend continuously on `g` on the invertible
locus (`continuousOn_rho_coeff`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- Coefficients of a linear substitution depend continuously on the substituting matrix (continuity version
of `contDiff_coeff_substitute`, on an arbitrary set). -/
theorem continuousOn_coeff_substitute {E : Type*} [TopologicalSpace E] {S : Set E}
    (M : E → Matrix (Fin 3) (Fin 3) ℂ) (hM : ∀ i j, ContinuousOn (fun x => M x i j) S)
    (F : Poly) : ∀ m : Fin 3 →₀ ℕ, ContinuousOn (fun x => (substitute (M x) F).coeff m) S := by
  have hX : ∀ (f : E → Poly), (∀ m, ContinuousOn (fun x => (f x).coeff m) S) → ∀ (i : Fin 3) (m : Fin 3 →₀ ℕ),
      ContinuousOn (fun x => (f x * MvPolynomial.X i).coeff m) S := by
    intro f hf i m
    classical
    by_cases h : i ∈ m.support
    · have e : (fun x => (f x * MvPolynomial.X i).coeff m) = fun x => (f x).coeff (m - Finsupp.single i 1) := by
        funext x
        rw [coeff_mul_X', ite_eq_left h]
      rw [e]
      exact hf _
    · have e : (fun x => (f x * MvPolynomial.X i).coeff m) = fun _ => (0 : ℂ) := by
        funext x
        rw [coeff_mul_X', ite_eq_right h]
      rw [e]
      exact continuousOn_const
  induction F using MvPolynomial.induction_on with
  | C a =>
    intro m
    have h : ∀ x, substitute (M x) (MvPolynomial.C a) = MvPolynomial.C a := fun x => by simp [substitute]
    simp only [h]
    exact continuousOn_const
  | add p q hp hq =>
    intro m
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hp m).add (hq m)
  | mul_X p i hp =>
    intro m
    have h : ∀ x, (substitute (M x) (p * MvPolynomial.X i)).coeff m =
        M x i 0 * (substitute (M x) p * MvPolynomial.X 0).coeff m +
          M x i 1 * (substitute (M x) p * MvPolynomial.X 1).coeff m +
            M x i 2 * (substitute (M x) p * MvPolynomial.X 2).coeff m := by
      intro x
      have e : substitute (M x) (p * MvPolynomial.X i) =
          MvPolynomial.C (M x i 0) * (substitute (M x) p * MvPolynomial.X 0) +
            MvPolynomial.C (M x i 1) * (substitute (M x) p * MvPolynomial.X 1) +
            MvPolynomial.C (M x i 2) * (substitute (M x) p * MvPolynomial.X 2) := by
        rw [map_mul, substitute_X, linearForm, Fin.sum_univ_three]
        ring
      rw [e, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_C_mul, coeff_C_mul]
    simp only [h]
    exact (((hM i 0).mul (hX _ hp 0 m)).add ((hM i 1).mul (hX _ hp 1 m))).add
      ((hM i 2).mul (hX _ hp 2 m))

theorem rho_eq_C_mul_substitute (g : Matrix (Fin 3) (Fin 3) ℝ) (Q : Poly) :
    TernaryPeriodPolynomials.Argument.SeedC3.rho g Q =
      MvPolynomial.C ((g.det⁻¹ : ℝ) : ℂ) *
        substitute ((g⁻¹).map (algebraMap ℝ ℂ)) Q := rfl

theorem continuousOn_matInv : ContinuousOn (fun q : Matrix (Fin 3) (Fin 3) ℝ => q⁻¹)
    {q | q.det ≠ 0} := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hq

theorem continuousOn_rho_coeff (F : Poly) (m : Fin 3 →₀ ℕ) :
    ContinuousOn (fun q : Matrix (Fin 3) (Fin 3) ℝ =>
      (TernaryPeriodPolynomials.Argument.SeedC3.rho q F).coeff m) {q | q.det ≠ 0} := by
  simp only [rho_eq_C_mul_substitute, coeff_C_mul]
  refine ContinuousOn.mul ?_ ?_
  · refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact ((Continuous.matrix_det continuous_id).continuousOn).inv₀ (fun q hq => hq)
  · refine continuousOn_coeff_substitute _ (fun i j => ?_) F m
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    have h1 := continuousOn_matInv
    exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn h1)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
