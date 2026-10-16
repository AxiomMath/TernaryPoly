module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KPrinted

@[expose] public section


/-!
# The orbit-seed series on the upper half plane

Paper: Appendix C.5.

For `τ` in the upper half plane the face point `x_τ = (0, 0, -Re τ, Im τ)` has `τ_{x_τ} = τ`, so the `Yⁿ`
coefficient of the radical average at the pair `(0, 2)` is the series of the orbit seeds at `τ`. This file proves:

* `summable_orbitSeed`: `Σ_o ‖orbitSeed_o τ‖` converges for every `τ` with `Im τ > 0` (`n ≥ 4`);
* `lineA1K_term`, `summable_Tinf`: the orbit terms of `lineA1K` are the `Tinf` terms, absolutely summable.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.FormClassK
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Series

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The face point `x_τ = (0, 0, -Re τ, Im τ)` whose `τ_x` is `τ`. -/
def facePt (τ : ℂ) : Face := ![0, 0, -τ.re, τ.im]

theorem facePt_mem {τ : ℂ} (hτ : 0 < τ.im) : facePt τ ∈ faceSet := by
  show (0 : ℝ) < facePt τ 3
  simpa [facePt] using hτ

theorem facePt_tau (τ : ℂ) :
    ((-(facePt τ 2) : ℝ) : ℂ) + Complex.I * ((facePt τ 3 : ℝ) : ℂ) = τ := by
  simp [facePt, Complex.ext_iff]

theorem lineA1K_term (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (o : OrbIdx N k) :
    ∫ v : Fin 2 → ℝ, cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      ((N : ℂ) ^ 2)⁻¹ * cx b (cx (orbitSign N k (Quotient.out o.1))
        (Tinf n (orbitSeed N k n f (Quotient.out o.1)) x p q m)) := by
  have hr : cuspRow (gammaN N) (CuspData.ofSL k).r (Quotient.out o.1) 0 ≠ 0 := by
    have := o.2
    rw [QAct.r0Q_out] at this
    exact this
  have hint : ∫ v : Fin 2 → ℝ, cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      cx b (∫ v : Fin 2 → ℝ, PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) := by
    simp_rw [cxL_apply]
    cases b
    · simp [cx]
    · simp only [cx, ite_true]
      exact integral_conj
  rw [hint, integral_comp_smul_N, PhiQ0_integral_eval N k n f hx p q m _ hr]
  cases b <;> simp [cx]

theorem summable_Tinf (hn : 4 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    Summable (fun o : OrbIdx N k => cx b (cx (orbitSign N k (Quotient.out o.1))
      (Tinf n (orbitSeed N k n f (Quotient.out o.1)) x p q m))) := by
  have hs := (lineA1K_data N k n f b hn hx p q m).1
  simp_rw [lineA1K_term N k n f b hx p q m] at hs
  exact (summable_mul_left_iff (by simp [NeZero.ne N])).1 hs

/-- **Absolute convergence of the orbit-seed series** at every `τ` of the upper half plane. -/
theorem summable_orbitSeed (hn : 4 ≤ n) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun o : OrbIdx N k => ‖orbitSeed N k n f (Quotient.out o.1) τ‖) := by
  have hx := facePt_mem hτ
  have hs := summable_Tinf N k n f (by omega) false hx 0 2 (Finsupp.single 1 n)
  have hs' : Summable (fun o : OrbIdx N k => ‖cinf n‖ * ‖orbitSeed N k n f (Quotient.out o.1) τ‖) := by
    refine (summable_norm_iff.2 hs).congr fun o => ?_
    obtain ⟨hd, M, hM⟩ := orbitSeed_data N k n f _ (orbitMat_ne N k o)
    rw [Tinf_Yn_pair02 n (by omega) _ hd M hM hx, facePt_tau]
    cases orbitSign N k (Quotient.out o.1) <;> simp [cx]
  exact (summable_mul_left_iff (by
    unfold cinf
    have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [Real.pi_ne_zero, this])).1 hs'

end Series

end TernaryPeriodPolynomials.Argument.EisensteinClass
