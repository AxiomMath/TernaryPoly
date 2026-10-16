module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): algebraic preliminaries for the Levi/Möbius
transformation. This file: the Möbius denominator `(A 1 0 : ℂ) * seedTau p + A 1 1` does not
vanish when `A.det > 0` and `p 3 > 0`; the complex derivative of the Möbius map via the quotient
rule; and the sparsity/antisymmetry facts for `seedForm` at the *full polynomial* level (not just
coefficientwise, as in `ClosednessHardTriples.lean`) needed to collapse `formPullback`'s
`Fin 5 × Fin 5` double sum down to its `8` nontrivial terms. Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- The Möbius denominator does not vanish on the upper half-plane region `p 3 > 0`, given
`A.det > 0`. If it did, `seedTau p` would be forced real (a ratio of two real numbers), but
`seedTau p`'s imaginary part is `p 3 ≠ 0`. -/
theorem leviDenom_ne_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 5 → ℝ)
    (hdet : 0 < A.det) (hp3 : 0 < p 3) :
    (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0 := by
  rcases eq_or_ne (A 1 0) 0 with hA10 | hA10
  · rw [hA10]
    simp only [Complex.ofReal_zero, zero_mul, zero_add, ne_eq]
    intro hzero
    have hA11 : A 1 1 = 0 := by exact_mod_cast hzero
    have hd0 : A.det = 0 := by rw [Matrix.det_fin_two, hA10, hA11]; ring
    linarith
  · intro hzero
    have hA10' : (A 1 0 : ℂ) ≠ 0 := by exact_mod_cast hA10
    have hτ : seedTau p = ((-(A 1 1) / A 1 0 : ℝ) : ℂ) := by
      have hτ' : seedTau p = -(A 1 1 : ℂ) / (A 1 0 : ℂ) := by
        field_simp
        linear_combination hzero
      rw [hτ']; push_cast; ring
    have him : (seedTau p).im = 0 := by rw [hτ]; exact Complex.ofReal_im _
    rw [seedTau] at him
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add] at him
    linarith

/-- The complex derivative of the Möbius map `z ↦ (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)` via
the quotient rule, with the numerator simplifying to `A.det` by the cross-term cancellation. -/
theorem hasDerivAt_leviMobius (A : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℂ)
    (hden : (A 1 0 : ℂ) * τ + A 1 1 ≠ 0) :
    HasDerivAt (fun z : ℂ => ((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1))
      ((A.det : ℂ) / ((A 1 0 : ℂ) * τ + A 1 1) ^ 2) τ := by
  have hf : HasDerivAt (fun z : ℂ => (A 0 0 : ℂ) * z + A 0 1) (A 0 0 : ℂ) τ := by
    have := (hasDerivAt_id τ).const_mul (A 0 0 : ℂ)
    simpa using this.add_const (A 0 1 : ℂ)
  have hg : HasDerivAt (fun z : ℂ => (A 1 0 : ℂ) * z + A 1 1) (A 1 0 : ℂ) τ := by
    have := (hasDerivAt_id τ).const_mul (A 1 0 : ℂ)
    simpa using this.add_const (A 1 1 : ℂ)
  have hdiv := hf.div hg hden
  have heq : (A 0 0 : ℂ) * ((A 1 0 : ℂ) * τ + A 1 1) - ((A 0 0 : ℂ) * τ + A 0 1) * (A 1 0 : ℂ) =
      (A.det : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  rw [heq] at hdiv
  exact hdiv

/-- `seedForm` vanishes identically (as a polynomial, not just coefficientwise) whenever its
bracket factor `seedBeta p i * seedDTau j - seedBeta p j * seedDTau i` vanishes. -/
theorem seedForm_eq_zero_of_bracket_zero (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5)
    (hz : seedBeta p i * seedDTau j - seedBeta p j * seedDTau i = 0) :
    seedForm n h p i j = 0 := by
  unfold seedForm
  rw [hz, mul_zero, map_zero, zero_mul]

/-- `seedForm` is antisymmetric in its last two arguments (as a polynomial). -/
theorem seedForm_swap (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    seedForm n h p j i = -seedForm n h p i j := by
  unfold seedForm
  have hb : seedBeta p j * seedDTau i - seedBeta p i * seedDTau j =
      -(seedBeta p i * seedDTau j - seedBeta p j * seedDTau i) := by ring
  rw [hb, mul_neg, map_neg, neg_mul]

/-- All `17` "trivial" `seedForm` vanishings needed to collapse `formPullback`'s double sum:
both indices in `{0,1}`, both in `{2,3}`, either index `= 4`, or a repeated index. -/
theorem seedForm_trivial_pairs (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) :
    seedForm n h p 0 0 = 0 ∧ seedForm n h p 0 1 = 0 ∧ seedForm n h p 0 4 = 0 ∧
    seedForm n h p 1 0 = 0 ∧ seedForm n h p 1 1 = 0 ∧ seedForm n h p 1 4 = 0 ∧
    seedForm n h p 2 2 = 0 ∧ seedForm n h p 2 3 = 0 ∧ seedForm n h p 2 4 = 0 ∧
    seedForm n h p 3 2 = 0 ∧ seedForm n h p 3 3 = 0 ∧ seedForm n h p 3 4 = 0 ∧
    seedForm n h p 4 0 = 0 ∧ seedForm n h p 4 1 = 0 ∧ seedForm n h p 4 2 = 0 ∧
    seedForm n h p 4 3 = 0 ∧ seedForm n h p 4 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact seedForm_eq_zero_of_bracket_zero n h p _ _ (by simp [seedBeta, seedDTau])

end TernaryPeriodPolynomials.Argument
