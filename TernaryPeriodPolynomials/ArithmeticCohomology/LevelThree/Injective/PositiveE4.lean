module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.PositiveE4Aux
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.PositiveEta
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle

@[expose] public section


/-!
# Positive level-three cusp forms of weights `7` and `8`

Using `exists_cusp_product_eq` for the seeds `B₄ = 81 E₄(3z) - E₄(z)` (times
`η(z) ^ (-3) η(3z) ^ 9`) and `A₄ B₄ = (E₄(z) - E₄(3z)) (81 E₄(3z) - E₄(z))`, together with the
positivity of `A₄`, `B₄` and of the eta quotients on the imaginary axis, we obtain nonzero
level-three cusp forms of weights `5 + 2` and `6 + 2` taking positive real values on the positive
imaginary axis (`exists_positive_form_five`, `exists_positive_form_six`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreeModularForms
open TernaryPeriodPolynomials.LevelThree.LevelThreeLowerBound

namespace TernaryPeriodPolynomials.LevelThreeInjective.PositiveE4

/-- A product of two positive real numbers is a positive real number. -/
theorem mul_pos_real {a b : ℂ} (ha : 0 < a.re ∧ a.im = 0) (hb : 0 < b.re ∧ b.im = 0) :
    0 < (a * b).re ∧ (a * b).im = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, ha.2, hb.2, mul_zero, sub_zero]
    exact mul_pos ha.1 hb.1
  · rw [Complex.mul_im, ha.2, hb.2]
    ring

/-- Multiplying a seed `s`, positive on the imaginary axis, by the eta quotient `phi a b` gives a
nonzero cusp form positive on the imaginary axis. -/
theorem positive_form_of {k w : ℤ} {e : ℕ} {s : ℍ → ℂ} {Ls : ℂ} (hs : IsMF w s)
    (hlead : HasLead s e Ls) (a b : ℕ) (hk : w + 3 * ((a : ℤ) + b) = k) (hInf : 1 ≤ e + a)
    (h0 : IsZeroAtImInfty (s ∣[w] (ModularGroup.S : SL(2, ℤ))) ∨ 1 ≤ b)
    (hpos : ∀ t : ℝ, 0 < t →
      0 < (s (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
        (s (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0) :
    ∃ f₀ : CuspForm binaryRealGammaOneThree k, f₀ ≠ 0 ∧ ∀ t : ℝ, 0 < t →
      0 < (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
        (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  obtain ⟨C, hC⟩ := PositiveEta.exists_cusp_product_eq hs hlead a b hk hInf h0
  have hval : ∀ t : ℝ, 0 < t → C (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))) =
      s (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))) *
        phi a b ((UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) : ℍ) : ℂ) :=
    fun _ _ => congrFun hC _
  have hpos' : ∀ t : ℝ, 0 < t →
      0 < (C (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
        (C (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
    intro t ht
    rw [hval t ht]
    exact mul_pos_real (hpos t ht) (PositiveEta.phi_ofComplex_pos a b t ht)
  refine ⟨C, fun hC0 => ?_, hpos'⟩
  have h1 := (hpos' 1 one_pos).1
  rw [hC0] at h1
  simp at h1

/-- A nonzero level-three cusp form of weight `5 + 2` taking positive real values on the positive
imaginary axis (namely `B₄ · η(z)^(-3) η(3z)^9`). -/
theorem exists_positive_form_five :
    ∃ f₀ : TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle.S 5,
      f₀ ≠ 0 ∧ ∀ t : ℝ, 0 < t →
        0 < (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
          (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  have hk : (4 : ℤ) + 3 * (((1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) =
      TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle.weight 5 := by
    show (4 : ℤ) + 3 * (((1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) = ((5 : ℕ) : ℤ) + 2
    norm_num
  exact positive_form_of isMF_B4 hasLead_B4 1 0 hk (by norm_num) (Or.inl B4_slash_zero) B4_pos

/-- A nonzero level-three cusp form of weight `6 + 2` taking positive real values on the positive
imaginary axis (namely `A₄ B₄`). -/
theorem exists_positive_form_six :
    ∃ f₀ : TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle.S 6,
      f₀ ≠ 0 ∧ ∀ t : ℝ, 0 < t →
        0 < (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
          (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  have hk : (4 + 4 : ℤ) + 3 * (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) =
      TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle.weight 6 := by
    show (4 + 4 : ℤ) + 3 * (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) = ((6 : ℕ) : ℤ) + 2
    norm_num
  exact positive_form_of isMF_AB hasLead_AB 0 0 hk (by norm_num) (Or.inl AB_slash_zero)
    (fun t ht => mul_pos_real (A4_pos t ht) (B4_pos t ht))

end TernaryPeriodPolynomials.LevelThreeInjective.PositiveE4
