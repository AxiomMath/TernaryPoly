module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Koszul
public import Mathlib.Algebra.Polynomial.Eval.Coeff

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def radicalShearFamily (index : Fin 2) : Poly →ₐ[ℂ] Polynomial Poly :=
  MvPolynomial.aeval (fun coordinate : Fin 3 =>
    if coordinate = 0 then Polynomial.C (X 0) -
      Polynomial.C (X index.succ) * Polynomial.X else Polynomial.C (X coordinate))

theorem radicalShearFamily_eval (index : Fin 2) (parameter : ℂ) (polynomial : Poly) :
    Polynomial.eval (C parameter) (radicalShearFamily index polynomial) =
      bind₁ (fun coordinate : Fin 3 =>
        if coordinate = 0 then X 0 - C parameter * X index.succ else X coordinate) polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [radicalShearFamily]
  | add first second firstIdentity secondIdentity =>
    simp [map_add, firstIdentity, secondIdentity]
  | mul_X polynomial coordinate identity =>
    rw [map_mul, Polynomial.eval_mul, identity, map_mul]
    congr 1
    by_cases zero : coordinate = 0
    · simp [radicalShearFamily, zero]
      ring
    · simp [radicalShearFamily, zero]

theorem radicalShearFamily_coeff_zero (index : Fin 2) (polynomial : Poly) :
    (radicalShearFamily index polynomial).coeff 0 = polynomial := by
  have identity := radicalShearFamily_eval index 0 polynomial
  have forms : (fun coordinate : Fin 3 =>
      if coordinate = 0 then X 0 - C (0 : ℂ) * X index.succ else X coordinate) = X := by
    funext coordinate
    by_cases zero : coordinate = 0 <;> simp [zero]
  rw [forms] at identity
  have atZero : Polynomial.eval 0 (radicalShearFamily index polynomial) = polynomial := by
    simpa using identity
  exact (Polynomial.coeff_zero_eq_eval_zero _).trans atZero

theorem polynomial_coeff_one_mul (first second : Polynomial Poly) :
    (first * second).coeff 1 =
      first.coeff 0 * second.coeff 1 + first.coeff 1 * second.coeff 0 := by
  rw [Polynomial.coeff_mul]
  have antidiagonal : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  rw [antidiagonal]
  simp

theorem radicalShearFamily_coeff_one (index : Fin 2) (polynomial : Poly) :
    (radicalShearFamily index polynomial).coeff 1 = -X index.succ * pderiv 0 polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [radicalShearFamily]
  | add first second firstIdentity secondIdentity =>
    rw [map_add, Polynomial.coeff_add, firstIdentity, secondIdentity, map_add, mul_add]
  | mul_X polynomial coordinate identity =>
    rw [map_mul, polynomial_coeff_one_mul, radicalShearFamily_coeff_zero, identity]
    have coefficientZero : (radicalShearFamily index (X coordinate)).coeff 0 = X coordinate :=
      radicalShearFamily_coeff_zero index (X coordinate)
    rw [coefficientZero]
    by_cases zero : coordinate = 0
    · subst coordinate
      simp [radicalShearFamily, pderiv_X]
      ring
    · simp [radicalShearFamily, zero, pderiv_X_of_ne zero]
      ring

theorem radicalShear_invariant_derivative (index : Fin 2) (polynomial : Poly)
    (invariant : ∀ parameter : ℚ,
      bind₁ (fun coordinate : Fin 3 =>
        if coordinate = 0 then X 0 - C (parameter : ℂ) * X index.succ else X coordinate)
          polynomial = polynomial) : pderiv 0 polynomial = 0 := by
  have injective : Function.Injective (fun parameter : ℚ => (C (parameter : ℂ) : Poly)) :=
    (MvPolynomial.C_injective (Fin 3) ℂ).comp Rat.cast_injective
  have infinite := Set.infinite_range_of_injective injective
  have familyEquality : radicalShearFamily index polynomial = Polynomial.C polynomial := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infinite.mono
    rintro parameter ⟨rational, rfl⟩
    change Polynomial.eval (C (rational : ℂ)) (radicalShearFamily index polynomial) =
      Polynomial.eval (C (rational : ℂ)) (Polynomial.C polynomial)
    rw [radicalShearFamily_eval, Polynomial.eval_C]
    exact invariant rational
  have coefficient := congrArg (fun family : Polynomial Poly => family.coeff 1) familyEquality
  rw [radicalShearFamily_coeff_one, Polynomial.coeff_C] at coefficient
  simp only [one_ne_zero, ↓reduceIte] at coefficient
  exact (mul_eq_zero.mp coefficient).resolve_left
    (neg_ne_zero.mpr (MvPolynomial.X_ne_zero index.succ))

theorem lineRadicalInvariants_le_derivativeKernel (degree : ℕ) :
    lineRadicalInvariants degree ≤ radicalDerivativeKernel degree := by
  intro polynomial invariant
  change pderiv 0 polynomial.val = 0
  apply radicalShear_invariant_derivative 0 polynomial.val
  intro parameter
  have actionEquality : rationalCoefficientComponent degree trivialCharacter
      (lineUnipotent parameter 0) polynomial = polynomial := invariant parameter 0
  have action := congrArg (fun value : HomogeneousPoly degree => (value.val : Poly)) actionEquality
  rw [rationalCoefficientComponent_lineUnipotent] at action
  have forms : (fun coordinate : Fin 3 =>
      if coordinate = 0 then X 0 - C (parameter : ℂ) * X (0 : Fin 2).succ else X coordinate) =
      (![X 0 - C (parameter : ℂ) * X 1 - C (0 : ℂ) * X 2, X 1, X 2] : Fin 3 → Poly) := by
    funext coordinate
    fin_cases coordinate <;> simp
  rw [forms]
  simpa only [Rat.cast_zero] using action

theorem binaryHomogeneousEmbedding_range_eq_invariants (degree : ℕ) :
    LinearMap.range (binaryHomogeneousEmbedding degree) = lineRadicalInvariants degree := by
  apply le_antisymm
  · exact binaryHomogeneousEmbedding_range_le_invariants degree
  · rw [binaryHomogeneousEmbedding_range_eq_derivativeKernel]
    exact lineRadicalInvariants_le_derivativeKernel degree

def binaryLineRadicalInvariantsEquiv (degree : ℕ) :
    Binary.HomogeneousPoly degree ≃ₗ[ℂ] lineRadicalInvariants degree :=
  (LinearEquiv.ofInjective (binaryHomogeneousEmbedding degree)
    (binaryHomogeneousEmbedding_injective degree)).trans
      (LinearEquiv.ofEq _ _ (binaryHomogeneousEmbedding_range_eq_invariants degree))

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
