module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.PolynomialTaylor

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem bernoulliOperator_translation_difference (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) :
    bernoulliOperator n t (bind₁ ![X 0-t,X 1,X 2] p.val - p.val) =
      -t * pderiv 0 p.val := by
  let D := polynomialTranslationDerivative n positive t linear
  let E : Module.End ℂ (HomogeneousPoly n) :=
    ∑ k ∈ Finset.range (n+1), (k.factorial : ℂ)⁻¹ • D^k
  have exponential : (E p).val = bind₁ ![X 0-t,X 1,X 2] p.val := by
    dsimp only [E, D]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
      Submodule.coe_smul,
      polynomialTranslationDerivative_pow n positive t linear independent]
    exact (homogeneous_translation_taylor p t).symm
  have identity := nilpotent_bernoulli_sum_identity (by omega : 2 ≤ n+1) D
    (polynomialTranslationDerivative_nilpotent n positive t linear independent)
  have evaluated := congrArg (fun operator : Module.End ℂ (HomogeneousPoly n) =>
    (operator p).val) identity
  change ((∑ k ∈ Finset.range (n+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • D^k)
    ((E-1) p)).val = -t * pderiv 0 p.val at evaluated
  rw [← bernoulliOperator_eq_endomorphism n positive t linear independent ((E-1) p)]
    at evaluated
  have argument : ((E-1) p).val = bind₁ ![X 0-t,X 1,X 2] p.val - p.val := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, exponential]
  simpa only [argument] using evaluated

theorem bernoulliOperator_neg (n : ℕ) (t p : Poly) :
    bernoulliOperator n t (-p) = -bernoulliOperator n t p := by
  have derivative_neg (k : ℕ) : ((fun q : Poly => pderiv 0 q)^[k]) (-p) =
      -((fun q : Poly => pderiv 0 q)^[k]) p := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_neg,
        Function.iterate_succ_apply']
  simp only [bernoulliOperator, derivative_neg, mul_neg, Finset.sum_neg_distrib]

theorem bernoulliOperator_coboundary (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) :
    bernoulliOperator n t (p.val - bind₁ ![X 0-t,X 1,X 2] p.val) =
      t * pderiv 0 p.val := by
  rw [← neg_sub (bind₁ ![X 0-t,X 1,X 2] p.val) p.val,
    bernoulliOperator_neg,
    bernoulliOperator_translation_difference n positive t linear independent p,
    neg_mul, neg_neg]

theorem radical_coboundary_bernoulli_zero (n : ℕ) (positive : 0 < n)
    (p : HomogeneousPoly n) :
    X 2 * bernoulliOperator n (X 1)
      (p.val - (rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 1 0) p).val) -
      X 1 * bernoulliOperator n (X 2)
        (p.val - (rationalCoefficientComponent n trivialCharacter
          (Adelic.lineUnipotent 0 1) p).val) = 0 := by
  rw [rationalCoefficient_lineUnipotent, rationalCoefficient_lineUnipotent]
  simp only [Rat.cast_one, Rat.cast_zero, map_one, map_zero, one_mul, zero_mul,
    sub_zero, evalTriple, aeval_eq_bind₁]
  rw [bernoulliOperator_coboundary n positive (X 1) (isHomogeneous_X ℂ 1)
    (by simp) p,
    bernoulliOperator_coboundary n positive (X 2) (isHomogeneous_X ℂ 2) (by simp) p]
  ring

theorem bernoulliOperator_injective (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0) :
    Function.Injective (fun p : HomogeneousPoly n => bernoulliOperator n t p.val) := by
  let D := polynomialTranslationDerivative n positive t linear
  obtain ⟨unit, unit_eq⟩ := nilpotent_bernoulli_isUnit (Nat.succ_pos n) D
    (polynomialTranslationDerivative_nilpotent n positive t linear independent)
  intro p q equal
  have values : unit.val p = unit.val q := by
    apply Subtype.ext
    rw [unit_eq, ← bernoulliOperator_eq_endomorphism n positive t linear independent,
      ← bernoulliOperator_eq_endomorphism n positive t linear independent]
    exact equal
  have canceled := congrArg (fun v : HomogeneousPoly n => unit⁻¹.val v) values
  simpa only [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] using canceled

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
