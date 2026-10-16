module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BernoulliAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.CoefficientAction

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem pderiv_homogeneous {n : ℕ} (p : Poly) (homogeneous : p.IsHomogeneous n)
    (i : Fin 3) : (pderiv i p).IsHomogeneous (n-1) := by
  intro exponent nonzero
  rw [coeff_pderiv] at nonzero
  have supported : p.coeff (exponent + Finsupp.single i 1) ≠ 0 := by
    exact left_ne_zero_of_mul nonzero
  have degree_eq := homogeneous supported
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, one_smul] at degree_eq
  omega

theorem homogeneous_iterate_pderiv_zero {n : ℕ} (p : Poly) (homogeneous : p.IsHomogeneous n)
    (i : Fin 3) : ((fun q : Poly => pderiv i q)^[n+1]) p = 0 := by
  induction n generalizing p with
  | zero =>
    have constant := homogeneousComponent_eq_self homogeneous
    rw [homogeneousComponent_zero] at constant
    rw [← constant]
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    simpa only [Nat.add_sub_cancel] using pderiv_homogeneous p homogeneous i

/-- The nilpotent infinitesimal translation on the fixed homogeneous degree. -/
def polynomialTranslationDerivative (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) : Module.End ℂ (HomogeneousPoly n) where
  toFun p := ⟨-t * pderiv 0 p.val, by
    change (-t * pderiv 0 p.val).IsHomogeneous n
    have degree_eq : 1 + (n-1) = n := by omega
    simpa only [degree_eq] using linear.neg.mul (pderiv_homogeneous p.val p.property 0)⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, mul_add]
  map_smul' a p := by
    apply Subtype.ext
    change -t * pderiv 0 (a • p.val) = a • (-t * pderiv 0 p.val)
    rw [Derivation.map_smul, mul_smul_comm]

theorem polynomialTranslationDerivative_pow (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) (k : ℕ) :
    (((polynomialTranslationDerivative n positive t linear)^k) p).val =
      (-t)^k * ((fun q : Poly => pderiv 0 q)^[k]) p.val := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change -t * pderiv 0 ((((polynomialTranslationDerivative n positive t linear)^k) p).val) = _
    rw [ih, pderiv_mul, pderiv_pow, map_neg, independent]
    simp only [neg_zero, mul_zero, zero_mul, zero_add, Function.iterate_succ_apply',
      pow_succ', mul_assoc]

theorem polynomialTranslationDerivative_nilpotent (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0) :
    (polynomialTranslationDerivative n positive t linear)^(n+1) = 0 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  rw [polynomialTranslationDerivative_pow n positive t linear independent p (n+1),
    homogeneous_iterate_pderiv_zero p.val p.property 0, mul_zero]
  rfl

theorem bernoulliOperator_eq_endomorphism (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) :
    bernoulliOperator n t p.val =
      ((∑ k ∈ Finset.range (n+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) •
        (polynomialTranslationDerivative n positive t linear)^k) p).val := by
  simp only [bernoulliOperator, LinearMap.sum_apply, Submodule.coe_sum,
    LinearMap.smul_apply, Submodule.coe_smul,
    polynomialTranslationDerivative_pow n positive t linear independent]
  apply Finset.sum_congr rfl
  intro k _
  rw [Algebra.smul_def, ← mul_assoc]
  rfl

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
