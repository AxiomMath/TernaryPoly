module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Action
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section


/-! The factorial monomial metric, with multiplication adjoint to partial differentiation. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

abbrev Exponent := Fin 3 →₀ ℕ

def factorialWeight (d : Exponent) : ℝ := ∏ i : Fin 3, (d i).factorial

theorem factorialWeight_pos (d : Exponent) : 0 < factorialWeight d := by
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.factorial_pos (d i)

theorem factorialWeight_succ (d : Exponent) (i : Fin 3) :
    factorialWeight (d + Finsupp.single i 1) = (d i + 1) * factorialWeight d := by
  fin_cases i <;> simp [factorialWeight, Fin.prod_univ_succ, Finsupp.single_apply,
    Nat.factorial_succ] <;> ring

/-- Monomials are orthogonal and `⟨x^d,x^d⟩ = ∏ i, (d i)!`. -/
def factorialPairing : Poly →ₗ[ℝ] Poly →ₗ[ℝ] ℝ :=
  (basisMonomials (Fin 3) ℝ).constr ℝ (fun d => factorialWeight d • lcoeff ℝ d)

theorem factorialPairing_monomial_one (d : Exponent) (q : Poly) :
    factorialPairing (monomial d 1) q = factorialWeight d * q.coeff d := by
  have h := (basisMonomials (Fin 3) ℝ).constr_basis ℝ
    (fun d => factorialWeight d • lcoeff ℝ d) d
  exact congrArg (fun f : Poly →ₗ[ℝ] ℝ => f q) h

theorem factorialPairing_monomial (d : Exponent) (a : ℝ) (q : Poly) :
    factorialPairing (monomial d a) q = a * factorialWeight d * q.coeff d := by
  have h : monomial d a = a • (monomial d 1 : Poly) := by simp [smul_monomial]
  rw [h, map_smul, LinearMap.smul_apply, factorialPairing_monomial_one]
  simp [mul_assoc]

theorem factorialPairing_sum (p q : Poly) :
    factorialPairing p q = ∑ d ∈ p.support, factorialWeight d * p.coeff d * q.coeff d := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, LinearMap.sum_apply, factorialPairing_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem factorialPairing_symmetric (p q : Poly) :
    factorialPairing p q = factorialPairing q p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      simp only [factorialPairing_monomial, coeff_monomial]
      by_cases h : d = e
      · subst e; simp; ring
      · simp [h, Ne.symm h]
    | add q r hq hr => simp_all
  | add p q hp hq => simp_all

theorem factorialPairing_self_nonneg (p : Poly) : 0 ≤ factorialPairing p p := by
  rw [factorialPairing_sum]
  apply Finset.sum_nonneg
  intro d hd
  have hw := (factorialWeight_pos d).le
  nlinarith [sq_nonneg (p.coeff d)]

theorem factorialPairing_self_eq_zero (p : Poly) : factorialPairing p p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    rw [factorialPairing_sum] at hp
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun d (_ : d ∈ p.support) =>
      show 0 ≤ factorialWeight d * p.coeff d * p.coeff d by
        nlinarith [factorialWeight_pos d, sq_nonneg (p.coeff d)])).mp hp
    apply MvPolynomial.ext
    intro d
    by_cases hd : d ∈ p.support
    · have hz := hterms d hd
      have hw := factorialWeight_pos d
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hw)
      · exact hz
    · simpa using (notMem_support_iff.mp hd)
  · rintro rfl
    simp

/-- Multiplication and differentiation are adjoint for the factorial metric. -/
theorem factorialPairing_X_mul (i : Fin 3) (p q : Poly) :
    factorialPairing (X i * p) q = factorialPairing p (pderiv i q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [X, monomial_mul_monomial, one_mul, factorialPairing_monomial,
      factorialPairing_monomial, coeff_pderiv, add_comm (Finsupp.single i 1) d,
      factorialWeight_succ]
    ring
  | add p r hp hr => simp [mul_add, hp, hr]

theorem factorialPairing_pderiv (i : Fin 3) (p q : Poly) :
    factorialPairing (pderiv i p) q = factorialPairing p (X i * q) := by
  rw [factorialPairing_symmetric, ← factorialPairing_X_mul, factorialPairing_symmetric]

theorem factorialPairing_X_pderiv (i j : Fin 3) (p q : Poly) :
    factorialPairing (X j * pderiv i p) q = factorialPairing p (X i * pderiv j q) := by
  rw [factorialPairing_X_mul, factorialPairing_pderiv]

/-- The infinitesimal transpose-adjoint identity, including the inverse-action sign. -/
theorem infinitesimal_transpose_adjoint (A : Mat) (p q : Poly) :
    factorialPairing (infinitesimal A p) q =
      factorialPairing p (infinitesimal A.transpose q) := by
  simp only [infinitesimal_apply, map_neg, LinearMap.neg_apply, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Matrix.transpose_apply, factorialPairing_X_pderiv]
  rw [Finset.sum_comm]

theorem infinitesimal_symmetric_adjoint (A : Mat) (hA : A.transpose = A) (p q : Poly) :
    factorialPairing (infinitesimal A p) q = factorialPairing p (infinitesimal A q) := by
  simpa only [hA] using infinitesimal_transpose_adjoint A p q

theorem infinitesimal_skew_adjoint (A : Mat) (hA : A.transpose = -A) (p q : Poly) :
    factorialPairing (infinitesimal A p) q = -factorialPairing p (infinitesimal A q) := by
  rw [infinitesimal_transpose_adjoint, hA]
  have hneg : infinitesimal (-A) = -infinitesimal A := by
    apply derivation_ext
    intro i
    simp [Finset.sum_neg_distrib]
  simp [hneg]

/-- A positive real inner-product core on all polynomials; its restriction gives the
admissible coefficient metric in each homogeneous degree. -/
@[instance_reducible] def factorialInnerCore : InnerProductSpace.Core ℝ Poly where
  inner := fun p q => factorialPairing p q
  conj_inner_symm := fun p q => by simpa using factorialPairing_symmetric q p
  re_inner_nonneg := factorialPairing_self_nonneg
  add_left := by intros; simp
  smul_left := by intros; simp
  definite := fun p h => (factorialPairing_self_eq_zero p).mp h

/-- The concrete positive inner product on the actual homogeneous coefficient space. -/
@[instance_reducible] def homogeneousInnerCore (n : ℕ) :
    InnerProductSpace.Core ℝ (homogeneousSubmodule (Fin 3) ℝ n) where
  inner := fun p q => factorialPairing p.val q.val
  conj_inner_symm := fun p q => by simpa using factorialPairing_symmetric q.val p.val
  re_inner_nonneg := fun p => factorialPairing_self_nonneg p.val
  add_left := by intros; simp
  smul_left := by intros; simp
  definite := fun p h => Subtype.ext ((factorialPairing_self_eq_zero p.val).mp h)

end TernaryPoly.SL3PolynomialCoercivity
