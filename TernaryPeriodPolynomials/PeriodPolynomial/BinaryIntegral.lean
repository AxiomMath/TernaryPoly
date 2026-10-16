module

public import TernaryPeriodPolynomials.Polynomial.Integral
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly

/-- Normalized polynomial integration commutes with rational algebra coefficient maps. -/
theorem map_polyIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (p : Polynomial R) :
    Polynomial.map φ.toRingHom (polyIntegral p) =
      polyIntegral (Polynomial.map φ.toRingHom p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n r =>
    simp only [polyIntegral_monomial, Polynomial.map_monomial, map_mul]
    have hc : φ.toRingHom (algebraMap ℚ R (((n : ℚ)+1)⁻¹)) =
        algebraMap ℚ S (((n : ℚ)+1)⁻¹) := φ.commutes _
    rw [hc]

/-- The successor coefficient of the integral is the divided original coefficient. -/
theorem polyIntegral_coeff_succ {R : Type*} [CommRing R] [Algebra ℚ R]
    (p : Polynomial R) (n : ℕ) :
    (polyIntegral p).coeff (n+1) =
      algebraMap ℚ R (((n : ℚ)+1)⁻¹) * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial m r =>
    simp only [polyIntegral_monomial, Polynomial.coeff_monomial, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst m; rfl
    · exact (mul_zero _).symm

/-- Partial differentiation in the first variable is ordinary differentiation after transport. -/
theorem finSuccEquiv_pderiv_zero_general (n : ℕ) (f : MvPolynomial (Fin (n+1)) ℚ) :
    finSuccEquiv ℚ n (pderiv 0 f) = Polynomial.derivative (finSuccEquiv ℚ n f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    cases i using Fin.cases with
    | zero => simp [map_mul, hp, Polynomial.derivative_mul, finSuccEquiv_X_zero, mul_comm]
    | succ i => simp [map_mul, hp, Polynomial.derivative_mul, finSuccEquiv_X_succ, mul_comm]

/-- Integrate in the first binary variable with zero integration constant. -/
def binaryIntegral : MvPolynomial (Fin 2) ℚ →ₗ[ℚ] MvPolynomial (Fin 2) ℚ :=
  (finSuccEquiv ℚ 1).symm.toLinearMap.comp
    (((polyIntegral (R := MvPolynomial (Fin 1) ℚ)).restrictScalars ℚ).comp
      (finSuccEquiv ℚ 1).toLinearMap)

@[simp] theorem finSuccEquiv_binaryIntegral (p : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 1 (binaryIntegral p) = polyIntegral (finSuccEquiv ℚ 1 p) := by
  simp [binaryIntegral]

/-- The first partial derivative of the binary integral recovers its input. -/
@[simp] theorem pderiv_zero_binaryIntegral (p : MvPolynomial (Fin 2) ℚ) :
    pderiv 0 (binaryIntegral p) = p := by
  apply (finSuccEquiv ℚ 1).injective
  rw [finSuccEquiv_pderiv_zero_general, finSuccEquiv_binaryIntegral, derivative_polyIntegral]

/-- Restricting the first variable to zero takes the constant coefficient after transport. -/
theorem finSuccEquiv_bind_zero (p : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 1 (bind₁ ![0, X 1] p) =
      Polynomial.C (Polynomial.eval 0 (finSuccEquiv ℚ 1 p)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp]
    have h1 : finSuccEquiv ℚ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
      finSuccEquiv_X_succ (j := 0)
    fin_cases i <;> simp [finSuccEquiv_X_zero, h1]

/-- The binary integral vanishes on the axis where its integration variable is zero. -/
@[simp] theorem bind_zero_binaryIntegral (p : MvPolynomial (Fin 2) ℚ) :
    bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) (binaryIntegral p) = 0 := by
  apply (finSuccEquiv ℚ 1).injective
  rw [finSuccEquiv_bind_zero, finSuccEquiv_binaryIntegral,
    ← Polynomial.coeff_zero_eq_eval_zero, polyIntegral_coeff_zero]
  simp

/-- Binary integration increases the homogeneous degree by exactly one. -/
theorem isHomogeneous_binaryIntegral {p : MvPolynomial (Fin 2) ℚ} {n : ℕ}
    (hp : p.IsHomogeneous n) : (binaryIntegral p).IsHomogeneous (n+1) := by
  intro d hd
  rw [← Finsupp.cons_tail d] at hd ⊢
  cases h0 : d 0 with
  | zero =>
    rw [h0, ← finSuccEquiv_coeff_coeff, finSuccEquiv_binaryIntegral,
      polyIntegral_coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hd
    exact (hd rfl).elim
  | succ k =>
    rw [h0, ← finSuccEquiv_coeff_coeff, finSuccEquiv_binaryIntegral,
      polyIntegral_coeff_succ, MvPolynomial.algebraMap_eq, coeff_C_mul,
      finSuccEquiv_coeff_coeff] at hd
    have h := hp (mul_ne_zero_iff.mp hd).2
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finsupp.sum_cons] at h ⊢
    omega

end TernaryPoly
