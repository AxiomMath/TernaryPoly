module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly

/-- Embedding the coefficient variables produces a univariate constant. -/
theorem finSuccEquiv_rename_succ (p : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 2 (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, rename_X, finSuccEquiv_X_succ, hp]

/-- First-coordinate translations fix every coefficient polynomial. -/
theorem alternatingShift_rename_succ (u : TernaryPolynomial)
    (p : MvPolynomial (Fin 2) ℚ) :
    alternatingShift u (rename Fin.succ p) = rename Fin.succ p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [rename_C, alternatingShift, bind₁_C_right]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, rename_X, hp]
    congr 1
    simp only [alternatingShift, bind₁_X_right]
    fin_cases i <;> rfl

/-- Coefficient polynomials are independent of the first coordinate. -/
theorem pderiv_zero_rename_succ (p : MvPolynomial (Fin 2) ℚ) :
    pderiv 0 (rename Fin.succ p : TernaryPolynomial) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [map_zero, finSuccEquiv_pderiv_zero, finSuccEquiv_rename_succ,
    Polynomial.derivative_C]

/-- The Todd operator fixes coefficient constants. -/
theorem todd_C {R : Type*} [CommRing R] [Algebra ℚ R] (u r : R) :
    todd u (Polynomial.C r) = Polynomial.C r := by
  rw [todd_eq_sum u (Polynomial.C r) 1 (by simp)]
  simp

/-- The ternary Todd operator fixes every polynomial in the other two coordinates. -/
theorem ternaryTodd_rename_succ (u p : MvPolynomial (Fin 2) ℚ) :
    ternaryTodd u (rename Fin.succ p) = rename Fin.succ p := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd, AlgEquiv.apply_symm_apply, finSuccEquiv_rename_succ, todd_C]

/-- The positive Euler section in the `Z` component. -/
def radicalEulerFirst (d : ℕ) (J : MvPolynomial (Fin 2) ℚ) : TernaryPolynomial :=
  rename Fin.succ (MvPolynomial.C ((d : ℚ)⁻¹) * pderiv 1 J)

/-- The negative Euler section in the `Y` component. -/
def radicalEulerSecond (d : ℕ) (J : MvPolynomial (Fin 2) ℚ) : TernaryPolynomial :=
  rename Fin.succ (-(MvPolynomial.C ((d : ℚ)⁻¹)) * pderiv 0 J)

/-- Both explicit Euler section polynomials have zero first partial derivative. -/
theorem radicalEuler_independent (d : ℕ) (J : MvPolynomial (Fin 2) ℚ) :
    pderiv 0 (radicalEulerFirst d J) = 0 ∧
      pderiv 0 (radicalEulerSecond d J) = 0 :=
  ⟨pderiv_zero_rename_succ _, pderiv_zero_rename_succ _⟩

/-- The Euler section is fixed by all first-coordinate translations. -/
theorem radicalEuler_shift (d : ℕ) (J : MvPolynomial (Fin 2) ℚ)
    (u : TernaryPolynomial) :
    alternatingShift u (radicalEulerFirst d J) = radicalEulerFirst d J ∧
      alternatingShift u (radicalEulerSecond d J) = radicalEulerSecond d J :=
  ⟨alternatingShift_rename_succ u _, alternatingShift_rename_succ u _⟩

/-- Its two finite differences have zero curl. -/
theorem radicalEuler_curl_zero (d : ℕ) (J : MvPolynomial (Fin 2) ℚ) :
    (alternatingShift (X 1) (radicalEulerSecond d J) - radicalEulerSecond d J) -
      (alternatingShift (X 2) (radicalEulerFirst d J) - radicalEulerFirst d J) = 0 := by
  rw [(radicalEuler_shift d J (X 1)).2, (radicalEuler_shift d J (X 2)).1]
  simp only [sub_self]

/-- Euler's identity provides the prescribed binary contraction in positive degree. -/
theorem binary_radicalEuler_contraction {d : ℕ} (hd : 0 < d)
    {J : MvPolynomial (Fin 2) ℚ} (hJ : J.IsHomogeneous d) :
    X 1 * (MvPolynomial.C ((d : ℚ)⁻¹) * pderiv 1 J) -
      X 0 * (-(MvPolynomial.C ((d : ℚ)⁻¹)) * pderiv 0 J) = J := by
  have heuler : X 0 * pderiv 0 J + X 1 * pderiv 1 J = MvPolynomial.C (d : ℚ) * J := by
    simpa only [Fin.sum_univ_two, nsmul_eq_mul, map_natCast] using hJ.sum_X_mul_pderiv
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  calc
    _ = MvPolynomial.C ((d : ℚ)⁻¹) * (X 0 * pderiv 0 J + X 1 * pderiv 1 J) := by ring
    _ = J := by
      rw [heuler, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hdq, map_one, one_mul]

/-- Todd contraction of the explicit Euler section is the prescribed target. -/
theorem radicalEuler_todd_contraction {d : ℕ} (hd : 0 < d)
    {J : MvPolynomial (Fin 2) ℚ} (hJ : J.IsHomogeneous d) :
    X 2 * ternaryTodd (X (0 : Fin 2)) (radicalEulerFirst d J) -
      X 1 * ternaryTodd (X (1 : Fin 2)) (radicalEulerSecond d J) = rename Fin.succ J := by
  simp only [radicalEulerFirst, radicalEulerSecond, ternaryTodd_rename_succ]
  have h := congrArg (rename (Fin.succ : Fin 2 → Fin 3))
    (binary_radicalEuler_contraction hd hJ)
  simpa only [map_sub, map_mul, rename_X,
    show Fin.succ (0 : Fin 2) = (1 : Fin 3) from rfl,
    show Fin.succ (1 : Fin 2) = (2 : Fin 3) from rfl] using h

/-- The two Euler section polynomials have degree one less than the target. -/
theorem radicalEuler_homogeneous {d : ℕ} {J : MvPolynomial (Fin 2) ℚ}
    (hJ : J.IsHomogeneous d) :
    (radicalEulerFirst d J).IsHomogeneous (d - 1) ∧
      (radicalEulerSecond d J).IsHomogeneous (d - 1) := by
  constructor
  · exact (hJ.pderiv.C_mul ((d : ℚ)⁻¹)).rename_isHomogeneous
  · change (rename Fin.succ (-(MvPolynomial.C ((d : ℚ)⁻¹)) * pderiv 0 J)).IsHomogeneous (d - 1)
    rw [neg_mul]
    exact (hJ.pderiv.C_mul ((d : ℚ)⁻¹)).neg.rename_isHomogeneous

/-- Every positive-degree homogeneous target is the contraction of a zero-curl pair. -/
theorem radical_todd_surjective {d : ℕ} (hd : 0 < d)
    (J : MvPolynomial (Fin 2) ℚ) (hJ : J.IsHomogeneous d) :
    ∃ g₁ g₂ : TernaryPolynomial,
      g₁.IsHomogeneous (d - 1) ∧ g₂.IsHomogeneous (d - 1) ∧
      pderiv 0 g₁ = 0 ∧ pderiv 0 g₂ = 0 ∧
      (alternatingShift (X 1) g₂ - g₂) - (alternatingShift (X 2) g₁ - g₁) = 0 ∧
      X 2 * ternaryTodd (X (0 : Fin 2)) g₁ -
        X 1 * ternaryTodd (X (1 : Fin 2)) g₂ = rename Fin.succ J := by
  refine ⟨radicalEulerFirst d J, radicalEulerSecond d J,
    (radicalEuler_homogeneous hJ).1, (radicalEuler_homogeneous hJ).2,
    (radicalEuler_independent d J).1, (radicalEuler_independent d J).2,
    radicalEuler_curl_zero d J, radicalEuler_todd_contraction hd hJ⟩

end TernaryPoly
