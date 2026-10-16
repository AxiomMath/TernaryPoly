module

public import TernaryPeriodPolynomials.AlternatingSolution.Certificate
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Basic
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Difference
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Transport
public import Mathlib.Algebra.Module.Rat

@[expose] public section

open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- Todd in the first ternary coordinate, with a polynomial in the other two as parameter. -/
def ternaryTodd (u : MvPolynomial (Fin 2) ℚ) (f : TernaryPolynomial) :
    TernaryPolynomial :=
  (finSuccEquiv ℚ 2).symm (todd u (finSuccEquiv ℚ 2 f))

/-- The actual alternating Todd expression in the literal certified frames. -/
def alternatingTodd (f : TernaryPolynomial) : TernaryPolynomial :=
  X 2 * ternaryTodd (X (0 : Fin 2)) (alternatingFrame1 f) -
    X 1 * ternaryTodd (X (1 : Fin 2)) (alternatingFrame2 f)

/-- Its univariate presentation keeps `Y` and `Z` in the coefficient ring. -/
theorem finSuccEquiv_alternatingTodd (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (alternatingTodd f) =
      (X 1 : MvPolynomial (Fin 2) ℚ) • todd (X (0 : Fin 2)) (finSuccEquiv ℚ 2 (alternatingFrame1 f)) -
        (X 0 : MvPolynomial (Fin 2) ℚ) • todd (X (1 : Fin 2)) (finSuccEquiv ℚ 2 (alternatingFrame2 f)) := by
  simp only [alternatingTodd, map_sub, finSuccEquiv_Z_mul, finSuccEquiv_Y_mul,
    ternaryTodd, AlgEquiv.apply_symm_apply, Polynomial.smul_eq_C_mul]

/-- The exact alternating zero curl, transported to the univariate coefficient ring. -/
theorem alternatingTodd_frames_zero_curl {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    (Polynomial.taylor (-X (0 : Fin 2)) (finSuccEquiv ℚ 2 (alternatingFrame2 f)) -
        finSuccEquiv ℚ 2 (alternatingFrame2 f)) -
      (Polynomial.taylor (-X (1 : Fin 2)) (finSuccEquiv ℚ 2 (alternatingFrame1 f)) -
        finSuccEquiv ℚ 2 (alternatingFrame1 f)) = 0 := by
  have h := congrArg (finSuccEquiv ℚ 2) (alternating_frames_curl_eq_zero hc hs hn)
  simpa only [map_sub, map_zero, alternatingShift,
    finSuccEquiv_shift_Y, finSuccEquiv_shift_Z] using h

/-- Applying two commuting Todd operators converts zero curl into zero derivative. -/
theorem todd_curl_derivative_of_difference {R : Type*} [CommRing R] [Algebra ℚ R]
    (hdiff : ∀ (u : R) (p : Polynomial R),
      todd u (Polynomial.taylor (-u) p - p) = (-u) • Polynomial.derivative p)
    (u v : R) (g₁ g₂ : Polynomial R)
    (hcurl : (Polynomial.taylor (-u) g₂ - g₂) -
      (Polynomial.taylor (-v) g₁ - g₁) = 0) :
    Polynomial.derivative (v • todd u g₁ - u • todd v g₂) = 0 := by
  have h := congrArg (fun p => todd u (todd v p)) (sub_eq_zero.mp hcurl)
  rw [todd_commute u v (Polynomial.taylor (-u) g₂ - g₂),
    hdiff u g₂, hdiff v g₁, map_smul, map_smul] at h
  have heq : u • todd v (Polynomial.derivative g₂) =
      v • todd u (Polynomial.derivative g₁) := by
    simpa only [neg_smul, neg_inj] using h
  simp only [map_sub, map_smul, derivative_todd]
  exact sub_eq_zero.mpr heq.symm

/-- The certified frames satisfy Todd derivative vanishing once the difference law is supplied. -/
theorem pderiv_zero_alternatingTodd_of_difference
    (hdiff : ∀ (u : MvPolynomial (Fin 2) ℚ) (p : Polynomial (MvPolynomial (Fin 2) ℚ)),
      todd u (Polynomial.taylor (-u) p - p) = (-u) • Polynomial.derivative p)
    {f : TernaryPolynomial} (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    pderiv 0 (alternatingTodd f) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [map_zero, finSuccEquiv_pderiv_zero, finSuccEquiv_alternatingTodd]
  exact todd_curl_derivative_of_difference hdiff _ _ _ _
    (alternatingTodd_frames_zero_curl hc hs hn)

/-- The actual alternating Todd expression has zero derivative in the first coordinate. -/
theorem pderiv_zero_alternatingTodd {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    pderiv 0 (alternatingTodd f) = 0 :=
  pderiv_zero_alternatingTodd_of_difference todd_difference hc hs hn

/-- Its univariate presentation is therefore a coefficient-ring constant. -/
theorem finSuccEquiv_alternatingTodd_eq_C {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    finSuccEquiv ℚ 2 (alternatingTodd f) =
      Polynomial.C ((finSuccEquiv ℚ 2 (alternatingTodd f)).coeff 0) := by
  let : IsAddTorsionFree (MvPolynomial (Fin 2) ℚ) :=
    IsAddTorsionFree.of_module_rat _
  apply Polynomial.eq_C_of_derivative_eq_zero
  rw [← finSuccEquiv_pderiv_zero, pderiv_zero_alternatingTodd hc hs hn, map_zero]

end TernaryPoly
