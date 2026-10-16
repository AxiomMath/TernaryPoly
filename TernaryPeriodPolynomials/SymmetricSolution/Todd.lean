module

public import TernaryPeriodPolynomials.SymmetricSolution.ToddCertificate
public import TernaryPeriodPolynomials.AlternatingSolution.Todd

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The actual symmetric Todd expression in the literal certified frames. -/
def symmetricTodd (f : TernaryPolynomial) : TernaryPolynomial :=
  X 2 * ternaryTodd (X (0 : Fin 2)) (symmetricFrame1 f) -
    X 1 * ternaryTodd (X (1 : Fin 2)) (symmetricFrame2 f)

/-- Its univariate presentation keeps `Y` and `Z` in the coefficient ring. -/
theorem finSuccEquiv_symmetricTodd (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (symmetricTodd f) =
      (X 1 : MvPolynomial (Fin 2) ℚ) • todd (X (0 : Fin 2)) (finSuccEquiv ℚ 2 (symmetricFrame1 f)) -
        (X 0 : MvPolynomial (Fin 2) ℚ) • todd (X (1 : Fin 2)) (finSuccEquiv ℚ 2 (symmetricFrame2 f)) := by
  simp only [symmetricTodd, map_sub, finSuccEquiv_Z_mul, finSuccEquiv_Y_mul,
    ternaryTodd, AlgEquiv.apply_symm_apply, Polynomial.smul_eq_C_mul]

/-- The exact symmetric zero curl, transported to the univariate coefficient ring. -/
theorem symmetricTodd_frames_zero_curl {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = f) (hn : N f = 0) :
    (Polynomial.taylor (-X (0 : Fin 2)) (finSuccEquiv ℚ 2 (symmetricFrame2 f)) -
        finSuccEquiv ℚ 2 (symmetricFrame2 f)) -
      (Polynomial.taylor (-X (1 : Fin 2)) (finSuccEquiv ℚ 2 (symmetricFrame1 f)) -
        finSuccEquiv ℚ 2 (symmetricFrame1 f)) = 0 := by
  have h := congrArg (finSuccEquiv ℚ 2) (symmetric_frames_curl_eq_zero hc hs hn)
  simpa only [map_sub, map_zero, symmetricShift,
    finSuccEquiv_shift_Y, finSuccEquiv_shift_Z] using h

/-- The certified frames satisfy Todd derivative vanishing once the difference law is supplied. -/
theorem pderiv_zero_symmetricTodd_of_difference
    (hdiff : ∀ (u : MvPolynomial (Fin 2) ℚ) (p : Polynomial (MvPolynomial (Fin 2) ℚ)),
      todd u (Polynomial.taylor (-u) p - p) = (-u) • Polynomial.derivative p)
    {f : TernaryPolynomial} (hc : C f = f) (hs : S f = f) (hn : N f = 0) :
    pderiv 0 (symmetricTodd f) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [map_zero, finSuccEquiv_pderiv_zero, finSuccEquiv_symmetricTodd]
  exact todd_curl_derivative_of_difference hdiff _ _ _ _
    (symmetricTodd_frames_zero_curl hc hs hn)

/-- The actual symmetric Todd expression has zero derivative in the first coordinate. -/
theorem pderiv_zero_symmetricTodd {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = f) (hn : N f = 0) :
    pderiv 0 (symmetricTodd f) = 0 :=
  pderiv_zero_symmetricTodd_of_difference todd_difference hc hs hn

/-- Its univariate presentation is therefore a coefficient-ring constant. -/
theorem finSuccEquiv_symmetricTodd_eq_C {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = f) (hn : N f = 0) :
    finSuccEquiv ℚ 2 (symmetricTodd f) =
      Polynomial.C ((finSuccEquiv ℚ 2 (symmetricTodd f)).coeff 0) := by
  let : IsAddTorsionFree (MvPolynomial (Fin 2) ℚ) :=
    IsAddTorsionFree.of_module_rat _
  apply Polynomial.eq_C_of_derivative_eq_zero
  rw [← finSuccEquiv_pderiv_zero, pderiv_zero_symmetricTodd hc hs hn, map_zero]

end TernaryPoly
