module

public import TernaryPeriodPolynomials.AlternatingSolution.FirstJet
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryIntegral

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Remove the unused third coordinate from a boundary polynomial. -/
def dropThird : TernaryPolynomial →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ ![X 0, X 1, 0]

/-- The corresponding map of univariate coefficient rings. -/
def dropThirdCoeff : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 1) ℚ :=
  bind₁ ![X 0, 0]

/-- The actual boundary polynomial in two variables. -/
def binaryBoundary (f : TernaryPolynomial) : MvPolynomial (Fin 2) ℚ :=
  bind₁ ![ -X 1, X 0, X 1-X 0] f

/-- The two-variable normalized first-jet primitive. -/
def binaryFirstJetPrimitive (f : TernaryPolynomial) : MvPolynomial (Fin 2) ℚ :=
  -binaryIntegral (binaryBoundary (pderiv 0 f+pderiv 1 f))

theorem finSuccEquiv_binary_X_one :
    finSuccEquiv ℚ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
  finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := 0)

theorem finSuccEquiv_dropThird (f : TernaryPolynomial) :
    finSuccEquiv ℚ 1 (dropThird f) =
      Polynomial.map dropThirdCoeff.toRingHom (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [dropThird, dropThirdCoeff, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp]
    fin_cases i <;>
      simp [dropThird, dropThirdCoeff, finSuccEquiv_X_zero, finSuccEquiv_binary_X_one,
        finSuccEquiv_ternary_X_one, finSuccEquiv_ternary_X_two]

theorem dropThird_alternatingPlaneH (f : TernaryPolynomial) :
    dropThird (alternatingPlaneH f) = binaryBoundary f := by
  unfold dropThird alternatingPlaneH substitute3 binaryBoundary
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

theorem map_finSuccEquiv_alternatingPlaneH (f : TernaryPolynomial) :
    Polynomial.map dropThirdCoeff.toRingHom (finSuccEquiv ℚ 2 (alternatingPlaneH f)) =
      finSuccEquiv ℚ 1 (binaryBoundary f) := by
  rw [← finSuccEquiv_dropThird, dropThird_alternatingPlaneH]

theorem binaryFirstJetPrimitive_transport (f : TernaryPolynomial) :
    finSuccEquiv ℚ 1 (binaryFirstJetPrimitive f) =
      Polynomial.map dropThirdCoeff.toRingHom (alternatingFirstJetPrimitive f) := by
  simp only [binaryFirstJetPrimitive, map_neg, finSuccEquiv_binaryIntegral,
    alternatingFirstJetPrimitive, Polynomial.map_neg, map_polyIntegral,
    map_finSuccEquiv_alternatingPlaneH]

theorem finSuccEquiv_binary_shift (p : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 1 (bind₁ ![X 0-X 1, X 1] p) =
      Polynomial.taylor (-X (0 : Fin 1)) (finSuccEquiv ℚ 1 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.taylor_mul, hp]
    fin_cases i <;>
      simp [finSuccEquiv_X_zero, finSuccEquiv_binary_X_one, sub_eq_add_neg]

/-- The actual first-jet equation descends to the exact binary polynomial ring. -/
theorem binaryFirstJetPrimitive_difference_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    bind₁ ![X 0-X 1, X 1] (binaryFirstJetPrimitive f) - binaryFirstJetPrimitive f =
      binaryBoundary f := by
  have h := congrArg (Polynomial.map dropThirdCoeff.toRingHom)
    (alternatingFirstJetDefect_eq_zero_of_todd_derivative hf hodd hc hs hJ)
  unfold alternatingFirstJetDefect at h
  rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_taylor,
    ← binaryFirstJetPrimitive_transport, map_finSuccEquiv_alternatingPlaneH,
    Polynomial.map_zero] at h
  have hu : dropThirdCoeff.toRingHom (-X (0 : Fin 2)) = -X (0 : Fin 1) := by
    simp [dropThirdCoeff]
  rw [hu] at h
  apply (finSuccEquiv ℚ 1).injective
  rw [map_sub, finSuccEquiv_binary_shift]
  exact sub_eq_zero.mp h

/-- The original norm relation gives the actual binary first-jet equation. -/
theorem binaryFirstJetPrimitive_difference {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    bind₁ ![X 0-X 1, X 1] (binaryFirstJetPrimitive f) - binaryFirstJetPrimitive f =
      binaryBoundary f :=
  binaryFirstJetPrimitive_difference_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

end TernaryPoly
