module

public import TernaryPeriodPolynomials.AlternatingSolution.ToddPlane
public import TernaryPeriodPolynomials.AlternatingSolution.PlaneDifferential
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Operator
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Parity
public import TernaryPeriodPolynomials.AlternatingSolution.FirstJetFormula

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Mixed partial derivatives commute in the exact ternary polynomial ring. -/
theorem ternary_pderiv_commute (i j : Fin 3) (f : TernaryPolynomial) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · ext d
    simp only [coeff_pderiv]
    simp [Finsupp.add_apply, hij, Ne.symm hij,
      add_comm, add_left_comm, mul_comm, mul_left_comm]

/-- Normal-plane specialization commutes with differentiation in the first coordinate. -/
theorem normalPlane_pderiv_zero (f : TernaryPolynomial) :
    normalPlane (pderiv 0 f) = pderiv 0 (normalPlane f) := by
  apply (finSuccEquiv ℚ 2).injective
  rw [finSuccEquiv_normalPlane, finSuccEquiv_pderiv_zero, finSuccEquiv_pderiv_zero,
    finSuccEquiv_normalPlane, Polynomial.derivative_map]

/-- The first normal derivative of the Todd expression is constant in the first variable. -/
theorem alternatingTodd_firstJet_derivative_zero_of_todd_derivative {f : TernaryPolynomial}
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    Polynomial.derivative (finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f)))) = 0 := by
  rw [← finSuccEquiv_pderiv_zero, ← normalPlane_pderiv_zero,
    ternary_pderiv_commute, hJ]
  simp

/-- The norm relation supplies the Todd derivative vanishing used by the first jet. -/
theorem alternatingTodd_firstJet_derivative_zero {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    Polynomial.derivative (finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f)))) = 0 :=
  alternatingTodd_firstJet_derivative_zero_of_todd_derivative
    (pderiv_zero_alternatingTodd hc hs hn)

/-- The normalized primitive of the first pair of boundary partial derivatives. -/
def alternatingFirstJetPrimitive (f : TernaryPolynomial) :
    Polynomial (MvPolynomial (Fin 2) ℚ) :=
  -polyIntegral (finSuccEquiv ℚ 2 (alternatingPlaneH (pderiv 0 f+pderiv 1 f)))

/-- The binary first-jet defect before the period-polynomial extraction. -/
def alternatingFirstJetDefect (f : TernaryPolynomial) :
    Polynomial (MvPolynomial (Fin 2) ℚ) :=
  Polynomial.taylor (-X (0 : Fin 2)) (alternatingFirstJetPrimitive f) -
    alternatingFirstJetPrimitive f - finSuccEquiv ℚ 2 (alternatingPlaneH f)

/-- Todd derivative vanishing kills the first-jet defect once its normal derivative formula is known. -/
theorem alternatingFirstJetDefect_eq_zero_of_formula_of_todd_derivative {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) (hJ : pderiv 0 (alternatingTodd f) = 0)
    (hformula : finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f))) =
      firstJetExpression (X (0 : Fin 2)) (finSuccEquiv ℚ 2 (alternatingPlaneH f))
        (finSuccEquiv ℚ 2 (alternatingPlaneA1 f))
        (finSuccEquiv ℚ 2 (alternatingPlaneD1 f))) :
    alternatingFirstJetDefect f = 0 := by
  have hd := alternatingTodd_firstJet_derivative_zero_of_todd_derivative hJ
  rw [hformula, firstJetExpression_eq (X (0 : Fin 2)) (alternatingFirstJetPrimitive f)
    _ _ _ (alternatingPlane_integral_derivative f)] at hd
  have hdef := firstJet_transport_derivative_eq_zero (X (0 : Fin 2)) _ hd
  exact firstJet_constant_eq_zero _ _ _ _
    (by simp [alternatingFirstJetPrimitive])
    (by simp [alternatingFirstJetPrimitive])
    (alternatingPlaneH_derivative_reflection hc hs)
    (alternatingPlaneH_eval_endpoints hc hs) hdef

/-- The norm form of the first-jet defect criterion. -/
theorem alternatingFirstJetDefect_eq_zero_of_formula {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0)
    (hformula : finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f))) =
      firstJetExpression (X (0 : Fin 2)) (finSuccEquiv ℚ 2 (alternatingPlaneH f))
        (finSuccEquiv ℚ 2 (alternatingPlaneA1 f))
        (finSuccEquiv ℚ 2 (alternatingPlaneD1 f))) :
    alternatingFirstJetDefect f = 0 :=
  alternatingFirstJetDefect_eq_zero_of_formula_of_todd_derivative hc hs
    (pderiv_zero_alternatingTodd hc hs hn) hformula

/-- The complete first normal derivative is the invertibly transported binary defect. -/
theorem alternatingTodd_firstJet_eq_transport {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = -f) :
    finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f))) =
      Polynomial.taylor (-(2*X (0 : Fin 2)))
        (todd (3*X (0 : Fin 2)) (todd (X (0 : Fin 2)) (alternatingFirstJetDefect f))) := by
  rw [alternatingTodd_firstJet_formula hf hn hc hs,
    firstJetExpression_eq (X (0 : Fin 2)) (alternatingFirstJetPrimitive f)
      _ _ _ (alternatingPlane_integral_derivative f)]
  rfl

/-- Todd derivative vanishing forces the entire first-jet defect to vanish. -/
theorem alternatingFirstJetDefect_eq_zero_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) : alternatingFirstJetDefect f = 0 :=
  alternatingFirstJetDefect_eq_zero_of_formula_of_todd_derivative hc hs hJ
    (alternatingTodd_firstJet_formula hf hodd hc hs)

/-- The original odd alternating norm equations kill the first-jet defect. -/
theorem alternatingFirstJetDefect_eq_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) : alternatingFirstJetDefect f = 0 :=
  alternatingFirstJetDefect_eq_zero_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

/-- The normal derivative also vanishes on the plane; no constant mode survives. -/
theorem alternatingTodd_first_normal_vanishes_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) : normalPlane (pderiv 2 (alternatingTodd f)) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [alternatingTodd_firstJet_eq_transport hf hodd hc hs,
    alternatingFirstJetDefect_eq_zero_of_todd_derivative hf hodd hc hs hJ]
  simp

/-- The norm form of first normal vanishing. -/
theorem alternatingTodd_first_normal_vanishes {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) : normalPlane (pderiv 2 (alternatingTodd f)) = 0 :=
  alternatingTodd_first_normal_vanishes_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

/-- The actual first-jet primitive is even in the integration variable. -/
theorem alternatingFirstJetPrimitive_even_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    (alternatingFirstJetPrimitive f).comp (-Polynomial.X) = alternatingFirstJetPrimitive f := by
  apply firstJet_primitive_even (X (0 : Fin 2)) (alternatingFirstJetPrimitive f)
    (finSuccEquiv ℚ 2 (alternatingPlaneH f))
    (finSuccEquiv ℚ 2 (alternatingPlaneH (pderiv 0 f+pderiv 1 f)))
  · simp [alternatingFirstJetPrimitive]
  · exact alternatingPlaneH_derivative_reflection hc hs
  · change Polynomial.derivative (alternatingFirstJetDefect f) = 0
    rw [alternatingFirstJetDefect_eq_zero_of_todd_derivative hf hodd hc hs hJ, map_zero]

/-- The norm form of parity of the first-jet primitive. -/
theorem alternatingFirstJetPrimitive_even {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    (alternatingFirstJetPrimitive f).comp (-Polynomial.X) = alternatingFirstJetPrimitive f :=
  alternatingFirstJetPrimitive_even_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

end TernaryPoly
