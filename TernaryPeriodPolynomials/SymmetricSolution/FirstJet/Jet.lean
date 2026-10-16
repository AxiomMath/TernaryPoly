module

public import TernaryPeriodPolynomials.SymmetricSolution.FirstJet.JetFrames
public import TernaryPeriodPolynomials.SymmetricSolution.Todd
public import TernaryPeriodPolynomials.AlternatingSolution.FirstJetFormula
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Basic

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

private theorem normalPlaneCoeff_X_zero :
    normalPlaneCoeff (X (0 : Fin 2)) = X (0 : Fin 2) := by
  simp [normalPlaneCoeff]

private theorem normalPlaneCoeff_X_one :
    normalPlaneCoeff (X (1 : Fin 2)) = 3 * X (0 : Fin 2) := by
  simp [normalPlaneCoeff]

private theorem toddXComm_neg (u : ToddCoefficient) (p : Polynomial ToddCoefficient) :
    toddXComm u (-p) = -toddXComm u p := by
  simp only [toddXComm, mul_neg, map_neg]
  abel

/-- The actual first normal derivative of the symmetric Todd expression is the first-jet operator. -/
theorem symmetricTodd_firstJet_formula {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = f) :
    finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (symmetricTodd f))) =
      firstJetExpression (X (0 : Fin 2))
        (finSuccEquiv ℚ 2 (alternatingPlaneH f))
        (finSuccEquiv ℚ 2 (alternatingPlaneA1 f))
        (finSuccEquiv ℚ 2 (alternatingPlaneD1 f)) := by
  have hF1 := symmetricFrame1_odd_plane hf hn
  have hF2 := symmetricFrame2_plane hf hn hc hs
  have hdF1 := symmetricFrame1_first_derivative_plane hf hn
  have hdF2 := symmetricFrame2_first_derivative_plane hf hn hc hs
  change normalPlane (symmetricFrame1 f) = _ at hF1
  change normalPlane (symmetricFrame2 f) = _ at hF2
  change normalPlane (pderiv 2 (symmetricFrame1 f)) = _ at hdF1
  change normalPlane (pderiv 2 (symmetricFrame2 f)) = _ at hdF2
  have hbase :
      finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (symmetricTodd f))) =
        finSuccEquiv ℚ 2 (normalPlane (ternaryTodd (X (0 : Fin 2)) (symmetricFrame1 f))) +
        (3*X (0 : Fin 2) : ToddCoefficient) • finSuccEquiv ℚ 2
          (normalPlane (pderiv 2 (ternaryTodd (X (0 : Fin 2)) (symmetricFrame1 f)))) -
        (X (0 : Fin 2) : ToddCoefficient) • finSuccEquiv ℚ 2
          (normalPlane (pderiv 2 (ternaryTodd (X (1 : Fin 2)) (symmetricFrame2 f)))) := by
    simp [symmetricTodd, normalPlane, Polynomial.smul_eq_C_mul,
      finSuccEquiv_ternary_X_one, map_ofNat, add_comm]
  rw [hbase, pderiv_two_ternaryTodd_Y,
    normalPlane_ternaryTodd_Z_parameter, finSuccEquiv_normalPlane_ternaryTodd,
    finSuccEquiv_normalPlane_ternaryTodd, normalPlaneCoeff_X_zero,
    hF1, hF2, hdF1, hdF2]
  simp only [map_neg, map_add, map_sub, finSuccEquiv_shift_one_Y,
    finSuccEquiv_shift_two_Y, toddXComm_neg, smul_neg]
  have ht := firstJet_frame_terms (X (0 : Fin 2) : ToddCoefficient)
    (finSuccEquiv ℚ 2 (alternatingPlaneA1 f))
    (finSuccEquiv ℚ 2 (alternatingPlaneD1 f))
  unfold firstJetExpression
  simp only [map_add, map_sub] at ht ⊢
  linear_combination ht


/-- The first normal derivative is the invertibly transported literal first-plane defect. -/
theorem symmetricTodd_firstJet_eq_transport {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = f) :
    finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (symmetricTodd f))) =
      Polynomial.taylor (-(2*X (0 : Fin 2)))
        (todd (3*X (0 : Fin 2)) (todd (X (0 : Fin 2)) (alternatingFirstJetDefect f))) := by
  rw [symmetricTodd_firstJet_formula hf hn hc hs,
    firstJetExpression_eq (X (0 : Fin 2)) (alternatingFirstJetPrimitive f)
      _ _ _ (alternatingPlane_integral_derivative f)]
  rfl

/-- Whole symmetric Todd vanishing kills the entire first-plane defect. -/
theorem symmetricFirstJetDefect_eq_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = f)
    (hJ : symmetricTodd f = 0) : alternatingFirstJetDefect f = 0 := by
  have h := symmetricTodd_firstJet_eq_transport hf hn hc hs
  rw [hJ] at h
  simp only [map_zero] at h
  apply todd_injective (X (0 : Fin 2))
  apply todd_injective (3*X (0 : Fin 2))
  apply Polynomial.taylor_injective (-(2*X (0 : Fin 2)))
  simpa only [map_zero] using h.symm

/-- The exact binary difference equation required by symmetric period extraction. -/
theorem symmetricBinaryFirstJetPrimitive_difference {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = f)
    (hJ : symmetricTodd f = 0) :
    bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f)-binaryFirstJetPrimitive f =
      binaryBoundary f := by
  have h := congrArg (Polynomial.map dropThirdCoeff.toRingHom)
    (symmetricFirstJetDefect_eq_zero hf hn hc hs hJ)
  unfold alternatingFirstJetDefect at h
  rw [Polynomial.map_sub,Polynomial.map_sub,Polynomial.map_taylor,
    ← binaryFirstJetPrimitive_transport,map_finSuccEquiv_alternatingPlaneH,
    Polynomial.map_zero] at h
  have hu : dropThirdCoeff.toRingHom (-X (0 : Fin 2)) = -X (0 : Fin 1) := by
    simp [dropThirdCoeff]
  rw [hu] at h
  apply (finSuccEquiv ℚ 1).injective
  rw [map_sub,finSuccEquiv_binary_shift]
  exact sub_eq_zero.mp h

end TernaryPoly
