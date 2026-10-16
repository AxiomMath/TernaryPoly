module

public import TernaryPeriodPolynomials.AlternatingSolution.ToddPlane
public import TernaryPeriodPolynomials.AlternatingSolution.FirstDerivativeFrames
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Operator
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Parameter

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly

/-- Coefficient specialization respects the canonical Todd commutator. -/
theorem map_toddXComm {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (u : R) (p : Polynomial R) :
    Polynomial.map φ.toRingHom (toddXComm u p) =
      toddXComm (φ u) (Polynomial.map φ.toRingHom p) := by
  simp only [toddXComm, Polynomial.map_sub, map_todd, Polynomial.map_mul, Polynomial.map_X]

private theorem normalPlaneCoeff_X_zero :
    normalPlaneCoeff (X (0 : Fin 2)) = X (0 : Fin 2) := by
  simp [normalPlaneCoeff]

private theorem normalPlaneCoeff_X_one :
    normalPlaneCoeff (X (1 : Fin 2)) = 3 * X (0 : Fin 2) := by
  simp [normalPlaneCoeff]

/-- The frame-derivative terms reduce to the translated sum of the two boundary partials. -/
theorem firstJet_frame_terms {R : Type*} [CommRing R] [Algebra ℚ R] [IsDomain R]
    (y : R) (a d : Polynomial R) :
    (3*y) • todd y a - y • todd (3*y)
        (a + Polynomial.taylor (-y) a - Polynomial.taylor (-(2*y)) d) =
      y • Polynomial.taylor (-(2*y)) (todd (3*y) (a+d)) := by
  have ht := todd_three_mul y a
  simp only [map_add, ← taylor_todd] at ht
  simp only [map_sub, map_add, ← taylor_todd, smul_sub, smul_add,
    Polynomial.smul_eq_C_mul, map_mul, map_ofNat] at ht ⊢
  linear_combination -Polynomial.C y * ht

/-- The scaled coefficient derivative supplies precisely the weighted parameter term on the plane. -/
theorem normalPlane_ternaryTodd_Z_parameter (f : TernaryPolynomial) :
    (X (0 : Fin 2) : ToddCoefficient) •
        finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (ternaryTodd (X (1 : Fin 2)) f))) =
      (X (0 : Fin 2) : ToddCoefficient) • todd (3*X (0 : Fin 2))
        (finSuccEquiv ℚ 2 (normalPlane (pderiv 2 f))) +
      (algebraMap ℚ ToddCoefficient (1/3)) • toddXComm (3*X (0 : Fin 2))
        (Polynomial.derivative (finSuccEquiv ℚ 2 (normalPlane f))) := by
  have h := congrArg (Polynomial.map normalPlaneCoeff.toRingHom)
    (ternaryTodd_Z_parameter_derivative f)
  simp only [Polynomial.map_smul, Polynomial.map_sub, map_todd, map_toddXComm,
    ← Polynomial.derivative_map, normalPlaneCoeff_X_one,
    ← finSuccEquiv_normalPlane] at h
  rw [show normalPlaneCoeff.toRingHom (X (1 : Fin 2)) = 3 * X (0 : Fin 2) from
    normalPlaneCoeff_X_one] at h
  have hthird : algebraMap ℚ ToddCoefficient (1/3) * (3*X (0 : Fin 2)) =
      X (0 : Fin 2) := by
    have he := congrArg (algebraMap ℚ ToddCoefficient)
      (show (1/3 : ℚ)*3 = 1 by norm_num)
    simp only [map_mul, map_ofNat, map_one] at he
    rw [← mul_assoc, he, one_mul]
  have ht := congrArg (fun q : Polynomial ToddCoefficient =>
    algebraMap ℚ ToddCoefficient (1/3) • q) h
  rw [smul_smul, hthird, smul_sub] at ht
  exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)

private theorem toddXComm_neg (u : ToddCoefficient) (p : Polynomial ToddCoefficient) :
    toddXComm u (-p) = -toddXComm u p := by
  simp only [toddXComm, mul_neg, map_neg]
  abel

/-- The actual first normal derivative of the alternating Todd expression is the first-jet operator. -/
theorem alternatingTodd_firstJet_formula {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = -f) :
    finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f))) =
      firstJetExpression (X (0 : Fin 2))
        (finSuccEquiv ℚ 2 (alternatingPlaneH f))
        (finSuccEquiv ℚ 2 (alternatingPlaneA1 f))
        (finSuccEquiv ℚ 2 (alternatingPlaneD1 f)) := by
  have hF1 := alternatingFrame1_plane hf hn
  have hF2 := alternatingFrame2_plane hf hn hc hs
  have hdF1 := alternatingFrame1_first_derivative_plane hf hn
  have hdF2 := alternatingFrame2_first_derivative_plane hf hn hc hs
  change normalPlane (alternatingFrame1 f) = _ at hF1
  change normalPlane (alternatingFrame2 f) = _ at hF2
  change normalPlane (pderiv 2 (alternatingFrame1 f)) = _ at hdF1
  change normalPlane (pderiv 2 (alternatingFrame2 f)) = _ at hdF2
  have hbase :
      finSuccEquiv ℚ 2 (normalPlane (pderiv 2 (alternatingTodd f))) =
        finSuccEquiv ℚ 2 (normalPlane (ternaryTodd (X (0 : Fin 2)) (alternatingFrame1 f))) +
        (3*X (0 : Fin 2) : ToddCoefficient) • finSuccEquiv ℚ 2
          (normalPlane (pderiv 2 (ternaryTodd (X (0 : Fin 2)) (alternatingFrame1 f)))) -
        (X (0 : Fin 2) : ToddCoefficient) • finSuccEquiv ℚ 2
          (normalPlane (pderiv 2 (ternaryTodd (X (1 : Fin 2)) (alternatingFrame2 f)))) := by
    simp [alternatingTodd, normalPlane, Polynomial.smul_eq_C_mul,
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

end TernaryPoly
