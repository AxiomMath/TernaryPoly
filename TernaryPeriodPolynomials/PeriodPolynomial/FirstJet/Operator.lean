module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Commutator
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Injective
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Constant

@[expose] public section


open Polynomial
noncomputable section
namespace TernaryPoly
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The first normal derivative after the frame and parameter derivative calculations. -/
def firstJetExpression (y : R) (h a d : Polynomial R) : Polynomial R :=
  -todd y h + (algebraMap ℚ R (1/3)) •
      toddXComm (3*y) (derivative (h + taylor (-y) h + taylor (-(2*y)) h)) +
    y • taylor (-(2*y)) (todd (3*y) (a+d))

/-- The scalar Bernoulli identity turns the first jet into the transported defect. -/
theorem firstJetExpression_eq [IsDomain R]
    (y : R) (p h a d : Polynomial R)
    (hpd : derivative p + derivative h = -(a+d)) :
    firstJetExpression y h a d =
      taylor (-(2*y)) (todd (3*y) (todd y (taylor (-y) p-p-h))) := by
  have hs := todd_scalar_firstJet y h
  rw [derivative_taylor, derivative_todd] at hs
  have had : a+d = -(derivative p + derivative h) := by rw [hpd, neg_neg]
  have hr : taylor (-(2*y)) (todd (3*y) (todd y (taylor (-y) p-p-h))) =
      (-y) • taylor (-(2*y)) (todd (3*y) (derivative p)) -
        taylor (-(2*y)) (todd (3*y) (todd y h)) := by
    rw [map_sub (todd y), todd_difference]
    simp only [map_sub, map_smul]
  rw [hr, firstJetExpression, had]
  simp only [map_neg, map_add, smul_neg, smul_add, neg_smul] at hs ⊢
  linear_combination hs

/-- The transported defect has zero derivative exactly when the defect does. -/
theorem firstJet_transport_derivative_eq_zero (y : R) (c : Polynomial R)
    (hc : derivative (taylor (-(2*y)) (todd (3*y) (todd y c))) = 0) :
    derivative c = 0 := by
  rw [derivative_taylor, derivative_todd, derivative_todd] at hc
  apply todd_injective y
  apply todd_injective (3*y)
  apply taylor_injective (-(2*y))
  simpa only [map_zero] using hc

end TernaryPoly
