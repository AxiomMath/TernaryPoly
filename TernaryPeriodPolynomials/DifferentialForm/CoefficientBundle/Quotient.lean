module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Core

@[expose] public section


/-! Identification of the glued bundle with the literal diagonal arithmetic orbit quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology Bundle
open scoped ContDiff Manifold

instance diagonalAction (n : ℕ) : MulAction DeckGroup (Space × Coefficients n) where
  smul g z := (g • z.1, coefficientAction n g z.2)
  one_smul z := by
    change (1 • z.1, coefficientAction n 1 z.2) = z
    simp
  mul_smul g h z := by
    change ((g*h) • z.1, coefficientAction n (g*h) z.2) =
      (g • (h • z.1), coefficientAction n g (coefficientAction n h z.2))
    simp only [mul_smul, coefficientAction_mul]

instance diagonalSMul (n : ℕ) : SMul DeckGroup (Space × Coefficients n) :=
  (diagonalAction n).toSMul

@[simp] theorem diagonal_smul (n : ℕ) (g : DeckGroup) (S : Space) (p : Coefficients n) :
    (g • (S,p) : Space × Coefficients n) = (g • S, coefficientAction n g p) := rfl

abbrev Associated (n : ℕ) := Quotient (MulAction.orbitRel DeckGroup (Space × Coefficients n))

def orbitClass (n : ℕ) (S : Space) (p : Coefficients n) : Associated n := Quotient.mk _ (S,p)

theorem orbitClass_smul (n : ℕ) (g : DeckGroup) (S : Space) (p : Coefficients n) :
    orbitClass n (g • S) (coefficientAction n g p) = orbitClass n S p := by
  apply Quotient.sound
  exact ⟨g,rfl⟩

theorem deckBetween_smul_left (S T : Space) (g : DeckGroup)
    (h : quotientProjection T = quotientProjection S) :
    deckBetween (g • S) T * g = deckBetween S T := by
  symm
  apply deckBetween_unique
  rw [mul_smul, deckBetween_spec]
  simpa only [quotientProjection_quotientCovering.map_smul] using h

def liftToTotal (n : ℕ) (z : Space × Coefficients n) : Total n :=
  ⟨quotientProjection z.1, coefficientAction n (deckBetween z.1 (chosenLift (quotientProjection z.1))) z.2⟩

theorem liftToTotal_smul (n : ℕ) (g : DeckGroup) (z : Space × Coefficients n) :
    liftToTotal n (g • z : Space × Coefficients n) = liftToTotal n z := by
  rcases z with ⟨S,p⟩
  apply TotalSpace.ext (quotientProjection_quotientCovering.map_smul g)
  apply heq_of_eq
  change coefficientAction n (deckBetween (g • S) (chosenLift (quotientProjection (g • S))))
    (coefficientAction n g p) = coefficientAction n (deckBetween S (chosenLift (quotientProjection S))) p
  rw [quotientProjection_quotientCovering.map_smul, ← coefficientAction_mul,
    deckBetween_smul_left S _ g (chosenLift_projection _)]

def quotientToTotal (n : ℕ) : Associated n → Total n :=
  Quotient.lift (liftToTotal n) (by
    intro a b h
    obtain ⟨g,hg⟩ := h
    rw [← hg]
    exact liftToTotal_smul n g b)

@[simp] theorem quotientToTotal_class (n : ℕ) (S : Space) (p : Coefficients n) :
    quotientToTotal n (orbitClass n S p) = liftToTotal n (S,p) := rfl

def totalToQuotient (n : ℕ) (z : Total n) : Associated n := orbitClass n (chosenLift z.proj) z.snd

@[simp] theorem quotientToTotal_totalToQuotient (n : ℕ) (z : Total n) :
    quotientToTotal n (totalToQuotient n z) = z := by
  rcases z with ⟨b,p⟩
  change Coefficients n at p
  apply TotalSpace.ext (chosenLift_projection b)
  apply heq_of_eq
  change coefficientAction n (deckBetween (chosenLift b) (chosenLift (quotientProjection (chosenLift b)))) p = p
  rw [chosenLift_projection, deckBetween_self, coefficientAction_one]

@[simp] theorem totalToQuotient_quotientToTotal (n : ℕ) (z : Associated n) :
    totalToQuotient n (quotientToTotal n z) = z := by
  induction z using Quotient.inductionOn with
  | h z =>
    rcases z with ⟨S,p⟩
    change orbitClass n (chosenLift (quotientProjection S))
      (coefficientAction n (deckBetween S (chosenLift (quotientProjection S))) p) = orbitClass n S p
    have h := orbitClass_smul n (deckBetween S (chosenLift (quotientProjection S))) S p
    rw [deckBetween_spec S (chosenLift (quotientProjection S)) (chosenLift_projection _)] at h
    exact h

def associatedEquiv (n : ℕ) : Associated n ≃ Total n where
  toFun := quotientToTotal n
  invFun := totalToQuotient n
  left_inv := totalToQuotient_quotientToTotal n
  right_inv := quotientToTotal_totalToQuotient n

end TernaryPoly.PolynomialCoefficientBundle
