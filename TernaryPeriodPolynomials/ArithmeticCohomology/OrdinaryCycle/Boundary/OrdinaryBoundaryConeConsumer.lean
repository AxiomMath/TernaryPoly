module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalVanishing

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology OrdinaryParabolicGroups OrdinaryFaceRadical
open OrdinaryBoundaryCommonRoot OrdinaryCovectors PolynomialGLAction
open RadicalFirstCohomologyLattice

/-- Unconditional normal form for an actual cone cocycle on the two full integral parabolics.
The genuine radical-H1 vanishing theorems discharge both Hochschild–Serre premises. -/
theorem actual_normalized (n : ℕ) (e : ℤ) (c : actualCycles n e) :
    ∃ v : Coefficients n × Coefficients n,
      (∀ r : planeRadical, (gauge (actualCoefficients n e) P Q c v).val.1
        (planeEquiv (SemidirectProduct.inl r)) = 0) ∧
      (∀ g : P, (gauge (actualCoefficients n e) P Q c v).val.1 g ∈
        Representation.invariants ((coefficientAction n e).comp planeRadical.subtype)) ∧
      (∀ r : lineRadical, (gauge (actualCoefficients n e) P Q c v).val.2.1
        (lineEquiv (SemidirectProduct.inl r)) = 0) ∧
      (∀ g : Q, (gauge (actualCoefficients n e) P Q c v).val.2.1 g ∈
        Representation.invariants ((coefficientAction n e).comp lineRadical.subtype)) ∧
      (gauge (actualCoefficients n e) P Q c v).val.2.2 ∈ (commonRepresentation n e).invariants :=
  actual_normalized_of_vanishing n e (actualPlane_radical_H1_invariants_zero n e)
    (actualLine_radical_H1_invariants_zero n e) c

/-- Every actual cone H1 class has a representative with pairwise distinguished coefficients
on both full faces and their compatibility corner. This is an algebraic cone statement. -/
theorem actual_class_pairwise_representative (n : ℕ) (e : ℤ) (x : actualH1 n e) :
    ∃ c : actualCycles n e, classOf (actualCoefficients n e) P Q c = x ∧
      (∀ g : P, Pairwise (evaluation n (c.val.1 g) : Poly)) ∧
      (∀ g : Q, Pairwise (evaluation n (c.val.2.1 g) : Poly)) ∧
      Pairwise (evaluation n c.val.2.2 : Poly) :=
  actual_class_pairwise_representative_of_vanishing n e
    (actualPlane_radical_H1_invariants_zero n e) (actualLine_radical_H1_invariants_zero n e) x

/-- Every functional annihilating pairwise support vanishes on all distinguished coefficients
of a representative of every actual cone H1 class. -/
theorem actual_class_annihilator_representative (n : ℕ) (e : ℤ) (x : actualH1 n e)
    (lam : Module.Dual ℚ (HomogeneousPoly n))
    (hlam : ∀ p : HomogeneousPoly n, Pairwise (p : Poly) → lam p = 0) :
    ∃ c : actualCycles n e, classOf (actualCoefficients n e) P Q c = x ∧
      (∀ g : P, lam (evaluation n (c.val.1 g)) = 0) ∧
      (∀ g : Q, lam (evaluation n (c.val.2.1 g)) = 0) ∧
      lam (evaluation n c.val.2.2) = 0 := by
  obtain ⟨c,hc,hp,hq,hu⟩ := actual_class_pairwise_representative n e x
  exact ⟨c,hc,fun g => hlam _ (hp g),fun g => hlam _ (hq g),hlam _ hu⟩

end TernaryPoly.OrdinaryBoundaryCone
