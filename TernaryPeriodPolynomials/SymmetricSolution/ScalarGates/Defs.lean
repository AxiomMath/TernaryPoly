module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.AlternatingExtension
public import TernaryPeriodPolynomials.SymmetricSolution.AllDegreeOrdinaryExtension
public import TernaryPeriodPolynomials.SymmetricSolution.Scalar
public import TernaryPeriodPolynomials.AlternatingSolution.OddDegree.Vanishing
public import TernaryPeriodPolynomials.Polynomial.Reduction

@[expose] public section


noncomputable section
namespace TernaryPoly.ScalarGates

/-- Literal reference evaluation of a genuine homogeneous functional on actual ordinary cycles. -/
def referenceValue (n : ℕ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n) :
    TernaryPolynomial :=
  (Φ (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)).val

/-- Equivariance for the actual ordinary-cycle action and exact determinant exponent e. -/
def Equivariant (n : ℕ) (e : ℤ)
    (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n) : Prop :=
  ∀ k z,Φ (OrdinaryIncidenceChains.complex.cyclesAction k z)=
    GoodChainComplex.coefficientAction n e k (Φ z)

/-- The scalar vanishing statement: the complete symmetric scalar vanishes in positive degree. -/
def ScalarZero : Prop :=
  ∀ n (f : TernaryPolynomial),0<n → f.IsHomogeneous n →
    PeriodRelations f → S f=f → symmetricScalar f=0

/-- The ordinary-support statement for both required determinant characters.
The literal exponents are 0 (untwisted) and -1 (determinant), not 1 and -1. -/
def OrdinaryReferencePairwise : Prop :=
  ∀ n,0<n → ∀ (e : ℤ),e=0 ∨ e= -1 →
    ∀ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      Equivariant n e Φ → Pairwise (referenceValue n Φ)

/-- A weaker support assertion suffices: only actual sector-compatible reference
values are tested, with even degree in the untwisted alternating case. -/
def SectorReferencePairwise : Prop :=
  (∀ n,0<n →
    ∀ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      Equivariant n (-1) Φ → PeriodRelations (referenceValue n Φ) →
      S (referenceValue n Φ)=referenceValue n Φ → symmetricTodd (referenceValue n Φ)=0 →
      Pairwise (referenceValue n Φ)) ∧
  (∀ n,0<n → Even n →
    ∀ Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      Equivariant n 0 Φ → PeriodRelations (referenceValue n Φ) →
      S (referenceValue n Φ)= -referenceValue n Φ → Pairwise (referenceValue n Φ))

/-- Full actual ordinary-reference support implies the precise weaker sector assertion. -/
theorem sectorReferencePairwise_of_ordinary (h : OrdinaryReferencePairwise) :
    SectorReferencePairwise := by
  constructor
  · intro n hn Φ hΦ _ _ _
    exact h n hn (-1) (Or.inr rfl) Φ hΦ
  · intro n hn _ Φ hΦ _ _
    exact h n hn 0 (Or.inl rfl) Φ hΦ

/-- The complete scalar-zero assertion supplies the entire Todd-zero hypothesis. -/
theorem todd_zero_of_scalar_gate (h : ScalarZero) {n : ℕ} {f : TernaryPolynomial}
    (hn : 0<n) (hf : f.IsHomogeneous n) (hrel : PeriodRelations f) (hs : S f=f) :
    symmetricTodd f=0 :=
  symmetricTodd_zero_of_scalar_zero hrel hs (h n f hn hf hrel hs)

end TernaryPoly.ScalarGates
