module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.LocalBadPlane
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

@[expose] public section


/-! Concrete intermediate objects for the decomposition of the five paper statements. -/

noncomputable section
namespace GeneralEisenstein
open Matrix Homogeneous Adelic

abbrev BoundaryHecke (n : ℕ) (χ : RankOneCharacter) :=
  (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n χ side)

def ActualBoundaryHecke (n : ℕ) (χ : RankOneCharacter) (hecke : BoundaryHecke n χ) : Prop :=
  ∀ side, RealizesHecke (flagRepresentation (rationalCoefficientComponent n χ) side) (hecke side)

/-- Normalization is a property of the actual chosen cochain, including pure
radical/Levi vanishing and all three displayed binary generator coordinates. -/
def NormalizedBadLine {n : ℕ} (f : HomogeneousPoly n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  PureMixedBadLine c ∧ mixedBernoulliCoordinate c binaryA = -bernoulliObstruction f ∧
    mixedBernoulliCoordinate c binaryB = 0 ∧ mixedBernoulliCoordinate c binaryR = 0

/-- Span of the line images of independently realized cuspidal representations. -/
def automorphicLineSpan (n : ℕ) : Submodule ℂ (StratumH2 n trivialCharacter .line) :=
  Submodule.span ℂ {a | ∃ D : CohomologicalCuspData n, a ∈ boundarySummand D.inducingData .line}

/-- Rational numbers integral at three, with an explicit prime-to-three denominator. -/
def IntegralAtThree (x : ℚ) : Prop :=
  ∃ a b : ℤ, (b : ZMod 3) ≠ 0 ∧ x = (a : ℚ) / (b : ℚ)

/-- A genuine rational correspondence whose local component at three belongs
to K₁: both matrices are integral, and the last row is e₃* modulo three. -/
def AwayThree (t : HeckeCorrespondence) : Prop :=
  (∀ i j, IntegralAtThree (t.g.val i j) ∧ IntegralAtThree ((t.g⁻¹).val i j)) ∧
    ∀ j, IntegralAtThree ((t.g.val 2 j - if j = 2 then 1 else 0) / 3)

/-- Finite algebraic combinations of actual Hecke operators away from three. -/
def awayThreeHeckeAlgebra {n : ℕ} (D : InducingData n) (hecke : BoundaryHecke n D.chi) :
    Subalgebra ℂ (Module.End ℂ (BoundaryCoordinates n D.chi)) :=
  Algebra.adjoin ℂ {A | ∃ t, AwayThree t ∧ A = pairHecke D hecke t}

abbrev SourceCochain (n : ℕ) :=
  (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n

/-- Literal finite-cusp support for every smooth archimedean translate. -/
def BadPlaneSource {n : ℕ} (c : SourceCochain n) : Prop :=
  ∀ x : Fin 3 → RealGL3, ∀ q : RationalGL3, GoodFlag .plane (QuotientGroup.mk q) →
    ∀ h : RealGL3, c x (rationalGroup q⁻¹ * atInfinity h) = 0

/-- A representative in the same independent constituent, not a substitute
space of equal dimension or a representative in a different automorphic W. -/
def BadPlaneRepresentative {n : ℕ} (D : InducingData n) (ξ : boundarySummand D .plane) : Prop :=
  ∃ (c : SourceCochain n) (z : MaximalCycles n D.chi .plane),
    IsSourceCocycle D .plane c ∧ Evaluates D .plane c z ∧
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z =
      ξ.val ∧ BadPlaneSource c

/-- A nonzero actual smooth vector fixed by GL₂(Zhat), hence level one. -/
def SphericalCusp (σ : CuspidalRepresentation) : Prop :=
  ∃ v : σ.smooth, v ≠ 0 ∧ ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v.val = v.val

/-- Repair only the value at the cohomological point; preserve the supplied
meromorphic continuation everywhere else. This avoids falsely demanding that
every arbitrary meromorphic representative already have its removable value. -/
def SameOffCohomologicalPoint (E E' : ℂ → AdelicGL → ℂ) : Prop :=
  ∀ s, s ≠ cohomologicalPoint → ∀ g, E' s g = E s g

end GeneralEisenstein
end
