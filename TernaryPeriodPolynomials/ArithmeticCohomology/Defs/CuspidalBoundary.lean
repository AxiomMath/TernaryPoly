module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Graph

@[expose] public section


/-!
# Concrete boundary conditions for the polynomial paper

Goodness uses the saturated integral lattice in a rational subspace, rather
than a chosen frame modulo three. Vanishing is a cohomological condition:
the restriction must be an actual coboundary, not zero at a chosen vector.
The recognition conclusion constructs the independent automorphic constituents
and their genuine Hecke projectors, and recovers the whole line coordinate.
-/

noncomputable section
namespace GeneralEisenstein
open Matrix Homogeneous

/-- The paper's unramified, weight-zero rank-one character. -/
def trivialCharacter : RankOneCharacter where
  toMonoidHom := 1
  continuous := continuous_const
  unitary := by intro t; simp
  rational := by intro q; rfl
  positiveReal := by intro t ht; rfl

/-- Independent cuspidal data in the paper's rank-one character sector.
There is no boundary/source identification among the input fields. -/
structure CohomologicalCuspData (n : ℕ) where
  cusp : CuspidalRepresentation
  cohomological : Cohomological cusp n

abbrev CohomologicalCuspData.inducingData {n : ℕ} (D : CohomologicalCuspData n) : InducingData n :=
  ⟨D.cusp, trivialCharacter, D.cohomological⟩

/-- An integral vector in the rational subspace represented by a maximal flag.
For a plane the first two columns span the subspace; for a line only the first
column does. Existential quantification avoids choosing a lattice basis. -/
def IntegralVectorInFlag (side : Side) (q : Flags side) (v : Fin 3 → ℤ) : Prop :=
  ∃ g : RationalGL3, QuotientGroup.mk g = q ∧
    ∃ w : Fin 3 → ℚ,
      (match side with
       | .plane => w 2 = 0
       | .line => w 1 = 0 ∧ w 2 = 0) ∧
      g.val *ᵥ w = fun i => (v i : ℚ)

/-- The reduction of the saturated lattice is not annihilated by e₃*. -/
def GoodFlag (side : Side) (q : Flags side) : Prop :=
  ∃ v : Fin 3 → ℤ, IntegralVectorInFlag side q v ∧ (v 2 : ZMod 3) ≠ 0

/-- A class restricts to zero at every good cusp. The one-cochain witnesses
literal coboundary vanishing on all homogeneous representatives at those flags. -/
def VanishesOnGood (n : ℕ) (χ : RankOneCharacter) (side : Side)
    (a : StratumH2 n χ side) : Prop :=
  ∃ z : MaximalCycles n χ side,
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side) z = a ∧
    ∃ u : MaximalCochains n χ side 1, ∀ x q, GoodFlag side q →
      z.val.val x q = (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) side) u).val x q

/-- Inner maximal-stratum cohomology: restriction to every complete flag is
an actual coboundary in the full arithmetic Borel cochain module. -/
def InnerBoundary (n : ℕ) (χ : RankOneCharacter) (side : Side)
    (a : StratumH2 n χ side) : Prop :=
  ∃ z : MaximalCycles n χ side,
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side) z = a ∧
    ∃ u : EdgeCochains n χ 1, ∀ x e,
      z.val.val x (endpoint side e) =
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n χ) Edges) u).val x e

/-- Both maximal coordinates vanish at every good vertex. -/
def GoodBoundaryVanishing (n : ℕ) (χ : RankOneCharacter)
    (b : BoundaryCoordinates n χ) : Prop :=
  VanishesOnGood n χ .plane b.1 ∧ VanishesOnGood n χ .line b.2

/-- The maximal coordinates of the restriction of a literal global cocycle. -/
def globalCoordinates (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    BoundaryCoordinates n χ :=
  (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane)
      (restrictionCocycle n χ .plane c),
   classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
      (restrictionCocycle n χ .line c))

/-- Recognition is an output, including finite spectral decomposition of the
actual line coordinate. It is not an assumed dictionary between two spaces of
equal dimension. Each projector is tied to the actual double-coset actions. -/
def CuspidalRecognition (n : ℕ)
    (b : BoundaryCoordinates n trivialCharacter) : Prop :=
  ∃ (hecke : (side : Side) → HeckeCorrespondence →
      Module.End ℂ (StratumH2 n trivialCharacter side)),
    (∀ side, RealizesHecke
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      (hecke side)) ∧
    ∃ (m : ℕ) (D : Fin m → CohomologicalCuspData n)
      (p : Fin m → Module.End ℂ (BoundaryCoordinates n trivialCharacter)),
      (∀ i, IsIsotypicalProjection (D i).inducingData hecke (p i)) ∧
      ∑ i, (p i b).2 = b.2

end GeneralEisenstein
end
