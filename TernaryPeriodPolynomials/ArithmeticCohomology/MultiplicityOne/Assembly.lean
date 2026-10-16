module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Reduction

@[expose] public section


/-!
# Assembly of the prime-three input at the identity plane

The consumer form of `SphericalForcedByLocal` asks it only for a nonzero pair. For the trivial
character the even-degree case holds outright (`sphericalForcedByLocal_of_even`). In odd degree a
non-spherical `D` with a nonzero pair has a nonzero level-three vector (`spherical_or_levelThree`);
the two inputs are

* `LevelThreeBridge`: such a vector produces a nonzero holomorphic level-three vector of weight
  `n + 3` (the level-three version of `cohomological_exists_spherical_holomorphic`);
* `LevelThreeMatching n`: a nonzero holomorphic level-three vector of a non-spherical `D` cannot
  coexist with a nonzero local joint eigenspace of the pair character at the identity plane
  (its classical form is a level-three eigenform with the eigenvalues of a level-one eigenform, and
  both of its traces to level one vanish, so it is zero by the Petersson argument).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- A nonzero level-three vector of a cohomological datum of odd degree gives a nonzero holomorphic
level-three vector of weight `degree + 3`. -/
def LevelThreeBridge : Prop :=
  ∀ (σ : CuspidalRepresentation) (degree : ℕ), Odd degree → Cohomological σ degree →
    (∃ v : σ.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues σ) →
      ∃ halfWeight : ℤ, 2 * halfWeight = -((degree : ℤ) + 3) ∧
        ∃ v ∈ levelThreeClassicalVectors σ halfWeight, v ≠ 0

/-- The matching input at the identity plane in degree `n`. -/
def LevelThreeMatching (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), D.chi = trivialCharacter →
    associatePair D ≠ ⊥ → ¬ SphericalCusp D.cusp →
    localJoint n D.chi (pairCharacter D hecke hhecke) .plane false ≠ ⊥ →
    ∀ halfWeight : ℤ, 2 * halfWeight = -((n : ℤ) + 3) →
      ∀ v ∈ levelThreeClassicalVectors D.cusp halfWeight, v = 0

/-- **The prime-three input at the identity plane, consumer form**, from the two inputs. -/
theorem sphericalForcedByLocal_of_inputs {n : ℕ} (hbridge : LevelThreeBridge)
    (hmatch : LevelThreeMatching n) (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 0 < n) (hne : associatePair D ≠ ⊥) : SphericalForcedByLocal D hecke hhecke := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact sphericalForcedByLocal_of_even D hχ hecke hhecke hn heven
  intro hloc
  by_contra hns
  obtain ⟨halfWeight, hw, v, hv, hv0⟩ :=
    hbridge D.cusp n hodd D.cohomological (exists_levelThree_of_not_spherical D hne hns)
  exact hv0 (hmatch D hecke hhecke hχ hne hns hloc halfWeight hw v hv)

/-- The matching input at the good line in degree `n`. -/
def LevelThreeMatchingLine (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), D.chi = trivialCharacter →
    associatePair D ≠ ⊥ → ¬ SphericalCusp D.cusp →
    localJoint n D.chi (pairCharacter D hecke hhecke) .line true ≠ ⊥ →
    ∀ halfWeight : ℤ, 2 * halfWeight = -((n : ℤ) + 3) →
      ∀ v ∈ levelThreeClassicalVectors D.cusp halfWeight, v = 0

/-- **The prime-three input at the good line, consumer form**, from the two inputs. -/
theorem sphericalForcedByLocalLine_of_inputs {n : ℕ} (hbridge : LevelThreeBridge)
    (hmatch : LevelThreeMatchingLine n) (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (hne : associatePair D ≠ ⊥) : SphericalForcedByLocalLine D hecke hhecke := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact sphericalForcedByLocalLine_of_even D hχ hecke hhecke hn heven hne
  intro hloc
  by_contra hns
  obtain ⟨halfWeight, hw, v, hv, hv0⟩ :=
    hbridge D.cusp n hodd D.cohomological (exists_levelThree_of_not_spherical D hne hns)
  exact hv0 (hmatch D hecke hhecke hχ hne hns hloc halfWeight hw v hv)

end TernaryPeriodPolynomials.MultiplicityOne
