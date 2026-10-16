module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.Stabilizer

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitPartition

/- Rational rank-one matrix orbits and their stabilizer cosets. -/

abbrev RankOne := {matrix : Rectangular ℚ // matrix ≠ 0 ∧ ¬ FullRank matrix}

instance rankOne_countable : Countable RankOne := by
  let : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  exact inferInstance

theorem singular_right (matrix : Rectangular ℚ) (singular : ¬ FullRank matrix) (element : BinaryRationalGL) :
    ¬ FullRank (matrix * element.val) := by
  intro fullRank
  have inverse : element.val * element⁻¹.val = 1 := element.val_inv
  have result := FrameFlags.fullRank_right_mul ⟨matrix * element.val, fullRank⟩ element⁻¹
  apply singular
  simpa only [Matrix.mul_assoc, inverse, Matrix.mul_one] using result

def orbitSetoid : Setoid RankOne where
  r first second := ∃ element : BinaryRationalGL, second.val = first.val * element.val
  iseqv := ⟨fun _ => ⟨1, (Matrix.mul_one _).symm⟩,
    fun {first second} relation => by
      obtain ⟨element, equality⟩ := relation
      refine ⟨element⁻¹, ?_⟩
      have inverse : element.val * element⁻¹.val = 1 := element.val_inv
      rw [equality, Matrix.mul_assoc, inverse, Matrix.mul_one],
    fun {first second third} firstRelation secondRelation => by
      obtain ⟨firstElement, firstEq⟩ := firstRelation
      obtain ⟨secondElement, secondEq⟩ := secondRelation
      refine ⟨firstElement * secondElement, ?_⟩
      rw [secondEq, firstEq]
      exact Matrix.mul_assoc _ _ _⟩

abbrev Orbit := Quotient orbitSetoid

def orbitClass : RankOne → Orbit := Quotient.mk orbitSetoid

def member (orbit : Orbit) (coset : BinaryRationalGL ⧸ stabilizer orbit.out.val) : RankOne :=
  ⟨orbitMap orbit.out.val coset, orbitMap_nonzero orbit.out.val orbit.out.property.1 coset,
    singular_right orbit.out.val orbit.out.property.2 coset.out⁻¹⟩

theorem member_class (orbit : Orbit) (coset : BinaryRationalGL ⧸ stabilizer orbit.out.val) :
    orbitClass (member orbit coset) = orbit := by
  have relation : orbitSetoid orbit.out (member orbit coset) := ⟨coset.out⁻¹, rfl⟩
  have equality := Quotient.sound relation
  exact equality.symm.trans (Quotient.out_eq orbit)

theorem member_injective (orbit : Orbit) : Function.Injective (member orbit) := by
  intro first second equality
  exact orbitMap_injective orbit.out.val (congrArg Subtype.val equality)

theorem member_surjective (orbit : Orbit) (matrix : RankOne) (membership : orbitClass matrix = orbit) :
    ∃ coset : BinaryRationalGL ⧸ stabilizer orbit.out.val, member orbit coset = matrix := by
  have relation : orbitSetoid orbit.out matrix := Quotient.exact ((Quotient.out_eq orbit).trans membership.symm)
  obtain ⟨element, equality⟩ := relation
  refine ⟨QuotientGroup.mk element⁻¹, ?_⟩
  apply Subtype.ext
  change orbitMap orbit.out.val (QuotientGroup.mk element⁻¹) = matrix.val
  rw [orbitMap_mk, inv_inv, ← equality]

def fiberMap (orbit : Orbit) (coset : BinaryRationalGL ⧸ stabilizer orbit.out.val) :
    {matrix : RankOne // orbitClass matrix = orbit} := ⟨member orbit coset, member_class orbit coset⟩

def fiberEquiv (orbit : Orbit) :
    (BinaryRationalGL ⧸ stabilizer orbit.out.val) ≃ {matrix : RankOne // orbitClass matrix = orbit} :=
  Equiv.ofBijective (fiberMap orbit) ⟨by
    intro first second equality
    exact member_injective orbit (congrArg Subtype.val equality), by
    intro matrix
    obtain ⟨coset, equality⟩ := member_surjective orbit matrix.val matrix.property
    exact ⟨coset, Subtype.ext equality⟩⟩

theorem fiberEquiv_val (orbit : Orbit) (coset : BinaryRationalGL ⧸ stabilizer orbit.out.val) :
    (fiberEquiv orbit coset).val.val = orbitMap orbit.out.val coset := rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitPartition
