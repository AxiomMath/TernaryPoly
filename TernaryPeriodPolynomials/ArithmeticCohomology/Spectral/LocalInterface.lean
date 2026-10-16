module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspLift

@[expose] public section


/-!
# The local statements at one cusp

Eigencharacter separation of a nonzero associate pair is equivalent to four local statements, one
per cusp (`CuspReduction.eigenSeparated_of_cusps`, `CuspLift.cusps_of_eigenSeparated`): every
class of the local joint generalized eigenspace of the pair character is the Shapiro coordinate of
a class of the cuspidal summand of that side, vanishing at the other cusp of the side.

A local statement splits into two independent halves:
* **uniqueness**: the local joint generalized eigenspace has dimension at most one;
* **witness**: if it is nonzero, some class of the cuspidal summand has nonzero coordinate at the
  cusp and vanishes at the other cusp of the side.
Every coordinate of a class of the summand lies in the local joint generalized eigenspace, so the
two halves give the local statement. When the associate pair is zero, separation is automatic, so
the local statements are only needed for a nonzero pair (for which the pair character is the actual
eigencharacter).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation

namespace TernaryPeriodPolynomials.Spectral.LocalInterface

open CuspOrbits CuspReduction CuspLift

variable {n : ℕ}

/-- The local statement at the cusp `(side, good)`. -/
def LocalStatement (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  ∀ y ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good,
    ∃ a ∈ boundarySummand D side,
      cuspRes n D.chi side good a = y ∧ cuspRes n D.chi side (!good) a = 0

/-- Local uniqueness: the local joint generalized eigenspace of the pair character has dimension at
most one. -/
def LocalUnique (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) ≤ 1

/-- Local witness: a nonzero local joint generalized eigenspace is seen by a class of the cuspidal
summand supported at the cusp. -/
def LocalWitness (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ →
    ∃ a ∈ boundarySummand D side,
      cuspRes n D.chi side good a ≠ 0 ∧ cuspRes n D.chi side (!good) a = 0

/-- **Separation from the local statements**, which are only needed for a nonzero pair. -/
theorem eigenSeparated_of_localStatements (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : associatePair D ≠ ⊥ → ∀ side good, LocalStatement D hecke hhecke side good) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  by_cases hbot : associatePair D = ⊥
  · exact eigenSeparated_of_eq_bot D hecke hbot
  · exact eigenSeparated_of_cusps D hecke hhecke (h hbot)

/-- The local cohomology at a cusp is finite-dimensional: it is a retract of the stratum. -/
theorem cuspH2_finiteDimensional (χ : RankOneCharacter) (side : Side) (good : Bool) :
    FiniteDimensional ℂ (CuspH2 n χ side good) := by
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n χ
  have hstratum : FiniteDimensional ℂ (StratumH2 n χ side) := by
    cases side
    · exact Module.Finite.of_injective (LinearMap.inl ℂ _ (StratumH2 n χ .line))
        LinearMap.inl_injective
    · exact Module.Finite.of_injective (LinearMap.inr ℂ (StratumH2 n χ .plane) _)
        LinearMap.inr_injective
  exact Module.Finite.of_injective (cuspLift n χ side good)
    (Function.LeftInverse.injective (cuspRes_cuspLift side good))

/-- The coordinate of a class of the cuspidal summand is a local eigenclass of the pair character. -/
theorem cuspRes_mem_localJoint_of_mem (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    {a : StratumH2 n D.chi side} (ha : a ∈ boundarySummand D side) :
    cuspRes n D.chi side good a ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good := by
  simp only [localJoint, Submodule.mem_iInf, Subtype.forall]
  intro t ht
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  have hpair : embedSide side a ∈ associatePair D := by
    cases side
    · exact ⟨ha, Submodule.zero_mem _⟩
    · exact ⟨Submodule.zero_mem _, ha⟩
  have heigen := pairCharacter_spec D hecke hhecke t ht _ hpair
  have hside : hecke side t a = pairCharacter D hecke hhecke t • a := by
    cases side
    · exact congrArg Prod.fst heigen
    · exact congrArg Prod.snd heigen
  rw [← cuspRes_hecke hecke hhecke t ht, hside, map_smul]

/-- **Uniqueness and a witness give the local statement.** -/
theorem localStatement_of_unique_witness (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hunique : LocalUnique D hecke hhecke side good)
    (hwitness : LocalWitness D hecke hhecke side good) :
    LocalStatement D hecke hhecke side good := by
  intro y hy
  by_cases hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥
  · refine ⟨0, Submodule.zero_mem _, ?_, map_zero _⟩
    rw [hbot, Submodule.mem_bot] at hy
    rw [hy, map_zero]
  obtain ⟨a, ha, hres, hother⟩ := hwitness hbot
  have := cuspH2_finiteDimensional (n := n) D.chi side good
  set K := localJoint n D.chi (pairCharacter D hecke hhecke) side good
  have hx : cuspRes n D.chi side good a ∈ K := cuspRes_mem_localJoint_of_mem D hecke hhecke side good ha
  have hne : (⟨_, hx⟩ : K) ≠ 0 := fun h => hres (congrArg Subtype.val h)
  have hrank : Module.finrank ℂ K = 1 :=
    le_antisymm hunique (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩)
  obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hrank ⟨y, hy⟩
  refine ⟨s • a, Submodule.smul_mem _ s ha, ?_, by rw [map_smul, hother, smul_zero]⟩
  rw [map_smul]
  exact congrArg Subtype.val hs

/-- If the local joint generalized eigenspace vanishes, the local statement holds. -/
theorem localStatement_of_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    LocalStatement D hecke hhecke side good := by
  intro y hy
  refine ⟨0, Submodule.zero_mem _, ?_, map_zero _⟩
  rw [hbot, Submodule.mem_bot] at hy
  rw [hy, map_zero]

end TernaryPeriodPolynomials.Spectral.LocalInterface
