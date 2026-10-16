module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.SideEquivalence

@[expose] public section


/-!
# Separation is a dimension inequality

The associate pair always lies in the joint generalized eigenspace of its own away-three
eigencharacter (`pair_scalar`). Hence eigencharacter separation, the single input of the three
projector/recovery targets, is equivalent to the inequality
`finrank (jointGenEigenspace D hecke c) ≤ finrank (associatePair D)`
for the eigencharacter `c` of a nonzero vector of the pair. This splits the direction into an
upper bound for the generalized eigenspace (Eichler–Shimura type) and a lower bound for the associate
pair (construction of source classes).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Spectral

open TernaryPeriodPolynomials.SpectralSeparation

variable {n : ℕ}

/-- The away-three eigencharacter of the associate pair (zero off `AwayThree`). -/
def pairCharacter (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) : ℂ := by
  classical
  exact if ht : AwayThree t then (HeckeEigen.Satake.pair_scalar D hecke hhecke t ht).choose else 0

theorem pairCharacter_spec (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (y : BoundaryCoordinates n D.chi) (hy : y ∈ associatePair D) :
    pairHecke D hecke t y = pairCharacter D hecke hhecke t • y := by
  classical
  rw [pairCharacter, dite_eq_left ht]
  exact (HeckeEigen.Satake.pair_scalar D hecke hhecke t ht).choose_spec y hy

/-- **Dimension criterion.** Separation follows from (and, by
`eigenSeparated_iff_eq_jointGenEigenspace`, is equivalent to) the bound
`dim jointGenEigenspace(pairCharacter) ≤ dim associatePair`. -/
theorem eigenSeparated_of_finrank_le (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (bound : Module.finrank ℂ (jointGenEigenspace D hecke (pairCharacter D hecke hhecke)) ≤
      Module.finrank ℂ (associatePair D)) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  classical
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n D.chi
  by_cases hbot : associatePair D = ⊥
  · exact eigenSeparated_of_eq_bot D hecke hbot
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hca : ∀ t, AwayThree t → pairHecke D hecke t a = pairCharacter D hecke hhecke t • a :=
    fun t ht => pairCharacter_spec D hecke hhecke t ht a ha
  have hiff := eigenSeparated_iff_eq_jointGenEigenspace D hecke hhecke
    (pairCharacter D hecke hhecke) a ha ha0 hca
  have hle : associatePair D ≤ jointGenEigenspace D hecke (pairCharacter D hecke hhecke) := by
    intro y hy
    simp only [jointGenEigenspace, Submodule.mem_iInf, Subtype.forall]
    intro t ht
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    exact pairCharacter_spec D hecke hhecke t ht y hy
  exact hiff.mpr (Submodule.eq_of_le_of_finrank_le hle bound)

/-- Conversely, separation forces the dimension bound. -/
theorem finrank_le_of_eigenSeparated (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D))
    (hne : associatePair D ≠ ⊥) :
    Module.finrank ℂ (jointGenEigenspace D hecke (pairCharacter D hecke hhecke)) ≤
      Module.finrank ℂ (associatePair D) := by
  classical
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n D.chi
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hca : ∀ t, AwayThree t → pairHecke D hecke t a = pairCharacter D hecke hhecke t • a :=
    fun t ht => pairCharacter_spec D hecke hhecke t ht a ha
  have heq := (eigenSeparated_iff_eq_jointGenEigenspace D hecke hhecke
    (pairCharacter D hecke hhecke) a ha ha0 hca).mp hsep
  rw [← heq]


/-- **Good/bad split of the direction.** Separation follows from two statements about the
joint generalized eigenspace `J` of the pair character:
* (good part) modulo classes vanishing at the good cusps, every `w ∈ J` is a source class;
* (bad part) every `w ∈ J` vanishing at the good cusps is a source class.
The good-vanishing subspace is stable under the away-three algebra
(`AwayThreeHeckeGoodCusps.away_three_hecke_good_cusps`), so the first statement concerns the
level-one Levi data of the good cusps and the second the level-three data of the bad cusps. -/
theorem eigenSeparated_of_good_bad (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (good : ∀ w ∈ jointGenEigenspace D hecke (pairCharacter D hecke hhecke),
      ∃ a ∈ associatePair D, w - a ∈ goodBoundarySubmodule n D.chi)
    (bad : jointGenEigenspace D hecke (pairCharacter D hecke hhecke) ⊓
      goodBoundarySubmodule n D.chi ≤ associatePair D) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n D.chi
  apply eigenSeparated_of_finrank_le D hecke hhecke
  have hle : associatePair D ≤ jointGenEigenspace D hecke (pairCharacter D hecke hhecke) := by
    intro y hy
    simp only [jointGenEigenspace, Submodule.mem_iInf, Subtype.forall]
    intro t ht
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    exact pairCharacter_spec D hecke hhecke t ht y hy
  have hge : jointGenEigenspace D hecke (pairCharacter D hecke hhecke) ≤ associatePair D := by
    intro w hw
    obtain ⟨a, ha, hwa⟩ := good w hw
    have hdiff : w - a ∈ jointGenEigenspace D hecke (pairCharacter D hecke hhecke) :=
      Submodule.sub_mem _ hw (hle ha)
    have hmem := bad ⟨hdiff, hwa⟩
    have : w = (w - a) + a := by abel
    rw [this]
    exact Submodule.add_mem _ hmem ha
  exact Submodule.finrank_mono hge

end TernaryPeriodPolynomials.Spectral
