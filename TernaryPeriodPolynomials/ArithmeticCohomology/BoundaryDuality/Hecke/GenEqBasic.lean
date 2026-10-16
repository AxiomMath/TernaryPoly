module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsJoint

@[expose] public section


/-!
# The prime eigenspace is the coordinate image, by dimension

At a cusp, the Shapiro coordinates of the summand classes lie in the local joint generalized
eigenspace `L` of all away-from-three operators, which lies in the joint generalized eigenspace `J`
of the prime operators `T_p`. If `J` has dimension at most `m` and `m` summand classes have linearly
independent coordinates, the sandwich `span ⊆ coordinate image ⊆ L ⊆ J` collapses.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq

open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-- The Shapiro coordinates of the summand classes lie in the joint generalized eigenspace of the
prime correspondences. -/
theorem coordinateImage_le_localJointGen (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) :
    coordinateImage D side good ≤
      localJointGen n D.chi (pairCharacter D hecke hhecke) side good := by
  rintro _ ⟨a, ha, rfl⟩
  exact localJoint_le_localJointGen n D.chi _ side good
    (cuspRes_mem_localJoint_of_mem D hecke hhecke side good ha)

/-- **The prime eigenspace is the coordinate image, by dimension.** If the joint generalized
eigenspace of the operators `T_p` has dimension at most `m` and `m` summand classes have linearly
independent coordinates at the cusp, then `J = L = coordinate image`. -/
theorem localJointGen_eq_coordinateImage_of_lowerBound (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) {m : ℕ}
    (h : LocalUpperBoundGen n D.chi (pairCharacter D hecke hhecke) side good m)
    (hglob : CoordinateLowerBound D side good m) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) side good =
        coordinateImage D side good ∧
      localJoint n D.chi (pairCharacter D hecke hhecke) side good =
        coordinateImage D side good := by
  obtain ⟨hfin, hdim⟩ := h
  obtain ⟨s, hs, hind⟩ := hglob
  have hspan : Submodule.span ℂ (Set.range s) ≤
      localJointGen n D.chi (pairCharacter D hecke hhecke) side good :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i =>
      coordinateImage_le_localJointGen D hecke hhecke side good (hs i))
  have hrank : Module.finrank ℂ (Submodule.span ℂ (Set.range s)) = m := by
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have heq : Submodule.span ℂ (Set.range s) =
      localJointGen n D.chi (pairCharacter D hecke hhecke) side good :=
    Submodule.eq_of_le_of_finrank_le hspan (by rw [hrank]; exact hdim)
  have hle : localJointGen n D.chi (pairCharacter D hecke hhecke) side good ≤
      coordinateImage D side good := by
    rw [← heq]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hs)
  have h1 : localJointGen n D.chi (pairCharacter D hecke hhecke) side good =
      coordinateImage D side good :=
    le_antisymm hle (coordinateImage_le_localJointGen D hecke hhecke side good)
  refine ⟨h1, le_antisymm ?_ ?_⟩
  · rw [← h1]
    exact localJoint_le_localJointGen n D.chi _ side good
  · rintro _ ⟨a, ha, rfl⟩
    exact cuspRes_mem_localJoint_of_mem D hecke hhecke side good ha

/-- **Multiplicity one version.** If the joint generalized eigenspace of the operators `T_p` has
dimension at most one and some summand class has nonzero coordinate at the cusp, then
`J = L = coordinate image`. -/
theorem localJointGen_eq_coordinateImage_of_ne_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool)
    (h : LocalUpperBoundGen n D.chi (pairCharacter D hecke hhecke) side good 1)
    (hne : coordinateImage D side good ≠ ⊥) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) side good =
        coordinateImage D side good ∧
      localJoint n D.chi (pairCharacter D hecke hhecke) side good =
        coordinateImage D side good := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact localJointGen_eq_coordinateImage_of_lowerBound D hecke hhecke side good h
    ⟨fun _ => x, fun _ => hx, linearIndependent_unique_iff.mpr hx0⟩

/-- From the two equalities with the coordinate image, the two joint eigenspaces agree. -/
theorem localJointGen_eq_localJoint_of_coordinate {D : InducingData n}
    {hecke : BoundaryHecke n D.chi} {hhecke : ActualBoundaryHecke n D.chi hecke}
    {side : Side} {good : Bool}
    (h : localJointGen n D.chi (pairCharacter D hecke hhecke) side good =
        coordinateImage D side good ∧
      localJoint n D.chi (pairCharacter D hecke hhecke) side good =
        coordinateImage D side good) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) side good =
      localJoint n D.chi (pairCharacter D hecke hhecke) side good :=
  h.1.trans h.2.symm

end TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq
