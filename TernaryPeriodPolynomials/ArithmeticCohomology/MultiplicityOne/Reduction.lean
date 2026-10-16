module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness

@[expose] public section


/-!
# The prime-three input at the level-one cusps: what is provable and what is not

`SphericalForcedByLocal D hecke hhecke` (identity plane) and `SphericalForcedByLocalLine D hecke
hhecke` (good line) say that a nonzero local joint generalized eigenspace of the pair character
forces `D.cusp` to have a `GL₂(ℤ̂)`-fixed vector.

* **The pair character is unconstrained on a zero pair.** `pairCharacter` is the choice of a scalar
  by which the away-three Hecke operators act on `associatePair D`. When `associatePair D = ⊥`
  every complex number is such a scalar (`pairScalar_of_associatePair_eq_bot`), and
  `pairCharacter` is the `Classical.choose` of an existential with the witness `0`
  (`pairCharacter_eq_choose_of_eq_bot`). The two bridge statements are therefore only meaningful
  for a nonzero pair; this is how their consumers use them (`eigenSeparated_of_eq_bot` handles the
  zero pair).
* **Unconditional discharges.** Each statement holds as soon as some summand class has a nonzero
  coordinate at the cusp, in particular under the local witness; and for the trivial
  character and even `n` (at the good line: `3 ≤ n` and a nonzero pair), where the local joint
  eigenspace is zero.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.MultiplicityOne

variable {n : ℕ}

/-! ## The pair character on a zero pair -/

/-- On a zero pair every complex number is an eigenvalue of every pair Hecke operator. -/
theorem pairScalar_of_associatePair_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hbot : associatePair D = ⊥) (t : HeckeCorrespondence) (c : ℂ) :
    ∀ y ∈ associatePair D, pairHecke D hecke t y = c • y := by
  intro y hy
  rw [hbot, Submodule.mem_bot] at hy
  subst hy
  simp

/-- On a zero pair the pair character at an away-three correspondence is the choice of a scalar
from an existential that every complex number witnesses. -/
theorem pairCharacter_eq_choose_of_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hbot : associatePair D = ⊥)
    (t : HeckeCorrespondence) (ht : AwayThree t) :
    pairCharacter D hecke hhecke t =
      Classical.choose (⟨0, pairScalar_of_associatePair_eq_bot D hecke hbot t 0⟩ :
        ∃ c : ℂ, ∀ y ∈ associatePair D, pairHecke D hecke t y = c • y) := by
  have h : pairCharacter D hecke hhecke t =
      (HeckeEigen.Satake.pair_scalar D hecke hhecke t ht).choose := by
    classical
    unfold pairCharacter
    exact dite_eq_left ht
  exact h

/-! ## Discharge from a nonzero coordinate -/

theorem coordinateImage_ne_bot_of_mem (D : InducingData n) (side : Side) (good : Bool)
    {a : StratumH2 n D.chi side} (ha : a ∈ boundarySummand D side)
    (h0 : cuspRes n D.chi side good a ≠ 0) : coordinateImage D side good ≠ ⊥ := by
  intro hbot
  apply h0
  have hmem : cuspRes n D.chi side good a ∈ coordinateImage D side good := ⟨a, ha, rfl⟩
  rwa [hbot, Submodule.mem_bot] at hmem

theorem sphericalForcedByLocal_of_coordinateImage_ne_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : coordinateImage D .plane false ≠ ⊥) : SphericalForcedByLocal D hecke hhecke :=
  fun _ => sphericalCusp_of_coordinateImage_ne_bot D h

theorem sphericalForcedByLocalLine_of_coordinateImage_ne_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : coordinateImage D .line true ≠ ⊥) : SphericalForcedByLocalLine D hecke hhecke :=
  fun _ => sphericalCusp_of_coordinateImage_line_ne_bot D h

/-- The local witness at the identity plane gives the prime-three input there. -/
theorem sphericalForcedByLocal_of_localWitness (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hw : LocalInterface.LocalWitness D hecke hhecke .plane false) :
    SphericalForcedByLocal D hecke hhecke := by
  intro hne
  obtain ⟨a, ha, h0, -⟩ := hw hne
  exact sphericalCusp_of_coordinateImage_ne_bot D
    (coordinateImage_ne_bot_of_mem D .plane false ha h0)

/-- The local witness at the good line gives the prime-three input there. -/
theorem sphericalForcedByLocalLine_of_localWitness (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hw : LocalInterface.LocalWitness D hecke hhecke .line true) :
    SphericalForcedByLocalLine D hecke hhecke := by
  intro hne
  obtain ⟨a, ha, h0, -⟩ := hw hne
  exact sphericalCusp_of_coordinateImage_line_ne_bot D
    (coordinateImage_ne_bot_of_mem D .line true ha h0)

/-! ## Even degree, trivial character: the local joint eigenspaces vanish -/

theorem sphericalForcedByLocal_of_even (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 0 < n) (heven : Even n) : SphericalForcedByLocal D hecke hhecke := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  intro hne
  exact absurd (IdentityPlaneEven.localJoint_identityPlane_eq_bot n hn heven _) hne

theorem sphericalForcedByLocalLine_of_even (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (heven : Even n) (hne : associatePair D ≠ ⊥) :
    SphericalForcedByLocalLine D hecke hhecke := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  intro hloc
  exact absurd (LocalUniqueness.localJoint_goodLine_eq_bot_of_even _ (by omega) heven
    (LocalUniqueness.pairCharacter_two_sub_one_norm_le (⟨cusp, coh⟩ : CohomologicalCuspData n)
      hecke hhecke hn hne)) hloc

end TernaryPeriodPolynomials.MultiplicityOne
