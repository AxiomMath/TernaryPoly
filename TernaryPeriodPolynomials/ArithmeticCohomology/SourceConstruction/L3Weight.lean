module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.BadLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Inputs
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelVector

@[expose] public section


/-!
# Level-three weight vectors from a level-three vector

For an inducing datum `D` of odd degree `n`, a nonzero smooth vector of `D.cusp` fixed by the
level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` produces a nonzero smooth level-three
vector of rotation weight `-(n + 3)` (`levelThreeWeightVectors D.cusp (sourceWeight n)`).

This is the level-three analogue of the extremal-weight step of the spherical theory: the
level-three port of that step (`MultiplicityOne.cohomological_exists_levelThree_classical`)
already yields a nonzero level-three vector of weight `-(n + 3)` with holomorphic scalar
realization, and a fortiori of that rotation weight.  The statements below restate it in terms of
`levelThreeWeightVectors` for each of the equivalent phrasings of the hypothesis: membership in
`levelThreeValues`, in SC's `badLevelSubspace`, `BadLineLevelVector`, `PlaneLevelVector _ true`,
and `SphericalCusp`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Separation
  (BadLineLevelVector PlaneLevelVector)
open TernaryPeriodPolynomials.MultiplicityOne
  (levelThreeValues cohomological_exists_levelThree_classical
    exists_levelThreeValues_of_badLineLevelVector planeLevelVector_true_iff)
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors sourceWeight levelThreeClassicalVectors_le_levelThreeWeightVectors
    levelThreeValues_eq_badLevelSubspace)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- **A level-three vector gives a nonzero level-three vector of weight `-(n + 3)`.** -/
theorem exists_levelThreeWeightVector_of_levelVector {n : ℕ} (hodd : Odd n) (D : InducingData n)
    (h : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp) :
    ∃ w : D.cusp.smooth, w ≠ 0 ∧ w ∈ levelThreeWeightVectors D.cusp (sourceWeight n) := by
  obtain ⟨halfWeight, hhalf, w, hw, hw0⟩ :=
    cohomological_exists_levelThree_classical D.cusp h hodd D.cohomological
  exact ⟨w, hw0,
    levelThreeClassicalVectors_le_levelThreeWeightVectors D.cusp halfWeight _ hhalf hw⟩

/-- **The level-three weight vectors are nonzero** when `D.cusp` has a nonzero level-three
vector (odd degree). -/
theorem levelThreeWeightVectors_ne_bot_of_levelVector {n : ℕ} (hodd : Odd n) (D : InducingData n)
    (h : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp) :
    levelThreeWeightVectors D.cusp (sourceWeight n) ≠ ⊥ := by
  obtain ⟨w, hw0, hw⟩ := exists_levelThreeWeightVector_of_levelVector hodd D h
  exact (Submodule.ne_bot_iff _).mpr ⟨w, hw, hw0⟩

/-- The same, from a nonzero vector of SC's `badLevelSubspace`. -/
theorem levelThreeWeightVectors_ne_bot_of_badLevelSubspace {n : ℕ} (hodd : Odd n)
    (D : InducingData n)
    (h : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ badLevelSubspace D.cusp) :
    levelThreeWeightVectors D.cusp (sourceWeight n) ≠ ⊥ := by
  obtain ⟨v, hv, hmem⟩ := h
  refine levelThreeWeightVectors_ne_bot_of_levelVector hodd D ⟨v, hv, ?_⟩
  rw [levelThreeValues_eq_badLevelSubspace]
  exact hmem

/-- The same, from `BadLineLevelVector D.cusp`. -/
theorem levelThreeWeightVectors_ne_bot_of_badLineLevelVector {n : ℕ} (hodd : Odd n)
    (D : InducingData n) (h : BadLineLevelVector D.cusp) :
    levelThreeWeightVectors D.cusp (sourceWeight n) ≠ ⊥ :=
  levelThreeWeightVectors_ne_bot_of_levelVector hodd D
    (exists_levelThreeValues_of_badLineLevelVector D.cusp h)

/-- The same, from `PlaneLevelVector D.cusp true`. -/
theorem levelThreeWeightVectors_ne_bot_of_planeLevelVector {n : ℕ} (hodd : Odd n)
    (D : InducingData n) (h : PlaneLevelVector D.cusp true) :
    levelThreeWeightVectors D.cusp (sourceWeight n) ≠ ⊥ :=
  levelThreeWeightVectors_ne_bot_of_levelVector hodd D ((planeLevelVector_true_iff D.cusp).mp h)

/-- The same, from a spherical vector. -/
theorem levelThreeWeightVectors_ne_bot_of_spherical {n : ℕ} (hodd : Odd n) (D : InducingData n)
    (h : SphericalCusp D.cusp) : levelThreeWeightVectors D.cusp (sourceWeight n) ≠ ⊥ := by
  obtain ⟨v, hv, hfix⟩ := h
  exact levelThreeWeightVectors_ne_bot_of_levelVector hodd D ⟨v, hv, fun k _ => hfix k⟩

end TernaryPeriodPolynomials.SourceConstruction
