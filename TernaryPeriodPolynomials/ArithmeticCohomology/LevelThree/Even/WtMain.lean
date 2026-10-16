module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart6
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Vectors

@[expose] public section


/-!
# Level-three weight vectors in every cohomological degree

Formalized by Claude Sonnet 5.5 (AxiomCode).

Weight-generic twin of `MultiplicityOne.cohomological_holomorphic_or_regularity_obstruction`
and `cohomological_exists_levelThree_holomorphic`.  The rotation weight is an integer `wt` with
`wt = -(degree + 3)`, so that no parity of the cohomological degree is needed (an even degree gives
an odd rotation weight).  The weight-free obstruction theorems of `BridgePart6` are reused unchanged
and the three kernel branches are closed with the `Wt` twins of `WtSmooth`.

* `cohomological_holomorphic_or_regularity_obstructionWt` — the holomorphic level-three vector of
  weight `wt`, or the regularity obstruction;
* `cohomological_exists_levelThree_holomorphicWt` — the obstruction is impossible;
* `exists_levelThreeWeightVector_of_levelVectorWt`,
  `levelThreeWeightVectors_ne_bot_of_levelVectorWt` — a nonzero level-three vector of a cohomological
  cuspidal representation of degree `n` produces a nonzero level-three vector of rotation weight
  `-(n + 3)`, for every `n`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.MultiplicityOne
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors mem_levelThreeWeightVectors)

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem cohomological_holomorphic_or_regularity_obstructionWt (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (wt : ℤ) (hwt : wt = -((degree : ℤ) + 3))
    (cohomological : Cohomological cusp degree) :
    (∃ vector : cusp.smooth, vector ≠ 0 ∧ vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ wt • vector.val) ∧
      cuspRaisingVector cusp wt vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
        UpperHalfPlane.upperHalfPlaneSet) ∨
    ∃ (level : Subgroup BinaryFiniteGL) (vector : cusp.H),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      vector ∈ cuspHilbertWeightValues cusp level (degree + 1 : ℕ) ∧
      DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet ∧
      vector ∉ cuspAffineSmoothValues cusp ∧
      cuspRaisingVector cusp (degree + 1 : ℕ) vector ∈ cuspAffineSmoothValues cusp := by
  obtain ⟨level, level_open, level_compact, alternatives⟩ :=
    cohomological_extremal_or_analytic_obstruction cusp spherical cohomological
  have central_positive := cohomological_centralCharacter_positive cusp cohomological
  have negative_eq : -2 - ((degree + 1 : ℕ) : ℤ) = wt := by omega
  have weight_eq : ((degree + 1 : ℕ) : ℤ) + 2 = -wt := by omega
  rcases alternatives
    with ⟨vector, nonzero, member, killed⟩ | ⟨vector, nonzero, member, annihilates⟩ |
    ⟨vector, member, differentiable, not_smooth, raised_smooth⟩
  · left
    have value_nonzero : vector.val ≠ 0 := fun equality => nonzero (Subtype.ext equality)
    have rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ wt • vector.val := by
      simpa only [negative_eq] using member.2
    have raising_zero : cuspRaisingVector cusp wt vector.val = 0 := by
      have equality := congrArg Subtype.val killed
      change cuspRaisingVector cusp (-2 - (degree + 1 : ℕ)) vector.val = 0 at equality
      simpa only [negative_eq] using equality
    exact cusp_exists_levelThree_smooth_raising_zeroWt cusp spherical central_positive vector.val
      wt value_nonzero rotation vector.property raising_zero
  · left
    obtain ⟨result, result_nonzero, fixed, rotation, killed, holomorphic⟩ :=
      cuspWeightWeakLoweringKernel_exists_levelThreeWt cusp spherical central_positive level
        level_open level_compact (degree + 1 : ℕ) (-wt) weight_eq vector nonzero member
        annihilates
    simp only [neg_neg] at rotation killed holomorphic
    exact ⟨result, result_nonzero, fixed, rotation, killed, holomorphic⟩
  · exact Or.inr ⟨level, vector, level_open, level_compact, member, differentiable, not_smooth,
      raised_smooth⟩

/-- The actual nonzero cohomology class supplies an exact level-three vector of rotation weight
`wt = -(degree + 3)` with holomorphic weighted orbit, for every degree. -/
theorem cohomological_exists_levelThree_holomorphicWt (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (wt : ℤ) (hwt : wt = -((degree : ℤ) + 3))
    (cohomological : Cohomological cusp degree) :
    ∃ vector : cusp.smooth, vector ≠ 0 ∧ vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ wt • vector.val) ∧
      cuspRaisingVector cusp wt vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  rcases cohomological_holomorphic_or_regularity_obstructionWt cusp spherical wt hwt cohomological
    with result | obstruction
  · exact result
  · obtain ⟨_, vector, _, _, _, differentiable, not_smooth, raised_smooth⟩ := obstruction
    exact False.elim (not_smooth (cuspAffineOrbitVector_contDiffOn_of_raising_smoothWt cusp
      ((degree + 1 : ℕ) : ℤ) vector differentiable raised_smooth))

/-- **A level-three vector gives a nonzero level-three vector of weight `-(n + 3)`**, for every
degree `n`. -/
theorem exists_levelThreeWeightVector_of_levelVectorWt {n : ℕ} (D : InducingData n)
    (h : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp) :
    ∃ w : D.cusp.smooth, w ≠ 0 ∧ w ∈ levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) := by
  obtain ⟨vector, nonzero, fixed, rotation, _, _⟩ :=
    cohomological_exists_levelThree_holomorphicWt D.cusp h (degree := n) (-((n : ℤ) + 3)) rfl
      D.cohomological
  exact ⟨vector, nonzero, mem_levelThreeWeightVectors.mpr ⟨fixed, rotation⟩⟩

/-- The level-three weight vectors of weight `-(n + 3)` are nonzero when `D.cusp` has a nonzero
level-three vector, for every degree `n`. -/
theorem levelThreeWeightVectors_ne_bot_of_levelVectorWt {n : ℕ} (D : InducingData n)
    (h : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp) :
    levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) ≠ ⊥ := by
  obtain ⟨w, hw0, hw⟩ := exists_levelThreeWeightVector_of_levelVectorWt D h
  exact (Submodule.ne_bot_iff _).mpr ⟨w, hw, hw0⟩

end TernaryPeriodPolynomials.EvenLevelThree
