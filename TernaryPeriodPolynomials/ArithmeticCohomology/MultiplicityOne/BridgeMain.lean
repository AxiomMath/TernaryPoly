module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart7

@[expose] public section


/-!
# Level-three classical vectors of a cohomological cuspidal representation

A cuspidal representation with a nonzero smooth vector fixed by the level
`{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` and a nonzero cohomology class in odd degree `n`
contains a nonzero level-three vector of rotation weight `-(n + 3)` whose scalar realization is
holomorphic (`levelThreeClassicalVectors`).  This is the level-three analogue of
`cohomological_exists_spherical_holomorphic` followed by `cuspClassicalVectors_mem_of_holomorphic`;
the chain was ported in `BridgeBasic` and `BridgePart1` to `BridgePart7`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Separation (PlaneLevelVector)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- A level-three rotation-weight vector with holomorphic scalar realization is a level-three
classical vector. -/
theorem levelThreeClassicalVectors_mem_of_holomorphic (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.smooth) (fixed : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector 1)
      UpperHalfPlane.upperHalfPlaneSet) : vector ∈ levelThreeClassicalVectors cusp halfWeight := by
  refine ⟨fixed, rotation, UpperHalfPlane.mdifferentiable_iff.mpr ?_⟩
  apply holomorphic.congr
  intro point positive
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
  rfl

/-- The level-three bridge: a cohomological cuspidal representation in odd degree `n` that has a
nonzero level-three vector contains a nonzero level-three classical vector of weight `n + 3`. -/
theorem cohomological_exists_levelThree_classical (cusp : CuspidalRepresentation)
    (level : ∃ v : cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues cusp) {degree : ℕ}
    (odd : Odd degree) (cohomological : Cohomological cusp degree) :
    ∃ halfWeight : ℤ, 2 * halfWeight = -((degree : ℤ) + 3) ∧
      ∃ v ∈ levelThreeClassicalVectors cusp halfWeight, v ≠ 0 := by
  obtain ⟨halfWeight, vector, weight, nonzero, fixed, rotation, _, holomorphic⟩ :=
    cohomological_exists_levelThree_holomorphic cusp level odd cohomological
  have scalar_holomorphic := cuspScalarWeightedRealization_holomorphic cusp halfWeight vector
    fixed rotation holomorphic 1
  exact ⟨halfWeight, weight, vector, levelThreeClassicalVectors_mem_of_holomorphic cusp halfWeight
    vector fixed rotation scalar_holomorphic, nonzero⟩

/-- The same, with the hypothesis phrased as `PlaneLevelVector cusp true`. -/
theorem cohomological_exists_levelThree_classical_of_planeLevelVector
    (cusp : CuspidalRepresentation) (level : PlaneLevelVector cusp true) {degree : ℕ}
    (odd : Odd degree) (cohomological : Cohomological cusp degree) :
    ∃ halfWeight : ℤ, 2 * halfWeight = -((degree : ℤ) + 3) ∧
      ∃ v ∈ levelThreeClassicalVectors cusp halfWeight, v ≠ 0 :=
  cohomological_exists_levelThree_classical cusp ((planeLevelVector_true_iff cusp).mp level) odd
    cohomological

end TernaryPeriodPolynomials.MultiplicityOne
