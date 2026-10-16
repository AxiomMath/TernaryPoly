module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CocycleRightDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_group_cocycle_coboundary_of_distinct_casimir
    (cusp : CuspidalRepresentation) (degree : ℕ) (scalar : ℂ)
    (casimir : cuspCasimirOperator cusp = scalar • 1)
    (distinct : scalar ≠ ((degree : ℂ) + 1) * ((degree : ℂ) + 3))
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second)) :
    ∃ vector, ∀ matrix, cocycle matrix = binaryCohomologicalRepresentation cusp degree matrix vector - vector := by
  obtain ⟨vector, infinitesimal_exact⟩ :=
    binary_lie_cocycle_coboundary_traceless_of_distinct_casimir cusp degree scalar casimir distinct
      (binaryCocycleInfinitesimal cusp degree cocycle smooth finite)
      (binaryCocycleInfinitesimal_lie_identity cusp degree cocycle smooth finite identity)
  refine ⟨vector, ?_⟩
  intro matrix
  have invariant (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0) :
      binaryCohomologicalDerivedOperator cusp degree direction
        (cocycle matrix - (binaryCohomologicalRepresentation cusp degree matrix vector - vector)) = 0 := by
    have conjugate_traceless : Matrix.trace (matrix.inv * direction * matrix.val) = 0 := by
      rw [binary_conjugate_trace, traceless]
    have relation := binaryCocycleInfinitesimal_group_relation cusp degree cocycle smooth finite identity matrix direction traceless
    rw [← infinitesimal_exact direction traceless,
      ← infinitesimal_exact (matrix.inv * direction * matrix.val) conjugate_traceless,
      ← binaryCohomologicalDerivedOperator_covariance cusp degree matrix direction traceless vector] at relation
    simp only [map_sub]
    calc
      _ = binaryCohomologicalDerivedOperator cusp degree direction vector +
          binaryCohomologicalDerivedOperator cusp degree direction (cocycle matrix) -
          binaryCohomologicalDerivedOperator cusp degree direction
            (binaryCohomologicalRepresentation cusp degree matrix vector) := by abel
      _ = 0 := by rw [relation, sub_self]
  apply sub_eq_zero.mp
  exact binary_invariant_zero_of_distinct_casimir cusp degree scalar casimir distinct _
    (invariant binaryRotationDirection binary_rankOne_directions_traceless.1)
    (invariant binarySplitDirection binary_rankOne_directions_traceless.2.1)
    (invariant binarySymmetricDirection binary_rankOne_directions_traceless.2.2)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
