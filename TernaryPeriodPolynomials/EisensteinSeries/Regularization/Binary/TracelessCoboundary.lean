module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CasimirCoboundary

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCoefficientDerivedOperator_smul (degree : ℕ) (scalar : ℝ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCoefficientDerivedOperator degree (scalar • direction) = scalar • binaryCoefficientDerivedOperator degree direction := by
  rw [← IsScalarTower.algebraMap_smul ℂ scalar (binaryCoefficientDerivedOperator degree direction)]
  change binaryCoefficientDerivedOperator degree (scalar • direction) =
    (scalar : ℂ) • binaryCoefficientDerivedOperator degree direction
  simp only [binaryCoefficientDerivedOperator, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [smul_neg (scalar : ℂ) (∑ row : Fin 2, ∑ column : Fin 2,
    (direction row column : ℂ) • binaryCoefficientEntry degree row column)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro column _
  exact mul_smul (scalar : ℂ) (direction row column : ℂ) _

noncomputable def binaryCohomologicalDerivedLinear (cusp : CuspidalRepresentation) (degree : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) where
  toFun := binaryCohomologicalDerivedOperator cusp degree
  map_add' first second := by
    simp only [binaryCohomologicalDerivedOperator_eq_sum, map_add, binaryCoefficientDerivedOperator_add]
    abel
  map_smul' scalar direction := by
    simp only [binaryCohomologicalDerivedOperator_eq_sum, map_smul,
      binaryCoefficientDerivedOperator_smul, AlgHom.map_smul_of_tower, RingHom.id_apply, smul_add]

theorem binary_traceless_decomposition (direction : Matrix (Fin 2) (Fin 2) ℝ)
    (traceless : Matrix.trace direction = 0) :
    direction = direction 0 0 • binarySplitDirection +
      ((direction 0 1 + direction 1 0) / 2) • binarySymmetricDirection +
      ((direction 0 1 - direction 1 0) / 2) • binaryRotationDirection := by
  have trace : direction 0 0 + direction 1 1 = 0 := by
    simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using traceless
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binarySplitDirection, binarySymmetricDirection, binaryRotationDirection, Matrix.smul_apply] <;> linarith

theorem binary_lie_cocycle_coboundary_traceless_of_distinct_casimir
    (cusp : CuspidalRepresentation) (degree : ℕ) (scalar : ℂ)
    (casimir : cuspCasimirOperator cusp = scalar • 1)
    (distinct : scalar ≠ ((degree : ℂ) + 1) * ((degree : ℂ) + 3))
    (cocycle : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (lie_identity : ∀ first second, Matrix.trace first = 0 → Matrix.trace second = 0 →
      cocycle (first * second - second * first) =
        binaryCohomologicalDerivedOperator cusp degree first (cocycle second) -
          binaryCohomologicalDerivedOperator cusp degree second (cocycle first)) :
    ∃ vector : BinaryDegreeMonomial (degree + 1) → cusp.smooth, ∀ direction,
      Matrix.trace direction = 0 → binaryCohomologicalDerivedOperator cusp degree direction vector = cocycle direction := by
  obtain ⟨vector, rotation, split, symmetric⟩ :=
    binary_lie_cocycle_coboundary_of_distinct_casimir cusp degree scalar casimir distinct cocycle lie_identity
  refine ⟨vector, ?_⟩
  intro direction traceless
  change binaryCohomologicalDerivedLinear cusp degree direction vector = cocycle direction
  rw [binary_traceless_decomposition direction traceless]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [show binaryCohomologicalDerivedLinear cusp degree binarySplitDirection vector = _ from split,
    show binaryCohomologicalDerivedLinear cusp degree binarySymmetricDirection vector = _ from symmetric,
    show binaryCohomologicalDerivedLinear cusp degree binaryRotationDirection vector = _ from rotation]

theorem binary_invariant_zero_of_distinct_casimir
    (cusp : CuspidalRepresentation) (degree : ℕ) (scalar : ℂ)
    (casimir : cuspCasimirOperator cusp = scalar • 1)
    (distinct : scalar ≠ ((degree : ℂ) + 1) * ((degree : ℂ) + 3))
    (vector : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (rotation : binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection vector = 0)
    (split : binaryCohomologicalDerivedOperator cusp degree binarySplitDirection vector = 0)
    (symmetric : binaryCohomologicalDerivedOperator cusp degree binarySymmetricDirection vector = 0) : vector = 0 := by
  have applied := congrArg (fun operator => operator vector)
    (binaryCohomological_difference_casimir_scalar cusp degree scalar casimir)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Module.End.one_apply, rotation, split, symmetric, map_zero, add_zero, sub_zero] at applied
  exact (smul_eq_zero.mp applied.symm).resolve_left (sub_ne_zero.mpr distinct)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
