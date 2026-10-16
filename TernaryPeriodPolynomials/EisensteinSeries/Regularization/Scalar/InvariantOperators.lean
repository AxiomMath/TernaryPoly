module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.DerivedRealization
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.LowestWeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryScalarDerivative (direction : Matrix (Fin 2) (Fin 2) ℝ)
    (function : BinaryAdelicGL → ℂ) (argument : BinaryAdelicGL) : ℂ :=
  fderiv ℝ (fun matrix => function (argument * atInfinity (invertibleMatrix matrix))) 1 direction

theorem binaryScalarDerivative_realize (cusp : CuspidalRepresentation)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0)
    (vector : cusp.smooth) :
    binaryScalarDerivative direction (cusp.realize vector) =
      cusp.realize (cuspDerivedAction cusp direction vector) := by
  funext argument
  exact cuspScalarMatrixOrbit_fderiv_traceless cusp vector argument direction traceless

theorem binaryScalarDerivative_rotation_realize (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) :
    binaryScalarDerivative binaryRotationDirection (cusp.realize vector) =
      cusp.realize (cuspRotationOperator cusp vector) :=
  binaryScalarDerivative_realize cusp _ binary_rankOne_directions_traceless.1 vector

theorem binaryScalarDerivative_split_realize (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) :
    binaryScalarDerivative binarySplitDirection (cusp.realize vector) =
      cusp.realize (cuspSplitOperator cusp vector) :=
  binaryScalarDerivative_realize cusp _ binary_rankOne_directions_traceless.2.1 vector

theorem binaryScalarDerivative_symmetric_realize (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) :
    binaryScalarDerivative binarySymmetricDirection (cusp.realize vector) =
      cusp.realize (cuspSymmetricOperator cusp vector) :=
  binaryScalarDerivative_realize cusp _ binary_rankOne_directions_traceless.2.2 vector

noncomputable def binaryScalarRaising (function : BinaryAdelicGL → ℂ) : BinaryAdelicGL → ℂ :=
  binaryScalarDerivative binarySplitDirection function +
    Complex.I • binaryScalarDerivative binarySymmetricDirection function

noncomputable def binaryScalarLowering (function : BinaryAdelicGL → ℂ) : BinaryAdelicGL → ℂ :=
  binaryScalarDerivative binarySplitDirection function -
    Complex.I • binaryScalarDerivative binarySymmetricDirection function

noncomputable def binaryScalarCasimir (function : BinaryAdelicGL → ℂ) : BinaryAdelicGL → ℂ :=
  binaryScalarDerivative binarySplitDirection (binaryScalarDerivative binarySplitDirection function) +
    binaryScalarDerivative binarySymmetricDirection (binaryScalarDerivative binarySymmetricDirection function) -
      binaryScalarDerivative binaryRotationDirection (binaryScalarDerivative binaryRotationDirection function)

theorem binaryScalarRaising_realize (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    binaryScalarRaising (cusp.realize vector) = cusp.realize (cuspRaisingOperator cusp vector) := by
  simp only [binaryScalarRaising, binaryScalarDerivative_split_realize,
    binaryScalarDerivative_symmetric_realize, cuspRaisingOperator, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul]

theorem binaryScalarLowering_realize (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    binaryScalarLowering (cusp.realize vector) = cusp.realize (cuspLoweringOperator cusp vector) := by
  simp only [binaryScalarLowering, binaryScalarDerivative_split_realize,
    binaryScalarDerivative_symmetric_realize, cuspLoweringOperator, LinearMap.sub_apply,
    LinearMap.smul_apply, map_sub, map_smul]

theorem binaryScalarCasimir_realize (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    binaryScalarCasimir (cusp.realize vector) = cusp.realize (cuspCasimirOperator cusp vector) := by
  simp only [binaryScalarCasimir, binaryScalarDerivative_split_realize,
    binaryScalarDerivative_symmetric_realize, binaryScalarDerivative_rotation_realize,
    cuspCasimirOperator, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    map_add, map_sub]

theorem cohomological_scalar_casimir {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (vector : cusp.smooth) :
    binaryScalarCasimir (cusp.realize vector) =
      (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • cusp.realize vector := by
  rw [binaryScalarCasimir_realize, cohomological_casimir_value cohomological,
    LinearMap.smul_apply, Module.End.one_apply, map_smul]

theorem cohomological_scalar_lowest_weight {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ function ∈ cuspFunctions cusp, function ≠ 0 ∧
      binaryScalarDerivative binaryRotationDirection function =
        (Complex.I * ((degree : ℂ) + 3)) • function ∧
      binaryScalarLowering function = 0 := by
  obtain ⟨vector, nonzero, rotation, lowering⟩ := cohomological_lowest_weight_vector cohomological
  refine ⟨cusp.realize vector, ⟨vector, rfl⟩, ?_, ?_, ?_⟩
  · simpa only [map_zero] using cusp.injective.ne_iff.mpr nonzero
  · rw [binaryScalarDerivative_rotation_realize, rotation, map_smul]
  · rw [binaryScalarLowering_realize, lowering, map_zero]

theorem cohomological_scalar_highest_weight {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ function ∈ cuspFunctions cusp, function ≠ 0 ∧
      binaryScalarDerivative binaryRotationDirection function =
        (-Complex.I * ((degree : ℂ) + 3)) • function ∧
      binaryScalarRaising function = 0 := by
  obtain ⟨vector, nonzero, rotation, raising⟩ := cohomological_highest_weight_vector cohomological
  refine ⟨cusp.realize vector, ⟨vector, rfl⟩, ?_, ?_, ?_⟩
  · simpa only [map_zero] using cusp.injective.ne_iff.mpr nonzero
  · rw [binaryScalarDerivative_rotation_realize, rotation, map_smul]
  · rw [binaryScalarRaising_realize, raising, map_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
