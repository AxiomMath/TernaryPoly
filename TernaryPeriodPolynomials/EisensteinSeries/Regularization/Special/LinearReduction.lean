module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.PositiveTriangularUnique
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def realSpecialOrthogonal : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  {matrix | (SpecialLinearGroup.toGL matrix).val.transpose *
    (SpecialLinearGroup.toGL matrix).val = 1}

theorem realSpecialOrthogonal_isCompact : IsCompact realSpecialOrthogonal :=
  SpecialLinearGroup.isClosedEmbedding_toGL.isCompact_preimage realOrthogonal_isCompact

theorem realSpecialOrthogonal_inv {matrix : SpecialLinearGroup (Fin 3) ℝ}
    (member : matrix ∈ realSpecialOrthogonal) : matrix⁻¹ ∈ realSpecialOrthogonal := by
  change (SpecialLinearGroup.toGL matrix⁻¹).val.transpose * (SpecialLinearGroup.toGL matrix⁻¹).val = 1
  rw [map_inv]
  exact real_orthogonal_inv member

theorem specialLinear_integral_real_reduction (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    ∃ integral : SpecialLinearGroup (Fin 3) ℤ, ∃ rotation : SpecialLinearGroup (Fin 3) ℝ,
      rotation ∈ realSpecialOrthogonal ∧
      realTriangularReduced (SpecialLinearGroup.toGL
        (SpecialLinearGroup.map (Int.castRingHom ℝ) integral * matrix * rotation)) ∧
      0 < (SpecialLinearGroup.toGL
        (SpecialLinearGroup.map (Int.castRingHom ℝ) integral * matrix * rotation)).val 0 0 := by
  obtain ⟨integral, rotation, integral_det, rotation_det, orthogonal, reduced, positive⟩ :=
    integral_real_positive_reduced_det_one (SpecialLinearGroup.toGL matrix)
      (Matrix.SpecialLinearGroup.det_coe matrix)
  let integralSL : SpecialLinearGroup (Fin 3) ℤ := ⟨integral.val, integral_det⟩
  let rotationSL : SpecialLinearGroup (Fin 3) ℝ := ⟨rotation.val, rotation_det⟩
  have rotation_coe : SpecialLinearGroup.toGL rotationSL = rotation := Units.ext rfl
  have integral_coe : SpecialLinearGroup.toGL
      (SpecialLinearGroup.map (Int.castRingHom ℝ) integralSL) = integralRealGroup integral := Units.ext rfl
  refine ⟨integralSL, rotationSL, ?_, ?_, ?_⟩
  · change (SpecialLinearGroup.toGL rotationSL).val.transpose * (SpecialLinearGroup.toGL rotationSL).val = 1
    rwa [rotation_coe]
  · simpa only [map_mul, integral_coe, rotation_coe] using reduced
  · simpa only [map_mul, integral_coe, rotation_coe] using positive

def realSpecialLinearReducedCover : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  {matrix | ∃ triangular rotation : SpecialLinearGroup (Fin 3) ℝ,
    realTriangularReduced (SpecialLinearGroup.toGL triangular) ∧
    0 < (SpecialLinearGroup.toGL triangular).val 0 0 ∧
    rotation ∈ realSpecialOrthogonal ∧ matrix = triangular * rotation}

theorem realSpecialLinearReducedCover_orbit (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    ∃ integral : integerSpecialLinearSubgroup,
      integral • matrix ∈ realSpecialLinearReducedCover := by
  obtain ⟨integral, rotation, orthogonal, reduced, positive⟩ :=
    specialLinear_integral_real_reduction matrix
  let integralReal := SpecialLinearGroup.map (Int.castRingHom ℝ) integral
  refine ⟨⟨integralReal, ⟨integral, rfl⟩⟩, integralReal * matrix * rotation, rotation⁻¹,
    reduced, positive, realSpecialOrthogonal_inv orthogonal, ?_⟩
  change integralReal * matrix = integralReal * matrix * rotation * rotation⁻¹
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem realSpecialLinearReducedCover_iUnion :
    (⋃ integral : integerSpecialLinearSubgroup, integral • realSpecialLinearReducedCover) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro matrix
  obtain ⟨integral, member⟩ := realSpecialLinearReducedCover_orbit matrix
  exact Set.mem_iUnion.mpr ⟨integral⁻¹, ⟨integral • matrix, member, inv_smul_smul integral matrix⟩⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
