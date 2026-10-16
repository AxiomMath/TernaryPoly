module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.FiniteDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.PlaneDecomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem planeLevi_multiply {R : Type*} [CommRing R]
    (first second : GeneralLinearGroup (Fin 2) R) (firstScalar secondScalar : Rˣ) :
    planeLevi (first * second) (firstScalar * secondScalar) =
      planeLevi first firstScalar * planeLevi second secondScalar :=
  (planeLeviHom R).map_mul (first, firstScalar) (second, secondScalar)

theorem planeLevi_inverse {R : Type*} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    (planeLevi binary scalar)⁻¹ = planeLevi binary⁻¹ scalar⁻¹ := by
  apply Units.ext
  rfl

theorem planeUnipotent_inverse {R : Type*} [CommRing R] (first second : R) :
    (planeUnipotent first second)⁻¹ = planeUnipotent (-first) (-second) := by
  apply Units.ext
  rfl

theorem planeParabolic_levi_first {R : Type*} [CommRing R]
    (matrix : GL3 R) (parabolic : InPlaneParabolic matrix) :
    ∃ (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) (first second : R),
      matrix = planeLevi binary scalar * planeUnipotent first second := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization matrix⁻¹ (inPlane_inv parabolic)
  refine ⟨binary⁻¹, scalar⁻¹, -first, -second, ?_⟩
  simpa only [inv_inv, _root_.mul_inv_rev, planeLevi_inverse, planeUnipotent_inverse] using
    congrArg Inv.inv factorization

theorem planeLevi_unipotent_commute {R : Type*} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) (first second : R) :
    planeLevi binary scalar * planeUnipotent first second =
      planeUnipotent ((binary.val 0 0 * first + binary.val 0 1 * second) * scalar.inv)
        ((binary.val 1 0 * first + binary.val 1 1 * second) * scalar.inv) *
          planeLevi binary scalar := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
      mul_assoc]

theorem finite_plane_rational_integral_decomposition (matrix : FiniteGL)
    (parabolic : InPlaneParabolic matrix) :
    ∃ rational : RationalGL3, ∃ integralMatrix : GL3 IntegralAdeles,
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding integralMatrix := by
  obtain ⟨binary, scalar, first, second, factorization⟩ :=
    planeParabolic_levi_first matrix parabolic
  obtain ⟨binaryRational, binaryIntegral, binary_decomposition⟩ :=
    binary_finite_rational_integral_decomposition binary
  obtain ⟨scalarRational, _, scalarIntegral, scalar_decomposition⟩ :=
    finiteIdele_rational_integral_decomposition scalar
  let integralBinary := GeneralLinearGroup.map integralEmbedding binaryIntegral
  let integralScalar := Units.map integralEmbedding.toMonoidHom scalarIntegral
  let firstCoordinate :=
    (integralBinary.val 0 0 * first + integralBinary.val 0 1 * second) * integralScalar.inv
  let secondCoordinate :=
    (integralBinary.val 1 0 * first + integralBinary.val 1 1 * second) * integralScalar.inv
  obtain ⟨firstRational, firstIntegral, first_approximation⟩ :=
    finiteAdele_rational_approximation firstCoordinate
  obtain ⟨secondRational, secondIntegral, second_approximation⟩ :=
    finiteAdele_rational_approximation secondCoordinate
  have unipotent_decomposition : planeUnipotent firstCoordinate secondCoordinate =
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
        (planeUnipotent firstRational secondRational) *
      GeneralLinearGroup.map integralEmbedding (planeUnipotent firstIntegral secondIntegral) := by
    rw [map_planeUnipotent, map_planeUnipotent, ← planeUnipotent_add]
    congr 1
    · exact (sub_eq_iff_eq_add.mp first_approximation).trans (add_comm _ _)
    · exact (sub_eq_iff_eq_add.mp second_approximation).trans (add_comm _ _)
  refine ⟨planeLevi binaryRational scalarRational * planeUnipotent firstRational secondRational,
    planeUnipotent firstIntegral secondIntegral * planeLevi binaryIntegral scalarIntegral, ?_⟩
  rw [factorization, binary_decomposition, scalar_decomposition, planeLevi_multiply,
    mul_assoc, planeLevi_unipotent_commute, ← map_planeLevi, ← map_planeLevi]
  change GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (planeLevi binaryRational scalarRational) *
        (planeUnipotent firstCoordinate secondCoordinate *
          GeneralLinearGroup.map integralEmbedding (planeLevi binaryIntegral scalarIntegral)) = _
  rw [unipotent_decomposition, map_mul, map_mul]
  simp only [mul_assoc]

theorem finite_rational_integral_decomposition (matrix : FiniteGL) :
    ∃ rational : RationalGL3, ∃ integralMatrix : GL3 IntegralAdeles,
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding integralMatrix := by
  obtain ⟨parabolic, integralMatrix, decomposition, parabolic_spec⟩ :=
    finite_plane_decomposition matrix
  obtain ⟨rational, parabolicIntegral, parabolic_decomposition⟩ :=
    finite_plane_rational_integral_decomposition parabolic parabolic_spec
  refine ⟨rational, parabolicIntegral * integralMatrix, ?_⟩
  rw [decomposition, parabolic_decomposition, map_mul, mul_assoc]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
