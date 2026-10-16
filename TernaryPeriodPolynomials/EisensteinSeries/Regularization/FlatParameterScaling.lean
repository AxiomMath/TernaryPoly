module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.PlaneDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.NormContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem planeLevi_rankOne_binary {R : Type*} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    planeLevi binary scalar = planeLevi 1 scalar * planeLevi binary 1 := by
  change (planeLeviHom R) (binary, scalar) =
    (planeLeviHom R) (1, scalar) * (planeLeviHom R) (binary, 1)
  rw [← map_mul]
  simp

theorem flat_section_parabolic_scaling
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameter : ℂ) (first second : Adeles) (binary : BinaryAdelicGL)
    (scalar : Adelesˣ) (compactMatrix : AdelicGL) (compact_spec : inMaximalCompact compactMatrix) :
    family parameter (planeUnipotent first second * planeLevi binary scalar * compactMatrix) =
      normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) *
        normPower scalar (-2 * inductionExponent .plane parameter) *
          family cohomologicalPoint
            (planeUnipotent first second * planeLevi binary scalar * compactMatrix) := by
  have point_exponent : inductionExponent .plane cohomologicalPoint = 0 := by
    norm_num [inductionExponent, cohomologicalPoint]
  simp only [mul_assoc, (flat.1 parameter).2.2.2.1,
    (flat.1 cohomologicalPoint).2.2.2.1, planeLevi_rankOne_binary binary scalar,
    (flat.1 parameter).2.2.2.2.1, (flat.1 cohomologicalPoint).2.2.2.2.1,
    point_exponent, mul_zero, normPower_zero, mul_one,
    flat_section_compact_levi_scaling flat parameter binary compactMatrix compact_spec]
  ring

theorem flat_section_parabolic_determinant_scaling
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameter : ℂ) (first second : Adeles) (binary : BinaryAdelicGL)
    (scalar : Adelesˣ) (compactMatrix : AdelicGL) (compact_spec : inMaximalCompact compactMatrix) :
    family parameter (planeUnipotent first second * planeLevi binary scalar * compactMatrix) =
      normPower (GeneralLinearGroup.det
        (planeUnipotent first second * planeLevi binary scalar * compactMatrix))
          ((parameter - cohomologicalPoint) / 3) *
        normPower scalar (-(parameter - cohomologicalPoint)) *
          family cohomologicalPoint
            (planeUnipotent first second * planeLevi binary scalar * compactMatrix) := by
  rw [flat_section_parabolic_scaling flat parameter first second binary scalar compactMatrix compact_spec]
  simp only [map_mul, det_planeUnipotent, one_mul, det_planeLevi, normPower_mul,
    normPower_det_compact compactMatrix compact_spec, mul_one]
  have exponent : (parameter - cohomologicalPoint) / 3 = inductionExponent .plane parameter := by
    simp only [cohomologicalPoint, inductionExponent]
    ring
  have scalar_exponent : (parameter - cohomologicalPoint) / 3 + -(parameter - cohomologicalPoint) =
      -2 * inductionExponent .plane parameter := by
    simp only [cohomologicalPoint, inductionExponent]
    ring
  rw [mul_assoc (normPower (GeneralLinearGroup.det binary) ((parameter - cohomologicalPoint) / 3))
    (normPower scalar ((parameter - cohomologicalPoint) / 3))
    (normPower scalar (-(parameter - cohomologicalPoint))), ← normPower_add, scalar_exponent, exponent]

theorem atInfinity_mul (first second : RealGL3) :
    atInfinity (first * second) = atInfinity first * atInfinity second := by
  apply adelicGroup_eq_of_components
  · simp only [map_mul, realGroup_atInfinity]
  · simp only [map_mul, finiteGroup_atInfinity, mul_one]

theorem atInfinity_planeLevi (binary : BinaryRealGL) (scalar : ℝˣ) :
    atInfinity (planeLevi binary scalar) =
      planeLevi (atInfinity binary) (realAdeleUnit scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, planeLevi, planeBlock, realAdeleUnit]

theorem atInfinity_planeUnipotent (first second : ℝ) :
    atInfinity (planeUnipotent first second) =
      planeUnipotent (first, 0) (second, 0) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, planeUnipotent]

theorem atInfinity_orthogonal_compact (matrix : RealGL3)
    (orthogonal : matrix.val.transpose * matrix.val = 1) :
    inMaximalCompact (atInfinity matrix) := by
  constructor
  · simpa only [realGroup_atInfinity] using orthogonal
  · exact ⟨1, by rw [map_one, finiteGroup_atInfinity]⟩

theorem adelicGroup_real_finite (matrix : AdelicGL) :
    matrix = atInfinity (realGroup matrix) * atFinite (finiteGroup matrix) := by
  apply adelicGroup_eq_of_components
  · simp only [map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one]
  · simp only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]

theorem orthogonal_integral_compact (matrix : RealGL3) (finiteMatrix : FiniteGL)
    (orthogonal : matrix.val.transpose * matrix.val = 1)
    (integral : finiteMatrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    inMaximalCompact (atInfinity matrix * atFinite finiteMatrix) := by
  constructor
  · simpa only [map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one] using orthogonal
  · simpa only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul] using integral

theorem integral_finite_plane_decomposition (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ (first second : Adeles) (binary : BinaryAdelicGL) (scalar : ℝˣ) (compactMatrix : AdelicGL),
      matrix = planeUnipotent first second * planeLevi binary (realAdeleUnit scalar) * compactMatrix ∧
      inMaximalCompact compactMatrix ∧ scalar.val = realPlaneHeight (realGroup matrix) := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, orthogonal, scalar_height⟩ :=
    real_plane_levi_decomposition (realGroup matrix)
  refine ⟨(first, 0), (second, 0), atInfinity binary, scalar,
    atInfinity compactMatrix * atFinite (finiteGroup matrix), ?_,
    orthogonal_integral_compact compactMatrix _ orthogonal integral, scalar_height⟩
  calc
    matrix = atInfinity (realGroup matrix) * atFinite (finiteGroup matrix) := adelicGroup_real_finite matrix
    _ = _ := by
      rw [decomposition, atInfinity_mul, atInfinity_mul, atInfinity_planeUnipotent, atInfinity_planeLevi,
        mul_assoc]

theorem flat_section_integral_finite_scaling
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameter : ℂ) (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    family parameter matrix =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) / 3 -
          Real.log (realPlaneHeight (realGroup matrix)) : ℝ) : ℂ)) *
      family cohomologicalPoint matrix := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, compact_spec, scalar_height⟩ :=
    integral_finite_plane_decomposition matrix integral
  have scaling := flat_section_parabolic_determinant_scaling flat parameter first second binary
    (realAdeleUnit scalar) compactMatrix compact_spec
  rw [← decomposition, normPower_realAdeleUnit, scalar_height,
    abs_of_pos (realPlaneHeight_pos (realGroup matrix)), normPower, ← Complex.exp_add] at scaling
  convert scaling using 2
  congr 1
  push_cast
  ring

theorem flat_section_real_scaling
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameter : ℂ) (matrix : RealGL3) :
    family parameter (atInfinity matrix) =
      Complex.exp ((parameter - cohomologicalPoint) *
        ((Real.log |matrix.val.det| / 3 - Real.log (realPlaneHeight matrix) : ℝ) : ℂ)) *
      family cohomologicalPoint (atInfinity matrix) := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, orthogonal, scalar_height⟩ :=
    real_plane_levi_decomposition matrix
  have adelic_decomposition : atInfinity matrix =
      planeUnipotent (first, 0) (second, 0) *
        planeLevi (atInfinity binary) (realAdeleUnit scalar) * atInfinity compactMatrix := by
    rw [decomposition, atInfinity_mul, atInfinity_mul, atInfinity_planeUnipotent, atInfinity_planeLevi]
  have scaling := flat_section_parabolic_determinant_scaling flat parameter
    (first, 0) (second, 0) (atInfinity binary) (realAdeleUnit scalar) (atInfinity compactMatrix)
    (atInfinity_orthogonal_compact compactMatrix orthogonal)
  rw [← adelic_decomposition, det_atInfinity, normPower_realAdeleUnit, normPower_realAdeleUnit,
    scalar_height, abs_of_pos (realPlaneHeight_pos matrix), ← Complex.exp_add] at scaling
  simp only [GeneralLinearGroup.val_det_apply] at scaling
  convert scaling using 2
  congr 1
  push_cast
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
