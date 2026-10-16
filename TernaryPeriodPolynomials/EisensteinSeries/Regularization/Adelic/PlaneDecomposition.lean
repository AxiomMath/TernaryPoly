module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.PlaneDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlatParameterScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem atFinite_mul (first second : FiniteGL) :
    atFinite (first * second) = atFinite first * atFinite second := by
  apply adelicGroup_eq_of_components
  · simp only [map_mul, realGroup_atFinite, mul_one]
  · simp only [map_mul, finiteGroup_atFinite]

theorem atInfinity_atFinite_commute (realMatrix : RealGL3) (finiteMatrix : FiniteGL) :
    atInfinity realMatrix * atFinite finiteMatrix = atFinite finiteMatrix * atInfinity realMatrix := by
  apply adelicGroup_eq_of_components
  · simp only [map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one, one_mul]
  · simp only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, mul_one, one_mul]

theorem planeParabolic_atInfinity {matrix : RealGL3} (parabolic : InPlaneParabolic matrix) :
    InPlaneParabolic (atInfinity matrix) := by
  constructor
  · apply Prod.ext
    · exact parabolic.1
    · rfl
  · apply Prod.ext
    · exact parabolic.2
    · rfl

theorem planeParabolic_atFinite {matrix : FiniteGL} (parabolic : InPlaneParabolic matrix) :
    InPlaneParabolic (atFinite matrix) := by
  constructor
  · apply Prod.ext
    · rfl
    · exact parabolic.1
  · apply Prod.ext
    · rfl
    · exact parabolic.2

theorem adelic_plane_decomposition (matrix : AdelicGL) :
    ∃ parabolic compactMatrix : AdelicGL,
      matrix = parabolic * compactMatrix ∧ InPlaneParabolic parabolic ∧ inMaximalCompact compactMatrix := by
  obtain ⟨realParabolic, realCompact, real_decomposition, real_parabolic, real_orthogonal, _⟩ :=
    real_plane_decomposition (realGroup matrix)
  obtain ⟨finiteParabolic, finiteIntegral, finite_decomposition, finite_parabolic⟩ :=
    finite_plane_decomposition (finiteGroup matrix)
  refine ⟨atInfinity realParabolic * atFinite finiteParabolic,
    atInfinity realCompact * atFinite (GeneralLinearGroup.map integralEmbedding finiteIntegral), ?_,
    inPlane_mul (planeParabolic_atInfinity real_parabolic) (planeParabolic_atFinite finite_parabolic),
    orthogonal_integral_compact realCompact _ real_orthogonal ⟨finiteIntegral, rfl⟩⟩
  apply adelicGroup_eq_of_components
  · simpa only [map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one] using real_decomposition
  · simpa only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul] using finite_decomposition

theorem adelic_plane_levi_decomposition (matrix : AdelicGL) :
    ∃ (first second : Adeles) (binary : BinaryAdelicGL) (scalar : Adelesˣ) (compactMatrix : AdelicGL),
      matrix = planeUnipotent first second * planeLevi binary scalar * compactMatrix ∧
        inMaximalCompact compactMatrix := by
  obtain ⟨parabolic, compactMatrix, decomposition, parabolic_spec, compact_spec⟩ :=
    adelic_plane_decomposition matrix
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization parabolic parabolic_spec
  exact ⟨first, second, binary, scalar, compactMatrix, by rw [← factorization]; exact decomposition,
    compact_spec⟩

theorem flat_section_real_exponential
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    ∃ weight : ℝ, ∀ parameter : ℂ, family parameter matrix =
      Complex.exp ((parameter - cohomologicalPoint) * (weight : ℂ)) * family cohomologicalPoint matrix := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, compact_spec⟩ :=
    adelic_plane_levi_decomposition matrix
  refine ⟨Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) / 3 -
    Real.log (adeleNorm scalar : ℝ), ?_⟩
  intro parameter
  have scaling := flat_section_parabolic_determinant_scaling flat parameter first second binary scalar
    compactMatrix compact_spec
  rw [← decomposition, normPower, normPower, ← Complex.exp_add] at scaling
  convert scaling using 2
  congr 1
  push_cast
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
