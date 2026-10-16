module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SmallDegreeLineVectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SmallDegreePlaneBoundary
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.DualHeightMinimum
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LineFactorization

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeLineBoundary

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open EisensteinRegularization.Helpers SmallDegreeLineVectors

theorem dual_planeParabolic_line {ring : Type*} [CommRing ring]
    (matrix : GL3 ring) (parabolic : InPlaneParabolic matrix) :
    InLineParabolic (weyl * generalLinearInverseTranspose ring matrix * weyl⁻¹) := by
  have inverse_parabolic := inPlane_inv parabolic
  constructor
  · simpa [generalLinearInverseTranspose, weyl, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three] using inverse_parabolic.1
  · simpa [generalLinearInverseTranspose, weyl, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three] using inverse_parabolic.2

theorem adelic_line_integral_decomposition (matrix : AdelicGL) :
    ∃ parabolic integralMatrix : AdelicGL,
      matrix = parabolic * integralMatrix ∧ InLineParabolic parabolic ∧
        finiteGroup integralMatrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
  obtain ⟨plane, compactMatrix, decomposition, parabolic, compact⟩ :=
    adelic_plane_decomposition (generalLinearInverseTranspose Adeles (weyl⁻¹ * matrix))
  refine ⟨weyl * generalLinearInverseTranspose Adeles plane * weyl⁻¹,
    weyl * generalLinearInverseTranspose Adeles compactMatrix, ?_,
    dual_planeParabolic_line plane parabolic, ?_⟩
  · have equality := congrArg (generalLinearInverseTranspose Adeles) decomposition
    rw [generalLinearInverseTranspose_involutive, map_mul] at equality
    calc
      matrix = (weyl : AdelicGL) * (weyl⁻¹ * matrix) :=
        (mul_inv_cancel_left (weyl : AdelicGL) matrix).symm
      _ = weyl * (generalLinearInverseTranspose Adeles plane *
          generalLinearInverseTranspose Adeles compactMatrix) :=
        congrArg (fun value : AdelicGL => weyl * value) equality
      _ = _ := by group
  · obtain ⟨integralMatrix, represents⟩ := compact.2
    refine ⟨weyl * generalLinearInverseTranspose IntegralAdeles integralMatrix, ?_⟩
    change GeneralLinearGroup.map integralEmbedding
      (weyl * generalLinearInverseTranspose IntegralAdeles integralMatrix) =
        GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)
          (weyl * generalLinearInverseTranspose Adeles compactMatrix)
    rw [map_mul, map_mul, map_weyl, map_weyl, ← generalLinearInverseTranspose_map,
      ← generalLinearInverseTranspose_map, represents]
    rfl

theorem lineParabolic_unipotent_factorization {ring : Type*} [CommRing ring]
    (matrix : GL3 ring) (parabolic : InLineParabolic matrix) :
    ∃ (first second : ring) (binary : GeneralLinearGroup (Fin 2) ring) (scalar : ringˣ),
      matrix = lineUnipotent first second * lineLevi scalar binary := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    lineParabolic_factorization matrix⁻¹ (inLine_inv parabolic)
  refine ⟨-first, -second, binary⁻¹, scalar⁻¹, ?_⟩
  have equality := congrArg (fun value : GL3 ring => value⁻¹) factorization
  have radical_inverse : (lineUnipotent first second)⁻¹ = lineUnipotent (-first) (-second) := by
    apply Units.ext
    rfl
  have levi_inverse : (lineLevi scalar binary)⁻¹ = lineLevi scalar⁻¹ binary⁻¹ :=
    ((lineLeviHom ring).map_inv (scalar, binary)).symm
  simpa only [inv_inv, _root_.mul_inv_rev, radical_inverse, levi_inverse] using equality

theorem line_induced_zero_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) (parameter : ℂ) (sectionValue : AdelicGL → ℂ)
    (induced : IsInduced data .line parameter sectionValue) : sectionValue = 0 := by
  funext matrix
  obtain ⟨parabolic, integralMatrix, decomposition, parabolic_spec, integral⟩ :=
    adelic_line_integral_decomposition matrix
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    lineParabolic_unipotent_factorization parabolic parabolic_spec
  rw [decomposition, factorization, mul_assoc, induced.2.2.2.1, lineLevi_split,
    mul_assoc, induced.2.2.2.2.1]
  have zero := lineCuspVector_small_degree_integral_zero small induced integralMatrix integral
  rw [← lineCuspVector_at_one induced (lineLevi 1 binary * integralMatrix),
    lineCuspVector_binary, zero, map_zero, smul_zero, map_zero]
  simp

theorem line_source_zero_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) (source : SourceCochain degree)
    (closed : IsSourceCocycle data .line source) : source = 0 := by
  funext vertices matrix
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact congrFun (line_induced_zero_of_small_degree small data cohomologicalPoint
    (fun argument => (source vertices argument).val.coeff monomial) (closed.1 vertices monomial)) matrix

theorem line_boundarySummand_eq_bot_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) : boundarySummand data .line = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro component ⟨source, closed, representative, evaluation, rfl⟩
  rw [line_source_zero_of_small_degree small data source closed] at evaluation
  rw [SmallDegreePlaneBoundary.evaluates_zero_source data .line representative evaluation, map_zero]
  exact Submodule.zero_mem _

theorem associatePair_eq_bot_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) : associatePair data = ⊥ := by
  simp [associatePair, SmallDegreePlaneBoundary.plane_boundarySummand_eq_bot_of_small_degree small data,
    line_boundarySummand_eq_bot_of_small_degree small data]

end TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeLineBoundary
