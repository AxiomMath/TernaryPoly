module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.RowReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SourceComparison.RationalInvariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeLineVectors

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open EisensteinRegularization.Helpers

def lineCuspVector {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (matrix : AdelicGL) : data.cusp.smooth :=
  Classical.choose (induced.2.2.2.2.2 matrix)

theorem lineCuspVector_realize {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    data.cusp.realize (lineCuspVector induced matrix) binary =
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .line parameter) *
        sectionValue (lineLevi 1 binary * matrix) :=
  congrFun (Classical.choose_spec (induced.2.2.2.2.2 matrix)) binary

theorem lineCuspVector_at_one {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (matrix : AdelicGL) : data.cusp.realize (lineCuspVector induced matrix) 1 = sectionValue matrix := by
  rw [lineCuspVector_realize, map_one, normPower_one, one_mul]
  have levi_one : lineLevi 1 (1 : BinaryAdelicGL) = 1 := (lineLeviHom Adeles).map_one
  rw [levi_one, one_mul]

theorem lineCuspVector_binary {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    lineCuspVector induced (lineLevi 1 binary * matrix) =
      normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) •
        cuspSmoothAction data.cusp binary (lineCuspVector induced matrix) := by
  apply data.cusp.injective
  funext argument
  have levi_mul : lineLevi 1 (argument * binary) = lineLevi 1 argument * lineLevi 1 binary := by
    change (lineLeviHom Adeles) (1, argument * binary) =
      (lineLeviHom Adeles) (1, argument) * (lineLeviHom Adeles) (1, binary)
    simpa only [Prod.mk_mul_mk, one_mul] using (lineLeviHom Adeles).map_mul (1, argument) (1, binary)
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  change data.cusp.realize (lineCuspVector induced (lineLevi 1 binary * matrix)) argument =
    normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) *
      data.cusp.realize ⟨data.cusp.π binary (lineCuspVector induced matrix).val,
        data.cusp.smooth_stable binary _ (lineCuspVector induced matrix).property⟩ argument
  rw [data.cusp.equivariant,
    lineCuspVector_realize, lineCuspVector_realize, ← mul_assoc, ← levi_mul,
    map_mul, normPower_mul]
  have cancel : normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) *
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .line parameter) = 1 := by
    rw [← normPower_add, add_neg_cancel, normPower_zero]
  calc
    _ = normPower (GeneralLinearGroup.det argument) (-binaryInductionExponent degree .line parameter) *
        (normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) *
          normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .line parameter)) *
        sectionValue (lineLevi 1 (argument * binary) * matrix) := by rw [cancel, mul_one]
    _ = _ := by ring

theorem reduced_row_lineLevi_fixed (row : Fin 3 → ZMod 3) (zero : row 1 = 0)
    (binary : GeneralLinearGroup (Fin 2) (ZMod 3)) (fixed : binary ∈ binaryReducedRowStabilizer) :
    row ᵥ* (lineLevi 1 binary).val = row := by
  obtain ⟨first, second⟩ := (binaryReducedRowStabilizer_mem binary).mp fixed
  ext column
  fin_cases column <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, lineLevi_val, zero, first, second]

theorem binaryRowLevel_lineLevi_conjugate_mem (binary : binaryRowLevel)
    (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (zero : (lastRow ᵥ* (GeneralLinearGroup.map integralReduction matrix)⁻¹.val) 1 = 0) :
    (GeneralLinearGroup.map integralEmbedding matrix)⁻¹ * lineLevi 1 binary.val *
      GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel := by
  obtain ⟨integralBinary, reduced, represents⟩ := binary.property
  refine ⟨matrix⁻¹ * lineLevi 1 integralBinary * matrix, ?_, ?_⟩
  · change lastRow ᵥ* (GeneralLinearGroup.map integralReduction
      (matrix⁻¹ * lineLevi 1 integralBinary * matrix)).val = lastRow
    simp only [map_mul, map_inv, map_lineLevi, map_one, Units.val_mul]
    rw [← vecMul_vecMul, ← vecMul_vecMul,
      reduced_row_lineLevi_fixed _ zero _ reduced, vecMul_vecMul,
      ← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one, vecMul_one]
  · simp only [map_mul, map_inv, map_lineLevi, map_one, represents]

theorem integral_line_row_reduction (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    ∃ binary : SpecialLinearGroup (Fin 2) ℤ,
      (lastRow ᵥ* (GeneralLinearGroup.map integralReduction
        (lineLevi 1 (SpecialLinearGroup.mapGL IntegralAdeles binary) * matrix))⁻¹.val) 1 = 0 := by
  let row := lastRow ᵥ* (GeneralLinearGroup.map integralReduction matrix)⁻¹.val
  obtain ⟨binary, zero⟩ := binaryIntegralRowRepresentatives_reduce ![row 1, row 2]
  refine ⟨binary, ?_⟩
  have levi_inv : (lineLevi 1 (SpecialLinearGroup.mapGL (ZMod 3) binary))⁻¹ =
      lineLevi 1 (SpecialLinearGroup.mapGL (ZMod 3) binary)⁻¹ := by
    change ((lineLeviHom (ZMod 3)) (1, SpecialLinearGroup.mapGL (ZMod 3) binary))⁻¹ =
      (lineLeviHom (ZMod 3)) (1, (SpecialLinearGroup.mapGL (ZMod 3) binary)⁻¹)
    simpa only [Prod.inv_mk, inv_one] using
      (map_inv (lineLeviHom (ZMod 3)) (1, SpecialLinearGroup.mapGL (ZMod 3) binary)).symm
  rw [map_mul, map_lineLevi, map_one, binaryIntegral_mapGL_map, _root_.mul_inv_rev, levi_inv]
  change (lastRow ᵥ* ((GeneralLinearGroup.map integralReduction matrix)⁻¹.val *
    (lineLevi 1 (SpecialLinearGroup.mapGL (ZMod 3) binary)⁻¹).val)) 1 = 0
  rw [← vecMul_vecMul]
  change (row ᵥ* (lineLevi 1 (SpecialLinearGroup.mapGL (ZMod 3) binary)⁻¹).val) 1 = 0
  simpa [lineLevi_val, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using zero

theorem atFinite_lineLevi (binary : BinaryFiniteGL) :
    atFinite (lineLevi 1 binary) = lineLevi 1 (atFinite binary) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, lineLevi_val]

theorem lineCuspVector_rowLevel_fixed {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (matrix : AdelicGL) (integralMatrix : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (represents : GeneralLinearGroup.map integralEmbedding integralMatrix = finiteGroup matrix)
    (zero : (lastRow ᵥ* (GeneralLinearGroup.map integralReduction integralMatrix)⁻¹.val) 1 = 0)
    (binary : binaryRowLevel) :
    data.cusp.π (atFinite binary.val) (lineCuspVector induced matrix).val =
      (lineCuspVector induced matrix).val := by
  have in_level : (finiteGroup matrix)⁻¹ * lineLevi 1 binary.val * finiteGroup matrix ∈ finiteLevel := by
    rw [← represents]
    exact binaryRowLevel_lineLevi_conjugate_mem binary integralMatrix zero
  have norm_one : normPower (GeneralLinearGroup.det (atFinite binary.val))
      (binaryInductionExponent degree .line parameter) = 1 := by
    obtain ⟨integralBinary, _, represents⟩ := binary.property
    rw [← represents]
    exact binaryIntegral_det_normPower integralBinary _
  have eigen := lineCuspVector_binary induced matrix (atFinite binary.val)
  rw [norm_one, one_smul, ← atFinite_lineLevi, atFinite_left_conjugate] at eigen
  have finite_invariance : lineCuspVector induced
      (matrix * atFinite ((finiteGroup matrix)⁻¹ * lineLevi 1 binary.val * finiteGroup matrix)) =
        lineCuspVector induced matrix := by
    apply data.cusp.injective
    funext evaluationPoint
    rw [lineCuspVector_realize, lineCuspVector_realize, ← mul_assoc, induced.2.1 ⟨_, in_level⟩]
  rw [finite_invariance] at eigen
  exact congrArg Subtype.val eigen.symm

theorem lineCuspVector_small_degree_integral_zero {degree : ℕ} (small : degree < 3)
    {data : InducingData degree} {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced data .line parameter sectionValue) (matrix : AdelicGL)
    (finite_integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    lineCuspVector induced matrix = 0 := by
  obtain ⟨integralMatrix, represents⟩ := finite_integral
  obtain ⟨binary, row_zero⟩ := integral_line_row_reduction integralMatrix
  let translated := atFinite (lineLevi 1 (SpecialLinearGroup.mapGL FiniteAdeles binary)) * matrix
  have translated_represents : GeneralLinearGroup.map integralEmbedding
      (lineLevi 1 (SpecialLinearGroup.mapGL IntegralAdeles binary) * integralMatrix) = finiteGroup translated := by
    simp only [translated, map_mul, map_lineLevi, map_one, binaryIntegral_mapGL_map,
      represents, finiteGroup_atFinite]
  have translated_zero : lineCuspVector induced translated = 0 :=
    cohomological_small_degree_rowLevel_zero data.cohomological small
      ⟨lineCuspVector induced translated,
        lineCuspVector_rowLevel_fixed induced translated _ translated_represents row_zero⟩
  have norm_one : normPower (GeneralLinearGroup.det (atFinite (SpecialLinearGroup.mapGL FiniteAdeles binary)))
      (binaryInductionExponent degree .line parameter) = 1 := by
    rw [← binaryIntegral_mapGL_map integralEmbedding binary]
    exact binaryIntegral_det_normPower _ _
  change lineCuspVector induced
    (atFinite (lineLevi 1 (SpecialLinearGroup.mapGL FiniteAdeles binary)) * matrix) = 0 at translated_zero
  rw [atFinite_lineLevi, lineCuspVector_binary, norm_one, one_smul] at translated_zero
  by_contra nonzero
  exact cuspSmoothAction_ne_zero data.cusp _ _ nonzero translated_zero

end TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeLineVectors
