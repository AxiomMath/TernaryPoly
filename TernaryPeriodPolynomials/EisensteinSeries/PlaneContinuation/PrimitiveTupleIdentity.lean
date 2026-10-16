module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.RecoveryOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryOperator
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveTupleIdentity

theorem coefficient_parameter {degree : ℕ} (data : InducingData degree) (first second : ℂ)
    (point : AdelicGL) (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL)
    (primitive : binary ∈ FinitePrimitiveRecovery.integralGroup) :
    RecoveryCoefficients.coefficient data first point key binary = RecoveryCoefficients.coefficient data second point key binary := by
  obtain ⟨integer, rfl⟩ := primitive
  unfold RecoveryCoefficients.coefficient
  congr 1
  change innerCharacter data first (GeneralLinearGroup.det (BinaryQuotientAverage.inclusion integer)) =
    innerCharacter data second (GeneralLinearGroup.det (BinaryQuotientAverage.inclusion integer))
  rw [RecoveryBinarySymmetry.inner_integral, RecoveryBinarySymmetry.inner_integral]

theorem primitiveOperator_integral {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (vector : data.cusp.H) :
    RecoveryOperatorLimit.primitiveOperator data reference halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
      ⟨point, rfl⟩ key vector =
        ∫ binary in FinitePrimitiveRecovery.integralGroup,
          RecoveryCoefficients.coefficient data reference (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary •
            data.cusp.π (atFinite binary) vector ∂BinaryProductHaar.finiteMeasure := by
  change (∫ binary,
    RecoveryOperatorLimit.primitiveCoefficient data reference
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary •
        data.cusp.π (atFinite binary) vector ∂BinaryProductHaar.finiteMeasure) = _
  rw [← integral_indicator FinitePrimitiveRecovery.integralGroup_isOpen.measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  by_cases inside : binary ∈ FinitePrimitiveRecovery.integralGroup
  · simp only [RecoveryOperatorLimit.primitiveCoefficient, Set.indicator_of_mem inside]
  · simp only [RecoveryOperatorLimit.primitiveCoefficient, Set.indicator_of_notMem inside, zero_smul]

theorem primitiveRow_integral {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) (value : Space data) :
    primitiveRow data reference halfPlane point value =
      ∫ binary in FinitePrimitiveRecovery.integralGroup,
        PrimitiveTupleKernel.kernel data reference (atFinite (GeneralLinearGroup.map integralEmbedding point)) value binary
          ∂BinaryProductHaar.finiteMeasure := by
  rw [primitiveRow_apply]
  simp only [primitiveOperator_integral]
  symm
  apply integral_finsetSum Finset.univ
  intro key _
  exact (FiniteHilbertConvolution.integrand_integrable data.cusp _
    (RecoveryCoefficients.coefficient_integrable data reference halfPlane
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) (value key)).integrableOn

theorem primitiveRow_tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re)
    (point : IntegralFiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value) :
    primitiveRow data reference halfPlane point (tuple induced value) =
      (FinitePrimitiveRecovery.mass : ℂ) •
        (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value)).val := by
  rw [primitiveRow_integral]
  have kernelEquality (binary : BinaryFiniteGL) (primitive : binary ∈ FinitePrimitiveRecovery.integralGroup) :
      PrimitiveTupleKernel.kernel data reference (atFinite (GeneralLinearGroup.map integralEmbedding point)) (tuple induced value) binary =
        (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value)).val := by
    have parameterEquality : PrimitiveTupleKernel.kernel data reference (atFinite (GeneralLinearGroup.map integralEmbedding point))
        (tuple induced value) binary = PrimitiveTupleKernel.kernel data parameter
          (atFinite (GeneralLinearGroup.map integralEmbedding point)) (tuple induced value) binary := by
      simp only [PrimitiveTupleKernel.kernel, coefficient_parameter data reference parameter _ _ binary primitive]
    exact parameterEquality.trans (PrimitiveTupleKernel.kernel_chart induced point value fullRank binary primitive)
  rw [setIntegral_congr_fun FinitePrimitiveRecovery.integralGroup_isOpen.measurableSet kernelEquality, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, FinitePrimitiveRecovery.mass, Complex.coe_smul]

theorem primitiveProjectedRow_tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re)
    (point : IntegralFiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value) :
    primitiveProjectedRow data reference halfPlane point (tuple induced value) =
      (FinitePrimitiveRecovery.mass : ℂ) •
        (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value)).val := by
  rw [primitiveProjectedRow, ContinuousLinearMap.comp_apply, primitiveRow_tuple induced reference halfPlane point value fullRank,
    map_smul, CompactAveraging.averagingOperator_of_fixed data.cusp finiteCongruence _ (profile_fixed induced point value fullRank)]

theorem normalized_right_level {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (matrix : IntegralFiniteGL) (level : matrix ∈ FiniteSectionProjection.integralLevel) :
    FiniteProfileResidues.character data matrix • normalized induced (point * FiniteSectionProjection.inclusion matrix) =
      normalized induced point := by
  have levelElement : GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel := ⟨matrix, level, rfl⟩
  have vector := CuspVectors.planeCuspVector_finiteLevel induced point
    ⟨GeneralLinearGroup.map integralEmbedding matrix, levelElement⟩
  change CuspVectors.planeCuspVector induced
    (point * FiniteSectionProjection.inclusion matrix) = CuspVectors.planeCuspVector induced point at vector
  unfold normalized
  rw [vector, map_mul, map_mul]
  change FiniteProfileResidues.character data matrix •
    ((outerCharacter data parameter (GeneralLinearGroup.det point) *
      outerCharacter data parameter (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding matrix))))⁻¹ • _) = _
  rw [RecoveryLevel.outer_integral, smul_smul, mul_inv]
  have scalar : FiniteProfileResidues.character data matrix *
      ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * (FiniteProfileResidues.character data matrix)⁻¹) =
        (outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ := by
    rw [mul_left_comm, mul_inv_cancel₀ (FiniteProfileResidues.character_nonzero data matrix), mul_one]
  rw [scalar]

theorem profile_right_level {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point matrix : IntegralFiniteGL) (level : matrix ∈ FiniteSectionProjection.integralLevel)
    (value : Rectangular ℝ) (fullRank : FullRank value) :
    FiniteProfileResidues.character data matrix •
      profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding (point * matrix)) value) =
        profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value) := by
  rw [RealFrameChart.profile_eq induced _ value fullRank, RealFrameChart.profile_eq induced _ value fullRank]
  have equality : atFinite (GeneralLinearGroup.map integralEmbedding (point * matrix)) * atInfinity (RealFrameChart.point value) =
      (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity (RealFrameChart.point value)) *
        FiniteSectionProjection.inclusion matrix := by
    rw [map_mul, atFinite_mul, mul_assoc, atFinite_atInfinity_commute, ← mul_assoc]
    rfl
  rw [equality]
  exact normalized_right_level induced _ matrix level

theorem primitiveAveragedRow_tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re)
    (point : IntegralFiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value) :
    primitiveAveragedRow data reference halfPlane point (tuple induced value) =
      (FinitePrimitiveRecovery.mass : ℂ) •
        (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value)).val := by
  simp only [primitiveAveragedRow, _root_.smul_apply, _root_.sum_apply,
    primitiveProjectedRow_tuple induced reference halfPlane _ value fullRank]
  have term (residue : FiniteSectionProjection.levelImage data) :
      FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue) •
        ((FinitePrimitiveRecovery.mass : ℂ) • (profile induced (adelicFrame
          (GeneralLinearGroup.map integralEmbedding (point * FiniteSectionProjection.representative data residue)) value)).val) =
        (FinitePrimitiveRecovery.mass : ℂ) •
          (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value)).val := by
    rw [smul_comm]
    exact congrArg (fun vector : data.cusp.smooth => (FinitePrimitiveRecovery.mass : ℂ) • vector.val)
      (profile_right_level induced point _ (FiniteSectionProjection.representative_level data residue) value fullRank)
  simp only [term, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀]
  exact_mod_cast Fintype.card_ne_zero

theorem primitiveOperator_tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re)
    (value : Rectangular ℝ) (fullRank : FullRank value) :
    primitiveOperator data reference halfPlane (tuple induced value) = (FinitePrimitiveRecovery.mass : ℂ) • tuple induced value := by
  funext key
  exact primitiveAveragedRow_tuple induced reference halfPlane (UniversalFiniteProfiles.representative data key) value fullRank

theorem admissible_identity {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (value : Space data) (membership : value ∈ admissible data) :
    primitiveOperator data reference halfPlane value = (FinitePrimitiveRecovery.mass : ℂ) • value := by
  let difference : Space data →L[ℂ] Space data := primitiveOperator data reference halfPlane -
    (FinitePrimitiveRecovery.mass : ℂ) • ContinuousLinearMap.id ℂ (Space data)
  have contained : admissible data ≤ difference.ker := by
    apply (Submodule.span ℂ (generators data)).topologicalClosure_minimal _ difference.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨parameter, function, induced, frame, fullRank, rfl⟩
    change primitiveOperator data reference halfPlane (tuple induced frame) -
      (FinitePrimitiveRecovery.mass : ℂ) • tuple induced frame = 0
    rw [primitiveOperator_tuple induced reference halfPlane frame fullRank, sub_self]
  have equality := contained membership
  change primitiveOperator data reference halfPlane value - (FinitePrimitiveRecovery.mass : ℂ) • value = 0 at equality
  exact sub_eq_zero.mp equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveTupleIdentity
