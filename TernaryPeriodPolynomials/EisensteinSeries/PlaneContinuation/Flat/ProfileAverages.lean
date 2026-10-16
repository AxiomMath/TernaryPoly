module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfileInterpolation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.GodementAverages
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PrimitiveFrameRecovery

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileInterpolation TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileAverages

section Assembly

variable {KeyType : Type} [Fintype KeyType] {degree : ℕ} (data : InducingData degree)
variable (families : KeyType → RealFamily data) (boxes : KeyType → Boxes)

theorem meromorphic (point : AdelicGL) (parameter : ℂ) :
    MeromorphicAt (fun parameter => average (continuation data families boxes parameter) point) parameter :=
  FiniteGodementAverages.meromorphic data Finset.univ _ _ _ _ _
    (fun index => (families index.1).continuous) (fun index => (families index.1).holomorphic)
    (fun index => (families index.1).bounded) point parameter

theorem integrable (point : AdelicGL) (parameter : ℂ) :
    Integrable (fun pair : Adeles × Adeles => continuation data families boxes parameter
      (planeUnipotent pair.1 pair.2 * point)) parameterMeasure :=
  FiniteGodementAverages.integrable data Finset.univ _ _ _ _ _
    (fun index => (families index.1).continuous) (fun index => (families index.1).holomorphic)
    (fun index => (families index.1).bounded) point parameter

theorem average_section (point : AdelicGL) (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    average (continuation data families boxes parameter) point =
      VectorGodement.sectionFunction data (test data families boxes parameter) parameter point :=
  FiniteGodementAverages.average_section data Finset.univ _ _ _ _ _
    (fun index => (families index.1).continuous) (fun index => (families index.1).holomorphic)
    (fun index => (families index.1).bounded) point parameter halfPlane

end Assembly

theorem exists_interpolation {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ test : ℂ → Rectangular Adeles → data.cusp.smooth, ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test parameter) parameter point) continuation ∧
      (∀ point parameter, MeromorphicAt (fun parameter => average (continuation parameter) point) parameter) ∧
      (∀ point parameter, Integrable (fun pair : Adeles × Adeles =>
        continuation parameter (planeUnipotent pair.1 pair.2 * point)) parameterMeasure) ∧
      (∀ (parameter : ℂ) (point : AdelicGL), (1 - (degree : ℝ)) / 2 < parameter.re →
        Integrable (VectorGodement.integrand data (test parameter) parameter point) BinaryHaar.measure) ∧
      ∀ parameter (point : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
        test parameter (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) =
          cutoff value • profile (flat.1 parameter)
            (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) := by
  choose families image using fun key : Key flat =>
    exists_realFamily flat (representative flat key) cutoff smooth compact supported
  choose boxes boxValue using fun key : Key flat => exists_boxes flat key
  refine ⟨test data families boxes, continuation data families boxes, continues data families boxes,
    meromorphic data families boxes, integrable data families boxes, test_integrable data families boxes, ?_⟩
  intro parameter point value fullRank
  rw [test_eq, finite_adelicFrame, archimedean_adelicFrame]
  simp only [boxValue, image, LinearEquiv.symm_apply_apply]
  let selected : Key flat := ⟨profileKey flat point, ⟨point, rfl⟩⟩
  rw [Finset.sum_eq_single selected]
  · have keyEquality := congrFun (congrFun (representative_key flat selected) parameter) ⟨value, fullRank⟩
    change profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding
      (representative flat selected)) value) =
      profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) at keyEquality
    simp only [selected, ite_true, one_smul, keyEquality]
  · intro key _ different
    have unequal : profileKey flat point ≠ key.val := by
      intro equality
      exact different (Subtype.ext equality.symm)
    simp only [ite_eq_right unequal, zero_smul]
  · simp

theorem exists_recovery {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ test : ℂ → Rectangular Adeles → data.cusp.smooth, ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test parameter) parameter point) continuation ∧
      (∀ point parameter, MeromorphicAt (fun parameter => average (continuation parameter) point) parameter) ∧
      (∀ point parameter, Integrable (fun pair : Adeles × Adeles =>
        continuation parameter (planeUnipotent pair.1 pair.2 * point)) parameterMeasure) ∧
      (∀ point parameter, (1 - (degree : ℝ)) / 2 < parameter.re →
        average (continuation parameter) point = VectorGodement.sectionFunction data (test parameter) parameter point) ∧
      (∀ (parameter : ℂ) (point : AdelicGL), (1 - (degree : ℝ)) / 2 < parameter.re →
        Integrable (VectorGodement.integrand data (test parameter) parameter point) BinaryHaar.measure) ∧
      ∀ parameter (point : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
        test parameter (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) =
          cutoff value • profile (flat.1 parameter)
            (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) := by
  choose families image using fun key : Key flat =>
    exists_realFamily flat (representative flat key) cutoff smooth compact supported
  choose boxes boxValue using fun key : Key flat => exists_boxes flat key
  refine ⟨test data families boxes, continuation data families boxes, continues data families boxes,
    meromorphic data families boxes, integrable data families boxes, average_section data families boxes,
    test_integrable data families boxes, ?_⟩
  intro parameter point value fullRank
  rw [test_eq, finite_adelicFrame, archimedean_adelicFrame]
  simp only [boxValue, image, LinearEquiv.symm_apply_apply]
  let selected : Key flat := ⟨profileKey flat point, ⟨point, rfl⟩⟩
  rw [Finset.sum_eq_single selected]
  · have keyEquality := congrFun (congrFun (representative_key flat selected) parameter) ⟨value, fullRank⟩
    change profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding
      (representative flat selected)) value) =
      profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) at keyEquality
    simp only [selected, ite_true, one_smul, keyEquality]
  · intro key _ different
    have unequal : profileKey flat point ≠ key.val := by
      intro equality
      exact different (Subtype.ext equality.symm)
    simp only [ite_eq_right unequal, zero_smul]
  · simp

theorem exists_meromorphic_decomposition {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ test : ℂ → Rectangular Adeles → data.cusp.smooth, ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test parameter) parameter point) continuation ∧
      (∀ point parameter, MeromorphicAt (fun parameter => average (continuation parameter) point) parameter) ∧
      ∀ (parameter : ℂ) (point : AdelicGL), (1 - (degree : ℝ)) / 2 < parameter.re →
        finiteGroup point ∈ Set.range (Matrix.GeneralLinearGroup.map integralEmbedding) →
          average (continuation parameter) point = PrimitiveFrameRecovery.mass cutoff point * sectionFunction parameter point +
            PrimitiveFrameRecovery.remainder data (test parameter) parameter point := by
  obtain ⟨test, continuation, continues, meromorphic, _, recovery, integrable, interpolation⟩ :=
    exists_recovery flat cutoff smooth compact supported
  refine ⟨test, continuation, continues, meromorphic, ?_⟩
  intro parameter point halfPlane pointIntegral
  rw [recovery point parameter halfPlane]
  exact PrimitiveFrameRecovery.section_eq (flat.1 parameter) (test parameter) cutoff (interpolation parameter)
    point pointIntegral (integrable parameter point halfPlane)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileAverages
