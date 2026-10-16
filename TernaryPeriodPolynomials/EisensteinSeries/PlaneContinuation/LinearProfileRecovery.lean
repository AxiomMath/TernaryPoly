module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UniversalFiniteProfiles
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.SectionAlgebra
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfileAverages

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LinearProfileRecovery

def test {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (cutoff : Rectangular ℝ → ℝ)
    (value : Rectangular Adeles) : data.cusp.smooth :=
  ∑ key : UniversalFiniteProfiles.Key data,
    (UniversalFiniteProfiles.boxes data key).test (finite value) •
      (cutoff (coordinateEquiv.symm (archimedean value)) •
        profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding
          (UniversalFiniteProfiles.representative data key)) (coordinateEquiv.symm (archimedean value))))

theorem test_add {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (cutoff : Rectangular ℝ → ℝ) :
    test (induced_add firstInduced secondInduced) cutoff =
      test firstInduced cutoff + test secondInduced cutoff := by
  funext value
  simp only [test, profile_add firstInduced secondInduced, smul_add, Finset.sum_add_distrib, Pi.add_apply]

theorem test_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (coefficient : ℂ) (cutoff : Rectangular ℝ → ℝ) :
    test (induced_smul induced coefficient) cutoff = coefficient • test induced cutoff := by
  funext value
  simp only [test, profile_smul induced coefficient, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro key _
  rw [smul_comm _ coefficient, smul_comm _ coefficient]

def testLinear {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (cutoff : Rectangular ℝ → ℝ) :
    inducedSpace data parameter →ₗ[ℂ] (Rectangular Adeles → data.cusp.smooth) where
  toFun := fun function => test function.property cutoff
  map_add' := fun first second => test_add first.property second.property cutoff
  map_smul' := fun coefficient function => test_smul function.property coefficient cutoff

def flatTestLinear {degree : ℕ} (data : InducingData degree) (cutoff : Rectangular ℝ → ℝ) :
    flatSpace data →ₗ[ℂ] (ℂ → Rectangular Adeles → data.cusp.smooth) where
  toFun := fun function parameter => test (function.property.1 parameter) cutoff
  map_add' := fun first second => funext (fun parameter =>
    test_add (first.property.1 parameter) (second.property.1 parameter) cutoff)
  map_smul' := fun coefficient function => funext (fun parameter =>
    test_smul (function.property.1 parameter) coefficient cutoff)

theorem test_primitive {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular ℝ → ℝ) (point : IntegralFiniteGL) (value : Rectangular ℝ)
    (fullRank : FullRank value) :
    test induced cutoff (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value) =
      cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value) := by
  simp only [test, FlatProfileInterpolation.finite_adelicFrame, FlatProfileInterpolation.archimedean_adelicFrame,
    LinearEquiv.symm_apply_apply, UniversalFiniteProfiles.boxes_frame]
  rw [Finset.sum_eq_single (UniversalFiniteProfiles.selected data point)]
  · have selectedEquality : UniversalFiniteProfiles.profileKey data point =
        (UniversalFiniteProfiles.selected data point).val := rfl
    rw [ite_eq_left selectedEquality, one_smul, UniversalFiniteProfiles.profile_eq_selected induced point value fullRank]
  · intro key _ different
    have unequal : UniversalFiniteProfiles.profileKey data point ≠ key.val := by
      intro equality
      exact different (Subtype.ext equality.symm)
    simp only [ite_eq_right unequal, zero_smul]
  · simp

theorem exists_recovery {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test (flat.1 parameter) cutoff) parameter point)
        continuation ∧
      (∀ point parameter, MeromorphicAt (fun parameter => average (continuation parameter) point) parameter) ∧
      (∀ point parameter, Integrable (fun pair : Adeles × Adeles =>
        continuation parameter (planeUnipotent pair.1 pair.2 * point)) parameterMeasure) ∧
      (∀ point parameter, (1 - (degree : ℝ)) / 2 < parameter.re →
        average (continuation parameter) point =
          VectorGodement.sectionFunction data (test (flat.1 parameter) cutoff) parameter point) ∧
      (∀ (parameter : ℂ) (point : AdelicGL), (1 - (degree : ℝ)) / 2 < parameter.re →
        Integrable (VectorGodement.integrand data (test (flat.1 parameter) cutoff) parameter point) BinaryHaar.measure) := by
  choose families image using fun key : UniversalFiniteProfiles.Key data =>
    exists_realFamily flat (UniversalFiniteProfiles.representative data key) cutoff smooth compact supported
  have equality : FlatProfileInterpolation.test data families (UniversalFiniteProfiles.boxes data) =
      fun parameter => test (flat.1 parameter) cutoff := by
    funext parameter value
    rw [FlatProfileInterpolation.test_eq]
    simp only [image]
    rfl
  refine ⟨FlatProfileInterpolation.continuation data families (UniversalFiniteProfiles.boxes data), ?_,
    FlatProfileAverages.meromorphic data families (UniversalFiniteProfiles.boxes data),
    FlatProfileAverages.integrable data families (UniversalFiniteProfiles.boxes data), ?_, ?_⟩
  · simpa only [equality] using FlatProfileInterpolation.continues data families (UniversalFiniteProfiles.boxes data)
  · simpa only [equality] using FlatProfileAverages.average_section data families (UniversalFiniteProfiles.boxes data)
  · simpa only [equality] using FlatProfileInterpolation.test_integrable data families (UniversalFiniteProfiles.boxes data)

theorem test_integrable {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value})
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    Integrable (VectorGodement.integrand data (test (flat.1 parameter) cutoff) parameter point) BinaryHaar.measure := by
  obtain ⟨_, _, _, _, _, integrable⟩ := exists_recovery flat cutoff smooth compact supported
  exact integrable parameter point halfPlane

def sectionLinear {degree : ℕ} (data : InducingData degree)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value})
    (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    flatSpace data →ₗ[ℂ] (AdelicGL → ℂ) where
  toFun := fun function => VectorGodement.sectionFunction data (test (function.property.1 parameter) cutoff) parameter
  map_add' := by
    intro first second
    have firstFlat : IsFlatSection data first.val := first.property
    have secondFlat : IsFlatSection data second.val := second.property
    funext point
    change VectorGodement.sectionFunction data (test (induced_add (firstFlat.1 parameter)
      (secondFlat.1 parameter)) cutoff) parameter point = _
    rw [test_add (firstFlat.1 parameter) (secondFlat.1 parameter)]
    simp only [VectorGodement.sectionFunction, VectorGodement.integrand, Pi.add_apply, map_add, mul_add]
    have integralEquality := integral_add
      (test_integrable firstFlat cutoff smooth compact supported parameter point halfPlane)
      (test_integrable secondFlat cutoff smooth compact supported parameter point halfPlane)
    exact (congrArg (fun scalar : ℂ =>
      GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) * scalar)
      integralEquality).trans (mul_add _ _ _)
  map_smul' := by
    intro coefficient function
    have flat : IsFlatSection data function.val := function.property
    funext point
    change VectorGodement.sectionFunction data
      (test (induced_smul (flat.1 parameter) coefficient) cutoff) parameter point = _
    rw [test_smul (flat.1 parameter) coefficient]
    exact GodementSums.section_smul data coefficient _ parameter point

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LinearProfileRecovery
