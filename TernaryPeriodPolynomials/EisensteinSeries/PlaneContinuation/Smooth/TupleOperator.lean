module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth.RecoveryEntries
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.FiniteAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothTupleOperator

abbrev Space {degree : ℕ} (data : InducingData degree) := UniversalFiniteProfiles.Key data → data.cusp.smooth

def projectedRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) : Space data →ₗ[ℂ] data.cusp.smooth :=
  ∑ key : UniversalFiniteProfiles.Key data,
    (SmoothRecoveryEntries.operator data parameter halfPlane point key).comp (LinearMap.proj key)

def averagedRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) : Space data →ₗ[ℂ] data.cusp.smooth :=
  (Fintype.card (levelImage data) : ℂ)⁻¹ •
    ∑ residue : levelImage data, FiniteProfileResidues.character data (representative data residue) •
      projectedRow data parameter halfPlane (point * representative data residue)

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) : Space data →ₗ[ℂ] Space data :=
  LinearMap.pi (fun key => averagedRow data parameter halfPlane (UniversalFiniteProfiles.representative data key))

theorem projectedRow_apply {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) :
    projectedRow data parameter halfPlane point value =
      ∑ key, SmoothRecoveryEntries.operator data parameter halfPlane point key (value key) := by
  simp only [projectedRow, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem projectedRow_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) :
    (projectedRow data parameter halfPlane point value).val =
      TupleRecoveryOperator.projectedRow data parameter halfPlane point (fun key => (value key).val) := by
  rw [projectedRow_apply, TupleRecoveryOperator.projectedRow, ContinuousLinearMap.comp_apply, TupleRecoveryOperator.row_apply]
  simp only [Submodule.coe_sum, SmoothRecoveryEntries.operator_val, map_sum]
  rfl

theorem averagedRow_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) :
    (averagedRow data parameter halfPlane point value).val =
      TupleRecoveryOperator.averagedRow data parameter halfPlane point (fun key => (value key).val) := by
  simp only [averagedRow, TupleRecoveryOperator.averagedRow, LinearMap.smul_apply, LinearMap.sum_apply,
    _root_.smul_apply, _root_.sum_apply, Submodule.coe_smul, Submodule.coe_sum, projectedRow_val]

theorem operator_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : Space data) :
    (fun key => (operator data parameter halfPlane value key).val) =
      TupleRecoveryOperator.operator data parameter halfPlane (fun key => (value key).val) := by
  funext key
  exact averagedRow_val data parameter halfPlane (UniversalFiniteProfiles.representative data key) value

def realAction {degree : ℕ} (data : InducingData degree) (matrix : BinaryRealGL) : Space data →ₗ[ℂ] Space data :=
  LinearMap.pi (fun key => (DirectionalRealization.smoothTranslate data.cusp matrix).comp (LinearMap.proj key))

theorem projectedRow_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (matrix : BinaryRealGL) (value : Space data) :
    projectedRow data parameter halfPlane point (realAction data matrix value) =
      DirectionalRealization.smoothTranslate data.cusp matrix (projectedRow data parameter halfPlane point value) := by
  simp only [projectedRow_apply, realAction, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    SmoothRecoveryEntries.operator_real, map_sum]

theorem averagedRow_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (matrix : BinaryRealGL) (value : Space data) :
    averagedRow data parameter halfPlane point (realAction data matrix value) =
      DirectionalRealization.smoothTranslate data.cusp matrix (averagedRow data parameter halfPlane point value) := by
  simp only [averagedRow, LinearMap.smul_apply, LinearMap.sum_apply, projectedRow_real, map_smul, map_sum]

theorem operator_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (matrix : BinaryRealGL) (value : Space data) :
    operator data parameter halfPlane (realAction data matrix value) =
      realAction data matrix (operator data parameter halfPlane value) := by
  funext key
  exact averagedRow_real data parameter halfPlane (UniversalFiniteProfiles.representative data key) matrix value

theorem vectors_contDiffOn {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) :
    ContDiffOn ℝ ⊤ (fun frame : Rectangular ℝ => tuple induced frame)
      {frame : Rectangular ℝ | FullRank frame} :=
  contDiffOn_pi.mpr (fun key => RealProfileRegularity.profile_contDiffOn induced
    (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)))

theorem averagedRow_contDiffOn {degree : ℕ} {data : InducingData degree} {parameter reference : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) :
    ContDiffOn ℝ ⊤ (fun frame : Rectangular ℝ =>
      (averagedRow data reference halfPlane point (vectors induced frame)).val)
        {frame : Rectangular ℝ | FullRank frame} := by
  simp only [averagedRow_val]
  exact ((TupleRecoveryOperator.averagedRow data reference halfPlane point).restrictScalars ℝ).contDiff.comp_contDiffOn
    (vectors_contDiffOn induced)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothTupleOperator
