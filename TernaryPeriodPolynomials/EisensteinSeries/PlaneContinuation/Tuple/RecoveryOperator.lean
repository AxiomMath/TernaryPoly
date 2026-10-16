module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PrimitiveTupleKernel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryOperator

def row {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) : Space data →L[ℂ] data.cusp.H :=
  ∑ key : UniversalFiniteProfiles.Key data,
    (RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
      ⟨point, rfl⟩ key).comp (ContinuousLinearMap.proj key)

def primitiveRow {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) : Space data →L[ℂ] data.cusp.H :=
  ∑ key : UniversalFiniteProfiles.Key data,
    (RecoveryOperatorLimit.primitiveOperator data reference halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
      ⟨point, rfl⟩ key).comp (ContinuousLinearMap.proj key)

theorem row_apply {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (value : Space data) :
    row data parameter halfPlane point value = ∑ key : UniversalFiniteProfiles.Key data,
      RecoveryCoefficients.operator data parameter halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
        ⟨point, rfl⟩ key (value key) := by
  simp only [row, _root_.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem primitiveRow_apply {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) (value : Space data) :
    primitiveRow data reference halfPlane point value = ∑ key : UniversalFiniteProfiles.Key data,
      RecoveryOperatorLimit.primitiveOperator data reference halfPlane (atFinite (GeneralLinearGroup.map integralEmbedding point))
        ⟨point, rfl⟩ key (value key) := by
  simp only [primitiveRow, _root_.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

def projectedRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) : Space data →L[ℂ] data.cusp.H :=
  (CompactAveraging.averagingOperator data.cusp finiteCongruence).comp (row data parameter halfPlane point)

def primitiveProjectedRow {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) : Space data →L[ℂ] data.cusp.H :=
  (CompactAveraging.averagingOperator data.cusp finiteCongruence).comp (primitiveRow data reference halfPlane point)

def averagedRow {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) : Space data →L[ℂ] data.cusp.H :=
  (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹ •
    ∑ residue : FiniteSectionProjection.levelImage data,
      FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue) •
        projectedRow data parameter halfPlane (point * FiniteSectionProjection.representative data residue)

def primitiveAveragedRow {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) : Space data →L[ℂ] data.cusp.H :=
  (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹ •
    ∑ residue : FiniteSectionProjection.levelImage data,
      FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue) •
        primitiveProjectedRow data reference halfPlane (point * FiniteSectionProjection.representative data residue)

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) : Space data →L[ℂ] Space data :=
  ContinuousLinearMap.pi (fun key => averagedRow data parameter halfPlane (UniversalFiniteProfiles.representative data key))

def primitiveOperator {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) : Space data →L[ℂ] Space data :=
  ContinuousLinearMap.pi (fun key => primitiveAveragedRow data reference halfPlane (UniversalFiniteProfiles.representative data key))

theorem row_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) :
    Tendsto (fun index : ℕ => row data (reference + index) (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index) point)
      atTop (nhds (primitiveRow data reference halfPlane point)) := by
  apply tendsto_finsetSum Finset.univ
  intro key _
  exact (((ContinuousLinearMap.compL ℂ (Space data) data.cusp.H data.cusp.H).flip
    (ContinuousLinearMap.proj key)).continuous.tendsto _).comp
      (RecoveryOperatorLimit.operator_tendsto data reference halfPlane _ ⟨point, rfl⟩ key)

theorem projectedRow_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) :
    Tendsto (fun index : ℕ => projectedRow data (reference + index)
      (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index) point) atTop
        (nhds (primitiveProjectedRow data reference halfPlane point)) :=
  (((ContinuousLinearMap.compL ℂ (Space data) data.cusp.H data.cusp.H)
    (CompactAveraging.averagingOperator data.cusp finiteCongruence)).continuous.tendsto _).comp
      (row_tendsto data reference halfPlane point)

theorem averagedRow_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) :
    Tendsto (fun index : ℕ => averagedRow data (reference + index)
      (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index) point) atTop
        (nhds (primitiveAveragedRow data reference halfPlane point)) := by
  apply Filter.Tendsto.const_smul
  apply tendsto_finsetSum Finset.univ
  intro residue _
  exact (projectedRow_tendsto data reference halfPlane (point * FiniteSectionProjection.representative data residue)).const_smul _

theorem operator_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) :
    Tendsto (fun index : ℕ => operator data (reference + index)
      (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index)) atTop
        (nhds (primitiveOperator data reference halfPlane)) := by
  exact ((ContinuousLinearMap.piEquivL ℂ (Space data) (fun _ : UniversalFiniteProfiles.Key data => data.cusp.H)).continuous.tendsto _).comp
    (tendsto_pi_nhds.mpr (fun key => averagedRow_tendsto data reference halfPlane (UniversalFiniteProfiles.representative data key)))

theorem operator_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : Space data) :
    operator data parameter halfPlane value ∈ ProfileTuples.fixed data := by
  intro key
  change averagedRow data parameter halfPlane (UniversalFiniteProfiles.representative data key) value ∈ _
  simp only [averagedRow, _root_.smul_apply, _root_.sum_apply]
  apply (fixedSubspace data.cusp finiteCongruence).smul_mem
  apply (fixedSubspace data.cusp finiteCongruence).sum_mem
  intro residue _
  apply (fixedSubspace data.cusp finiteCongruence).smul_mem
  exact CompactAveraging.averagingOperator_mem_fixedSubspace data.cusp finiteCongruence _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryOperator
