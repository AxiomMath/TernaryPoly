module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArchimedeanAveraging
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArchimedeanAveraging
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealCompactProjection

def fixedSubspace (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL) : Submodule ℂ data.H where
  carrier := {vector | ∀ matrix : group, data.π (atInfinity matrix.val) vector = vector}
  zero_mem' := fun _ => map_zero _
  add_mem' {first second} firstFixed secondFixed matrix := by rw [map_add, firstFixed matrix, secondFixed matrix]
  smul_mem' scalar vector vectorFixed matrix := by rw [map_smul, vectorFixed matrix]

theorem fixedSubspace_isClosed (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL) :
    IsClosed (fixedSubspace data group : Set data.H) := by
  change IsClosed {vector | ∀ matrix : group, data.π (atInfinity matrix.val) vector = vector}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun matrix =>
    isClosed_eq (unitaryOperator data (atInfinity matrix.val)).continuous continuous_id)

instance fixedSubspace_complete (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL) :
    CompleteSpace (fixedSubspace data group) :=
  (fixedSubspace_isClosed data group).isComplete.completeSpace_coe

noncomputable def averagingOperator (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL) :
    data.H →L[ℂ] data.H := (fixedSubspace data group).starProjection

theorem averagingOperator_norm_le (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL) :
    ‖averagingOperator data group‖ ≤ 1 := (fixedSubspace data group).starProjection_norm_le

theorem exists_probability_leftInvariantMeasure (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) [MeasurableSpace group] [BorelSpace group] :
    ∃ measure : Measure group, IsProbabilityMeasure measure ∧ measure.IsMulLeftInvariant := by
  have : CompactSpace group := isCompact_iff_compactSpace.mp compactness
  let measure : Measure group := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts group)
  refine ⟨measure, ⟨?_⟩, inferInstance⟩
  exact Measure.haarMeasure_self

theorem orbit_integrable (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) [MeasurableSpace group] [BorelSpace group]
    (measure : Measure group) [IsFiniteMeasure measure] (vector : data.H) :
    Integrable (fun matrix : group => data.π (atInfinity matrix.val) vector) measure := by
  have weighted : Integrable (fun matrix : group => (1 : ℂ) • data.π (atInfinity matrix.val) vector) measure :=
    weighted_orbit_integrable data vector compactness measure (fun _ => (1 : ℂ)) continuous_const
  simpa only [one_smul] using weighted

theorem integral_fixed (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) [MeasurableSpace group] [BorelSpace group]
    (measure : Measure group) [IsFiniteMeasure measure] [measure.IsMulLeftInvariant] (vector : data.H) :
    (∫ matrix : group, data.π (atInfinity matrix.val) vector ∂measure) ∈ fixedSubspace data group := by
  intro fixedMatrix
  have integrability := orbit_integrable data group compactness measure vector
  have mappedIntegral := (unitaryOperator data (atInfinity fixedMatrix.val)).integral_comp_comm integrability
  have functionEquality :
      (fun matrix : group => unitaryOperator data (atInfinity fixedMatrix.val)
        (data.π (atInfinity matrix.val) vector)) =
      (fun matrix : group => data.π (atInfinity (fixedMatrix * matrix).val) vector) := by
    funext matrix
    change data.π (atInfinity fixedMatrix.val) (data.π (atInfinity matrix.val) vector) =
      data.π (atInfinity (fixedMatrix.val * matrix.val)) vector
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul, Module.End.mul_apply]
  calc
    _ = ∫ matrix : group, unitaryOperator data (atInfinity fixedMatrix.val)
        (data.π (atInfinity matrix.val) vector) ∂measure := mappedIntegral.symm
    _ = ∫ matrix : group, data.π (atInfinity (fixedMatrix * matrix).val) vector ∂measure :=
      congrArg (fun function : group → data.H => ∫ matrix, function matrix ∂measure) functionEquality
    _ = _ := integral_mul_left_eq_self (fun matrix : group => data.π (atInfinity matrix.val) vector) fixedMatrix

theorem integral_inner_fixed (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) [MeasurableSpace group] [BorelSpace group]
    (measure : Measure group) [IsProbabilityMeasure measure] (vector target : data.H)
    (targetFixed : target ∈ fixedSubspace data group) :
    inner ℂ target (∫ matrix : group, data.π (atInfinity matrix.val) vector ∂measure) = inner ℂ target vector := by
  have innerEquality (matrix : group) : inner ℂ target (data.π (atInfinity matrix.val) vector) =
      inner ℂ target vector := by
    let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π (atInfinity matrix.val), data.unitary (atInfinity matrix.val)⟩
    have preservation := isometry.inner_map_map target vector
    change inner ℂ (data.π (atInfinity matrix.val) target) (data.π (atInfinity matrix.val) vector) = _ at preservation
    rwa [targetFixed matrix] at preservation
  rw [← integral_inner (orbit_integrable data group compactness measure vector) target]
  simp only [innerEquality]
  simp

theorem averagingOperator_eq_integral (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) [MeasurableSpace group] [BorelSpace group]
    (measure : Measure group) [IsProbabilityMeasure measure] [measure.IsMulLeftInvariant] (vector : data.H) :
    averagingOperator data group vector = ∫ matrix : group, data.π (atInfinity matrix.val) vector ∂measure := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (integral_fixed data group compactness measure vector)
  intro target targetFixed
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right, integral_inner_fixed data group compactness measure vector target targetFixed, sub_self]

theorem averagingOperator_preserves_fixedSmooth (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    averagingOperator data group vector.val ∈ data.smooth ∧
      averagingOperator data group vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level := by
  let _ : MeasurableSpace group := borel group
  have : BorelSpace group := ⟨rfl⟩
  obtain ⟨measure, probability, leftInvariance⟩ := exists_probability_leftInvariantMeasure group compactness
  have : IsProbabilityMeasure measure := probability
  have : measure.IsMulLeftInvariant := leftInvariance
  rw [averagingOperator_eq_integral data group compactness measure]
  have weighted :
      (∫ matrix : group, (1 : ℂ) • data.π (atInfinity matrix.val) vector.val ∂measure) ∈ data.smooth ∧
      (∫ matrix : group, (1 : ℂ) • data.π (atInfinity matrix.val) vector.val ∂measure) ∈
        TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level :=
    weighted_integral_mem data level openness compactLevel vector fixed compactness
      measure (fun _ => (1 : ℂ)) continuous_const
  simpa only [one_smul] using weighted

theorem averagingOperator_mem_smooth (data : CuspidalRepresentation) (group : Subgroup BinaryRealGL)
    (compactness : IsCompact (group : Set BinaryRealGL)) (vector : data.smooth) :
    averagingOperator data group vector.val ∈ data.smooth := by
  obtain ⟨level, openness, compactLevel, fixed⟩ := ((data.smooth_exact vector.val).mp vector.property).2
  exact (averagingOperator_preserves_fixedSmooth data group compactness level openness compactLevel vector fixed).1

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealCompactProjection
