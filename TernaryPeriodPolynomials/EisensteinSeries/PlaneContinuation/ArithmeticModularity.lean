module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ModularTransformation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ModularFiniteDimension
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArithmeticModularity

noncomputable def arithmeticGroup : Subgroup BinaryRealGL :=
  (CongruenceSubgroup.Gamma 3).map (SpecialLinearGroup.mapGL ℝ)

instance arithmeticGroup_detOne : arithmeticGroup.HasDetOne := by
  unfold arithmeticGroup
  infer_instance

instance arithmeticGroup_finiteIndex :
    arithmeticGroup.IsFiniteRelIndex (SpecialLinearGroup.mapGL ℝ (R := ℤ)).range := by
  constructor
  rw [arithmeticGroup, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero

theorem integral_congruence (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (membership : matrix ∈ CongruenceSubgroup.Gamma 3) :
    SpecialLinearGroup.mapGL IntegralAdeles matrix ∈ integralCongruence := by
  change GeneralLinearGroup.map integralReduction (SpecialLinearGroup.mapGL IntegralAdeles matrix) = 1
  have reduction := CongruenceSubgroup.Gamma_mem'.mp membership
  apply Units.ext
  apply Matrix.ext
  intro row column
  have entry := congrArg (fun value : SpecialLinearGroup (Fin 2) (ZMod 3) => value.val row column) reduction
  simpa using entry

theorem rational_decomposition (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ matrix) =
      atInfinity (SpecialLinearGroup.mapGL ℝ matrix) *
        atFinite (GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles matrix)) := by
  rw [← Norm.combineGL_eq_mul]
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · change (matrix.val row column : ℝ) = (matrix.val row column : ℝ)
    rfl
  · simp [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
      combineGL, pairMatrix]

theorem conjugate_congruence (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (membership : matrix ∈ CongruenceSubgroup.Gamma 3) (point : IntegralBinaryGL) :
    point⁻¹ * (SpecialLinearGroup.mapGL IntegralAdeles matrix)⁻¹ * point ∈ integralCongruence := by
  change GeneralLinearGroup.map integralReduction _ = 1
  have reduction : GeneralLinearGroup.map integralReduction (SpecialLinearGroup.mapGL IntegralAdeles matrix) = 1 :=
    integral_congruence matrix membership
  simp [map_mul, map_inv, reduction]

theorem realize_right_fixed (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (element : BinaryFiniteGL) (membership : element ∈ finiteCongruence) (point : BinaryAdelicGL) :
    data.realize vector (point * atFinite element) = data.realize vector point := by
  have equality : (⟨data.π (atFinite element) vector.val,
      data.smooth_stable _ _ vector.property⟩ : data.smooth) = vector :=
    Subtype.ext (fixed ⟨element, membership⟩)
  rw [← data.equivariant, equality]

theorem arithmetic_factorization (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) :
    atFinite (GeneralLinearGroup.map integralEmbedding point) *
        atInfinity (SpecialLinearGroup.mapGL ℝ matrix) * atInfinity realPoint =
      GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ matrix) *
        ((atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) *
          atFinite (GeneralLinearGroup.map integralEmbedding
            (point⁻¹ * (SpecialLinearGroup.mapGL IntegralAdeles matrix)⁻¹ * point))) := by
  let finiteMatrix := GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles matrix)
  let finitePoint := GeneralLinearGroup.map integralEmbedding point
  let correction := GeneralLinearGroup.map integralEmbedding
    (point⁻¹ * (SpecialLinearGroup.mapGL IntegralAdeles matrix)⁻¹ * point)
  have cancellation : finiteMatrix * finitePoint * correction = finitePoint := by
    simp only [finiteMatrix, finitePoint, correction, map_mul, map_inv]
    group
  have adelicCancellation : atFinite finiteMatrix * atFinite finitePoint * atFinite correction =
      atFinite finitePoint := by
    rw [← atFinite_mul, ← atFinite_mul, cancellation]
  rw [rational_decomposition]
  change atFinite finitePoint * atInfinity (SpecialLinearGroup.mapGL ℝ matrix) * atInfinity realPoint =
    (atInfinity (SpecialLinearGroup.mapGL ℝ matrix) * atFinite finiteMatrix) *
      ((atFinite finitePoint * atInfinity realPoint) * atFinite correction)
  rw [atFinite_atInfinity_commute finitePoint (SpecialLinearGroup.mapGL ℝ matrix),
    mul_assoc (atFinite finitePoint) (atInfinity realPoint) (atFinite correction),
    ← atFinite_atInfinity_commute correction realPoint]
  calc
    _ = atInfinity (SpecialLinearGroup.mapGL ℝ matrix) *
        (atFinite finiteMatrix * atFinite finitePoint * atFinite correction) * atInfinity realPoint := by
      rw [adelicCancellation]
    _ = _ := by group

theorem realize_arithmetic (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (membership : matrix ∈ CongruenceSubgroup.Gamma 3)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) :
    data.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding point) *
      atInfinity (SpecialLinearGroup.mapGL ℝ matrix) * atInfinity realPoint) =
        data.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) := by
  rw [arithmetic_factorization, data.leftRational]
  exact realize_right_fixed data vector fixed _
    ⟨_, conjugate_congruence matrix membership point, rfl⟩ _

theorem realization_arithmetic (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (weight : ℤ) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (membership : matrix ∈ CongruenceSubgroup.Gamma 3) (point : IntegralBinaryGL) :
    HolomorphicRealization.realization data weight vector
        (atFinite (GeneralLinearGroup.map integralEmbedding point) *
          atInfinity (SpecialLinearGroup.mapGL ℝ matrix)) =
      HolomorphicRealization.realization data weight vector
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) := by
  funext argument
  change HighestWeightHolomorphic.function _ _ _ _ _ = HighestWeightHolomorphic.function _ _ _ _ _
  simp only [HighestWeightHolomorphic.function,
    UpperTriangularChart.raw_eq data _ vector argument argument.im_pos]
  rw [realize_arithmetic data vector fixed matrix membership point]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArithmeticModularity
