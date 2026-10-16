module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.NormMeasurable
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.LocalBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Topology

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspFunctionContinuity

theorem real_projection_continuous :
    Continuous (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (n := Fin 2)) := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    continuous_fst.comp ((continuous_apply column).comp (continuous_apply row))))

theorem finite_projection_continuous :
    Continuous (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (n := Fin 2)) := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    continuous_snd.comp ((continuous_apply column).comp (continuous_apply row))))

theorem finite_fixed (data : CuspidalRepresentation) (vector : data.smooth) (finite : BinaryFiniteGL)
    (fixed : data.π (atFinite finite) vector.val = vector.val) (point : BinaryAdelicGL) :
    data.realize vector (point * atFinite finite) = data.realize vector point := by
  have vectorEquality : (⟨data.π (atFinite finite) vector.val,
      data.smooth_stable (atFinite finite) vector.val vector.property⟩ : data.smooth) = vector :=
    Subtype.ext fixed
  rw [← data.equivariant, vectorEquality]

theorem continuous (data : CuspidalRepresentation) (vector : data.smooth) : Continuous (data.realize vector) := by
  obtain ⟨level, levelOpen, _, fixed⟩ := ((data.smooth_exact vector.val).mp vector.property).2
  apply continuous_iff_continuousAt.mpr
  intro point
  let finite := GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) point
  let localFunction := fun value : BinaryAdelicGL => data.realize vector
    (atFinite finite * atInfinity (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) value))
  have localContinuous : Continuous localFunction :=
    (ScalarLocalBounds.smooth_continuous (data.scalarSmooth vector (atFinite finite))).comp
      (continuous_pi (fun _ : Fin 1 => real_projection_continuous))
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  have near : {value : BinaryAdelicGL | finite⁻¹ * GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) value ∈ level} ∈ nhds point := by
    apply (levelOpen.preimage (continuous_const.mul finite_projection_continuous)).mem_nhds
    change finite⁻¹ * finite ∈ level
    rw [inv_mul_cancel]
    exact level.one_mem
  filter_upwards [near] with value membership
  let difference := finite⁻¹ * GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) value
  have factorization : value =
      (atFinite finite * atInfinity (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) value)) * atFinite difference := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, mul_assoc, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_mul]
    dsimp only [difference]
    rw [mul_inv_cancel_left]
    exact CasimirIrreducibility.binaryAdelic_decomposition value
  calc
    data.realize vector value = data.realize vector
        ((atFinite finite * atInfinity (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) value)) * atFinite difference) :=
      congrArg (data.realize vector) factorization
    _ = localFunction value := finite_fixed data vector difference (fixed ⟨difference, membership⟩) _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspFunctionContinuity
