module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.ScalarSeries
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFourierOperator

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationBanach

def orbitSpace : Submodule ℂ (lp (fun _ : BinaryAdelicGL => ℂ) ⊤) where
  carrier := {function | ∀ point : BinaryAdelicGL,
    Continuous (fun parameter : Parameter => function (point * atInfinity (rotation parameter)))}
  zero_mem' := fun _ => continuous_const
  add_mem' := by
    intro _ _ firstContinuous secondContinuous point
    exact (firstContinuous point).add (secondContinuous point)
  smul_mem' := by
    intro scalar _ continuity point
    exact (continuity point).const_smul scalar

theorem orbitSpace_isClosed : IsClosed (orbitSpace : Set (lp (fun _ : BinaryAdelicGL => ℂ) ⊤)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro sequence function membership convergence point
  have uniform : TendstoUniformly
      (fun index : ℕ => fun parameter : Parameter => sequence index (point * atInfinity (rotation parameter)))
      (fun parameter : Parameter => function (point * atInfinity (rotation parameter))) Filter.atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon positiveEpsilon
    filter_upwards [Metric.tendsto_nhds.mp convergence epsilon positiveEpsilon] with index estimate
    intro parameter
    have bound := lp.norm_apply_le_norm (by simp : (⊤ : ENNReal) ≠ 0)
      (function - sequence index) (point * atInfinity (rotation parameter))
    change ‖function (point * atInfinity (rotation parameter)) -
      sequence index (point * atInfinity (rotation parameter))‖ ≤ ‖function - sequence index‖ at bound
    rw [dist_eq_norm]
    exact bound.trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using estimate)
  exact uniform.continuous (Filter.Eventually.of_forall (fun index => membership index point)).frequently

noncomputable instance orbitSpace_complete : CompleteSpace orbitSpace := by
  let _ : IsClosed (orbitSpace : Set (lp (fun _ : BinaryAdelicGL => ℂ) ⊤)) := orbitSpace_isClosed
  exact IsClosed.completeSpace_coe

noncomputable def orbitMap (point : BinaryAdelicGL) : orbitSpace →L[ℂ] C(Parameter, ℂ) :=
  let linear : orbitSpace →ₗ[ℂ] C(Parameter, ℂ) :=
    { toFun := fun function => ⟨fun parameter => function.val (point * atInfinity (rotation parameter)), function.property point⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  linear.mkContinuous 1 (fun function => by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro parameter
    exact (lp.norm_apply_le_norm (by simp) function.val _).trans_eq (one_mul _).symm)

noncomputable def coefficient (point : BinaryAdelicGL) (index : ℤ) : orbitSpace →L[ℂ] ℂ :=
  (coefficientOperator index).comp (orbitMap point)

theorem coefficient_apply (point : BinaryAdelicGL) (index : ℤ) (function : orbitSpace) :
    coefficient point index function = fourierCoeff (fun parameter : Parameter =>
      function.val (point * atInfinity (rotation parameter))) index := rfl

theorem eq_zero_of_coefficients (function : orbitSpace)
    (coefficients : ∀ point : BinaryAdelicGL, ∀ index : ℤ, coefficient point index function = 0) : function = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext point
  change function.val point = 0
  have zeroOrbit := FourierUniqueness.scalar_eq_zero (orbitMap point function) (coefficients point)
  have atZero := congrArg (fun orbit : C(Parameter, ℂ) => orbit 0) zeroOrbit
  change function.val (point * atInfinity (rotation 0)) = 0 at atZero
  simpa only [rotation_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, mul_one] using atZero

theorem continuous_of_coefficients {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source]
    [CompleteSpace Source] (linear : Source →ₗ[ℂ] orbitSpace)
    (continuity : ∀ point : BinaryAdelicGL, ∀ index : ℤ,
      Continuous (fun vector : Source => coefficient point index (linear vector))) : Continuous linear := by
  apply linear.continuous_of_isClosed_graph
  have graphEquality : (linear.graph : Set (Source × orbitSpace)) =
      ⋂ point : BinaryAdelicGL, ⋂ index : ℤ,
        {pair : Source × orbitSpace | coefficient point index pair.2 = coefficient point index (linear pair.1)} := by
    ext pair
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro equality point index
      exact congrArg (coefficient point index) equality
    · intro equality
      apply sub_eq_zero.mp
      apply eq_zero_of_coefficients
      intro point index
      rw [map_sub, equality, sub_self]
  rw [graphEquality]
  apply isClosed_iInter
  intro point
  apply isClosed_iInter
  intro index
  exact isClosed_eq ((coefficient point index).continuous.comp continuous_snd)
    ((continuity point index).comp continuous_fst)

noncomputable def realization (data : CuspidalRepresentation) : data.smooth →ₗ[ℂ] orbitSpace :=
  (boundedRealization data).codRestrict orbitSpace (fun vector point => scalarOrbit_continuous data point vector)

theorem coefficient_realization (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (index : ℤ) (vector : data.smooth) :
    coefficient point index (realization data vector) =
      data.realize (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier.smoothMode data index vector) point :=
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationKernel.scalarCoefficient_eq_mode data point index vector

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationBanach
