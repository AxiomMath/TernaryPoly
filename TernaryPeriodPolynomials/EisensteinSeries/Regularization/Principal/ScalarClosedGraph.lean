module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.WeightDimension
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.BoundedAdelicFourier

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspPrincipalRotationCoefficient
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (argument : BinaryAdelicGL) (weight : ℤ) :
    cuspFiniteFixedSubmodule cusp binaryPrincipalLevel →L[ℂ] ℂ := by
  let estimate := cohomological_principal_weight_scalar_bound cohomological weight
  let constant := estimate.choose
  have nonnegative := estimate.choose_spec.1
  have bounded := estimate.choose_spec.2
  let coefficient := (cuspScalarRotationCoefficient cusp argument weight).comp
    (cuspFiniteFixedSubmodule cusp binaryPrincipalLevel).subtype
  refine coefficient.mkContinuous constant ?_
  intro vector
  let projected : cuspPrincipalWeightSubmodule cusp weight :=
    ⟨cuspSmoothRotationProjection cusp weight vector.val, (fun binary =>
      cuspRotationProjection_finite_fixed cusp weight vector.val.val binary.val (vector.property binary)),
      cuspSmoothRotationProjection_eigenvector cusp weight vector.val⟩
  change ‖fourierCoeff (cuspScalarCircleOrbit cusp argument vector.val) weight‖ ≤ constant * ‖vector‖
  rw [← cusp_realize_rotation_projection]
  exact (cusp_realize_norm_le cusp projected.val argument).trans
    ((bounded projected).trans (mul_le_mul_of_nonneg_left
      (cuspRotationFourier_norm_le cusp weight vector.val.val) nonnegative))

theorem cuspPrincipalRotationCoefficient_apply
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (argument : BinaryAdelicGL) (weight : ℤ) (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) :
    cuspPrincipalRotationCoefficient cohomological argument weight vector =
      boundedAdelicFourierCoefficient argument weight (cuspBoundedRealization cusp vector.val) := rfl

noncomputable def cuspPrincipalRealization (cusp : CuspidalRepresentation) :
    cuspFiniteFixedSubmodule cusp binaryPrincipalLevel →ₗ[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ :=
  (cuspBoundedRealization cusp).comp (cuspFiniteFixedSubmodule cusp binaryPrincipalLevel).subtype

theorem cuspPrincipalRealization_graph_eq
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ((cuspPrincipalRealization cusp).graph : Set
      (cuspFiniteFixedSubmodule cusp binaryPrincipalLevel × BoundedContinuousFunction BinaryAdelicGL ℂ)) =
      ⋂ argument, ⋂ weight, {pair | boundedAdelicFourierCoefficient argument weight pair.2 =
        cuspPrincipalRotationCoefficient cohomological argument weight pair.1} := by
  ext pair
  change pair ∈ (cuspPrincipalRealization cusp).graph ↔ _
  simp only [LinearMap.mem_graph_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro equality argument weight
    rw [equality, cuspPrincipalRotationCoefficient_apply]
    rfl
  · intro coefficients
    apply sub_eq_zero.mp
    apply boundedAdelicFourierCoefficient_zero
    intro argument weight
    rw [map_sub, coefficients, cuspPrincipalRotationCoefficient_apply]
    exact sub_self _

theorem cuspPrincipalRealization_graph_isClosed
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree) :
    IsClosed ((cuspPrincipalRealization cusp).graph : Set
      (cuspFiniteFixedSubmodule cusp binaryPrincipalLevel × BoundedContinuousFunction BinaryAdelicGL ℂ)) := by
  rw [cuspPrincipalRealization_graph_eq cohomological]
  apply isClosed_iInter
  intro argument
  apply isClosed_iInter
  intro weight
  exact isClosed_eq ((boundedAdelicFourierCoefficient argument weight).continuous.comp continuous_snd)
    ((cuspPrincipalRotationCoefficient cohomological argument weight).continuous.comp continuous_fst)

theorem cuspPrincipalRealization_limit_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (vectors : ℕ → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (function : BoundedContinuousFunction BinaryAdelicGL ℂ)
    (hilbert_limit : Tendsto (fun index => (vectors index).val.val) atTop (nhds 0))
    (scalar_limit : Tendsto (fun index => cuspBoundedRealization cusp (vectors index).val) atTop (nhds function)) :
    function = 0 := by
  have vector_limit : Tendsto vectors atTop (nhds 0) :=
    tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr hilbert_limit)
  have graph_limit := vector_limit.prodMk_nhds scalar_limit
  have member := (cuspPrincipalRealization_graph_isClosed cohomological).mem_of_tendsto graph_limit
    (Eventually.of_forall (fun index =>
      (LinearMap.mem_graph_iff (cuspPrincipalRealization cusp) _).mpr rfl))
  have equality := (LinearMap.mem_graph_iff (cuspPrincipalRealization cusp) _).mp member
  simpa only [map_zero] using equality

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
