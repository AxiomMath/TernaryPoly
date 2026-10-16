module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteLadderClosure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLowering_norm_le_raising (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (nonnegative : 0 ≤ weight) (vector : cuspAffineSmoothValues cusp)
    (member : vector ∈ cuspFiniteWeightValues cusp level weight) :
    ‖(cuspLoweringOperator cusp weight vector).val‖ ≤ ‖(cuspRaisingOperator cusp weight vector).val‖ := by
  have identity := cuspLadder_norm_identity cusp weight vector member.2
  have weight_nonnegative : (0 : ℝ) ≤ weight := by exact_mod_cast nonnegative
  have product_nonnegative := mul_nonneg weight_nonnegative (sq_nonneg ‖vector.val‖)
  nlinarith [norm_nonneg (cuspLoweringOperator cusp weight vector).val,
    norm_nonneg (cuspRaisingOperator cusp weight vector).val]

theorem cuspRaising_graph_approximation (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (nonnegative : 0 ≤ weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    ∃ (sequence : ℕ → cuspAffineSmoothValues cusp) (lower_limit : cusp.H),
      (∀ index, sequence index ∈ cuspFiniteWeightValues cusp level weight) ∧
      Tendsto (fun index => (sequence index).val) atTop (nhds vector.val) ∧
      Tendsto (fun index => (cuspRaisingOperator cusp weight (sequence index)).val) atTop
        (nhds ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)) ∧
      Tendsto (fun index => (cuspLoweringOperator cusp weight (sequence index)).val) atTop (nhds lower_limit) := by
  have closable := cuspFiniteRaisingPMap_isClosable cusp spherical level weight
  have member : (vector.val, ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)) ∈
      closure ((cuspFiniteRaisingPMap cusp level weight).graph : Set (cusp.H × cusp.H)) := by
    change _ ∈ (cuspFiniteRaisingPMap cusp level weight).graph.topologicalClosure
    rw [closable.graph_closure_eq_closure_graph]
    exact (cuspFiniteRaisingPMap cusp level weight).closure.mem_graph vector
  obtain ⟨pairs, pairs_mem, pairs_limit⟩ := mem_closure_iff_seq_limit.mp member
  choose original first second using fun index => (cuspFiniteRaisingPMap cusp level weight).mem_graph_iff.mp (pairs_mem index)
  let sequence : ℕ → cuspAffineSmoothValues cusp := fun index => ⟨(original index).val, (original index).property.2⟩
  have sequence_mem (index : ℕ) : sequence index ∈ cuspFiniteWeightValues cusp level weight := (original index).property.1
  have first_eq : (fun index => (sequence index).val) = fun index => (pairs index).1 := funext first
  have second_eq : (fun index => (cuspRaisingOperator cusp weight (sequence index)).val) =
      fun index => (pairs index).2 := funext second
  have first_limit : Tendsto (fun index => (sequence index).val) atTop (nhds vector.val) := by
    rw [first_eq]
    exact (continuous_fst.tendsto _).comp pairs_limit
  have second_limit : Tendsto (fun index => (cuspRaisingOperator cusp weight (sequence index)).val) atTop
      (nhds ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)) := by
    rw [second_eq]
    exact (continuous_snd.tendsto _).comp pairs_limit
  have lower_cauchy : CauchySeq (fun index => (cuspLoweringOperator cusp weight (sequence index)).val) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon positive
    obtain ⟨bound, bound_property⟩ := Metric.cauchySeq_iff.mp second_limit.cauchySeq epsilon positive
    refine ⟨bound, fun first first_large second second_large => ?_⟩
    have norm_bound := cuspLowering_norm_le_raising cusp level weight nonnegative (sequence first - sequence second)
      (Submodule.sub_mem _ (sequence_mem first) (sequence_mem second))
    simp only [map_sub, Submodule.coe_sub] at norm_bound
    rw [dist_eq_norm]
    exact lt_of_le_of_lt norm_bound (by
      simpa only [dist_eq_norm] using bound_property first first_large second second_large)
  obtain ⟨lower_limit, lower_tendsto⟩ := cauchySeq_tendsto_of_complete lower_cauchy
  exact ⟨sequence, lower_limit, sequence_mem, first_limit, second_limit, lower_tendsto⟩

theorem cuspAffineDifferential_horizontal_ladders (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cuspAffineSmoothValues cusp) :
    cuspAffineDifferential cusp 1 vector = (1 / 2 : ℂ) •
      (cuspRaisingOperator cusp weight vector + cuspLoweringOperator cusp weight vector -
        (Complex.I * (weight : ℂ)) • vector) := by
  simp only [cuspRaisingOperator, cuspLoweringOperator, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  module

theorem cuspAffineDifferential_vertical_ladders (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cuspAffineSmoothValues cusp) :
    cuspAffineDifferential cusp Complex.I vector = (-Complex.I / 2) •
      (cuspRaisingOperator cusp weight vector - cuspLoweringOperator cusp weight vector) := by
  calc
    _ = -(Complex.I ^ 2) • cuspAffineDifferential cusp Complex.I vector := by simp
    _ = _ := by
      simp only [cuspRaisingOperator, cuspLoweringOperator, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply]
      module

def realCoordinateCLM {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (first second : E) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight first + Complex.imCLM.smulRight second

theorem realCoordinateCLM_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (derivative : ℂ →L[ℝ] E) : realCoordinateCLM (derivative 1) (derivative Complex.I) = derivative := by
  ext direction
  exact (realLinear_complex_coordinates derivative.toLinearMap direction).symm

theorem realCoordinateCLM_continuous {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (fun pair : E × E => realCoordinateCLM pair.1 pair.2) := by
  exact (((ContinuousLinearMap.smulRightL ℝ ℂ E) Complex.reCLM).continuous.comp continuous_fst).add
    (((ContinuousLinearMap.smulRightL ℝ ℂ E) Complex.imCLM).continuous.comp continuous_snd)

theorem cuspRaising_graph_approximation_fderiv (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (nonnegative : 0 ≤ weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    ∃ (sequence : ℕ → cuspAffineSmoothValues cusp) (derivative : ℂ →L[ℝ] cusp.H),
      (∀ index, sequence index ∈ cuspFiniteWeightValues cusp level weight) ∧
      Tendsto (fun index => (sequence index).val) atTop (nhds vector.val) ∧
      Tendsto (fun index => fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I)
        atTop (nhds derivative) ∧
      derivative 1 + Complex.I • derivative Complex.I + (Complex.I * (weight : ℂ) / 2) • vector.val =
        ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H) := by
  obtain ⟨sequence, lower_limit, members, first_limit, raising_limit, lowering_limit⟩ :=
    cuspRaising_graph_approximation cusp spherical level weight nonnegative vector
  let raised := ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)
  let horizontal := (1 / 2 : ℂ) • (raised + lower_limit - (Complex.I * (weight : ℂ)) • vector.val)
  let vertical := (-Complex.I / 2) • (raised - lower_limit)
  have horizontal_limit : Tendsto (fun index => (cuspAffineDifferential cusp 1 (sequence index)).val)
      atTop (nhds horizontal) := by
    have identity (index : ℕ) := congrArg Subtype.val (cuspAffineDifferential_horizontal_ladders cusp weight (sequence index))
    simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub] at identity
    simp_rw [identity]
    exact ((raising_limit.add lowering_limit).sub (first_limit.const_smul _)).const_smul _
  have vertical_limit : Tendsto (fun index => (cuspAffineDifferential cusp Complex.I (sequence index)).val)
      atTop (nhds vertical) := by
    have identity (index : ℕ) := congrArg Subtype.val (cuspAffineDifferential_vertical_ladders cusp weight (sequence index))
    simp only [Submodule.coe_smul, Submodule.coe_sub] at identity
    simp_rw [identity]
    exact (raising_limit.sub lowering_limit).const_smul _
  have derivative_limit := (realCoordinateCLM_continuous.tendsto (horizontal, vertical)).comp
    (horizontal_limit.prodMk_nhds vertical_limit)
  refine ⟨sequence, realCoordinateCLM horizontal vertical, members, first_limit, ?_, ?_⟩
  · simpa only [Function.comp_def, cuspAffineDifferential_apply, realCoordinateCLM_fderiv] using derivative_limit
  · simp only [realCoordinateCLM, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      one_smul, zero_smul, add_zero, zero_add]
    change horizontal + Complex.I • vertical + (Complex.I * (weight : ℂ) / 2) • vector.val = raised
    dsimp only [horizontal, vertical]
    rw [smul_smul]
    have scalar : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]
    rw [scalar]
    module

end TernaryPeriodPolynomials.SphericalDetection.Helpers
