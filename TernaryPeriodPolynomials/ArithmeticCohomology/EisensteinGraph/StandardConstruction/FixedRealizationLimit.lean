module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarRealization

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FixedRealizationLimit

theorem average_distance_le (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (target : lp (fun _ : BinaryAdelicGL => ℂ) ⊤)
    (fixed : ∀ element : level, ∀ point,
      target (point * atFinite element.val) = target point) :
    ‖boundedRealization data (smoothAverage data level compactness vector) - target‖ ≤
      ‖boundedRealization data vector - target‖ := by
  classical
  let orbit := orbitFinset data level compactness vector
  have cardPositive : 0 < orbit.card := Finset.card_pos.mpr (orbitFinset_nonempty data level compactness vector)
  have cardComplex : (orbit.card : ℂ) ≠ 0 := by exact_mod_cast cardPositive.ne'
  have cardReal : (orbit.card : ℝ) ≠ 0 := by exact_mod_cast cardPositive.ne'
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro point
  have pointBound (value : {value // value ∈ orbit}) :
      ‖data.realize (smoothOrbitElement data level compactness vector value) point - target point‖ ≤
        ‖boundedRealization data vector - target‖ := by
    obtain ⟨element, equality⟩ := (mem_orbitFinset data level compactness vector value.val).mp value.property
    have vectorEquality : smoothOrbitElement data level compactness vector value =
        (⟨data.π (atFinite element.val) vector.val,
          data.smooth_stable _ _ vector.property⟩ : data.smooth) := Subtype.ext equality.symm
    rw [vectorEquality, data.equivariant, ← fixed element point]
    exact lp.norm_apply_le_norm (by simp) (boundedRealization data vector - target) _
  have subtract : data.realize (smoothAverage data level compactness vector) point - target point =
      (orbit.card : ℂ)⁻¹ • ∑ value ∈ orbit.attach,
        (data.realize (smoothOrbitElement data level compactness vector value) point - target point) := by
    rw [smoothAverage_eq_sum, map_smul, map_sum]
    simp only [Pi.smul_apply, Finset.sum_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_attach, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ cardComplex]
  change ‖data.realize (smoothAverage data level compactness vector) point - target point‖ ≤ _
  rw [subtract, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (orbit.card : ℝ)⁻¹ * ∑ value ∈ orbit.attach,
        ‖data.realize (smoothOrbitElement data level compactness vector value) point - target point‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (orbit.card : ℝ)⁻¹ * ((orbit.card : ℝ) * ‖boundedRealization data vector - target‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      calc
        _ ≤ ∑ _value ∈ orbit.attach, ‖boundedRealization data vector - target‖ :=
          Finset.sum_le_sum (fun value _ => pointBound value)
        _ = _ := by rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    _ = _ := by rw [inv_mul_cancel_left₀ cardReal]

theorem fixed_limit_unique {I : Type} (filter : Filter I) [filter.NeBot]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (FiniteRotationTypes.fixedMode data level index))
    (family : I → fixedSmooth data level) (vector : fixedSmooth data level)
    (target : lp (fun _ : BinaryAdelicGL => ℂ) ⊤)
    (hilbertLimit : Tendsto (fun index => (family index).val.val) filter (𝓝 vector.val.val))
    (scalarLimit : Tendsto (fun index => boundedRealization data (family index).val) filter (𝓝 target)) :
    target = boundedRealization data vector.val := by
  have orbitMember : target ∈ RotationBanach.orbitSpace :=
    RotationBanach.orbitSpace_isClosed.mem_of_tendsto scalarLimit
      (Filter.Eventually.of_forall (fun index => (RotationBanach.realization data (family index).val).property))
  let orbitTarget : RotationBanach.orbitSpace := ⟨target, orbitMember⟩
  have orbitLimit : Tendsto (fun index => RotationBanach.realization data (family index).val)
      filter (𝓝 orbitTarget) := tendsto_subtype_rng.mpr scalarLimit
  have fixedLimit : Tendsto family filter (𝓝 vector) :=
    tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr hilbertLimit)
  have equality : orbitTarget = RotationBanach.realization data vector.val := by
    apply sub_eq_zero.mp
    apply RotationBanach.eq_zero_of_coefficients
    intro point index
    rw [map_sub, sub_eq_zero]
    let _ : FiniteDimensional ℂ (FiniteRotationTypes.fixedMode data level index) := finiteTypes index
    have modeContinuous := FiniteRotationTypes.scalar_mode_continuous data level openness compactness
      index (fun value : fixedSmooth data level => value)
      (continuous_subtype_val.comp continuous_subtype_val) point
    have modeLimit := modeContinuous.continuousAt.tendsto.comp fixedLimit
    have coefficientLimit := (RotationBanach.coefficient point index).continuous.continuousAt.tendsto.comp orbitLimit
    simp only [Function.comp_def, RotationBanach.coefficient_realization] at coefficientLimit modeLimit ⊢
    exact tendsto_nhds_unique coefficientLimit modeLimit
  exact congrArg Subtype.val equality

theorem limit_unique {I : Type} (filter : Filter I) [filter.NeBot]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (FiniteRotationTypes.fixedMode data level index))
    (family : I → data.smooth) (vector : data.smooth)
    (vectorFixed : vector.val ∈ fixedSubspace data level)
    (target : lp (fun _ : BinaryAdelicGL => ℂ) ⊤)
    (targetFixed : ∀ element : level, ∀ point, target (point * atFinite element.val) = target point)
    (hilbertLimit : Tendsto (fun index => (family index).val) filter (𝓝 vector.val))
    (scalarLimit : Tendsto (fun index => boundedRealization data (family index)) filter (𝓝 target)) :
    target = boundedRealization data vector := by
  let averaged : I → fixedSmooth data level := fun index =>
    ⟨smoothAverage data level compactness (family index), averagingOperator_mem_fixedSubspace data level _⟩
  let fixedVector : fixedSmooth data level := ⟨vector, vectorFixed⟩
  have averagedHilbert : Tendsto (fun index => (averaged index).val.val) filter (𝓝 fixedVector.val.val) := by
    have limit := (averagingOperator data level).continuous.continuousAt.tendsto.comp hilbertLimit
    rw [averagingOperator_of_fixed data level vector.val vectorFixed] at limit
    exact limit
  have averagedScalar : Tendsto (fun index => boundedRealization data (averaged index).val)
      filter (𝓝 target) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_iff_norm_sub_tendsto_zero.mp scalarLimit) (fun _ => norm_nonneg _)
      (fun index => average_distance_le data level compactness (family index) target targetFixed)
  exact fixed_limit_unique filter data level openness compactness finiteTypes averaged fixedVector target
    averagedHilbert averagedScalar

theorem principal_limit_unique {I : Type} (filter : Filter I) [filter.NeBot]
    {degree : ℕ} (data : InducingData degree)
    (family : I → data.cusp.smooth) (vector : data.cusp.smooth)
    (vectorFixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (target : lp (fun _ : BinaryAdelicGL => ℂ) ⊤)
    (targetFixed : ∀ element : finiteCongruence, ∀ point,
      target (point * atFinite element.val) = target point)
    (hilbertLimit : Tendsto (fun index => (family index).val) filter (𝓝 vector.val))
    (scalarLimit : Tendsto (fun index => boundedRealization data.cusp (family index)) filter (𝓝 target)) :
    target = boundedRealization data.cusp vector :=
  limit_unique filter data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
    (EndpointAdmissibility.all_finiteDimensional data) family vector vectorFixed target targetFixed
    hilbertLimit scalarLimit

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FixedRealizationLimit
