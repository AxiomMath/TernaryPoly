module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CuspidalHilbert
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging

theorem atFinite_one {size : ℕ} :
    atFinite (1 : Matrix.GeneralLinearGroup (Fin size) FiniteAdeles) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  by_cases equality : row = column <;>
    simp [atFinite, combineGL, pairMatrix, equality]

noncomputable def finiteInclusion : BinaryFiniteGL →* BinaryAdelicGL where
  toFun := atFinite
  map_one' := atFinite_one
  map_mul' := TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_mul

theorem action_mul (data : CuspidalRepresentation) (first second : BinaryFiniteGL) (vector : data.H) :
    data.π (atFinite (first * second)) vector =
      data.π (atFinite first) (data.π (atFinite second) vector) := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_mul, map_mul, Module.End.mul_apply]

theorem action_inv_cancel (data : CuspidalRepresentation) (matrix : BinaryFiniteGL) (vector : data.H) :
    data.π (atFinite matrix) (data.π (atFinite matrix⁻¹) vector) = vector := by
  rw [← action_mul, mul_inv_cancel, atFinite_one, map_one, Module.End.one_apply]

theorem action_injective (data : CuspidalRepresentation) (matrix : BinaryFiniteGL) :
    Function.Injective (data.π (atFinite matrix)) := by
  let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π (atFinite matrix), data.unitary (atFinite matrix)⟩
  exact isometry.injective

theorem smooth_orbit_locallyConstant (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (vector : data.smooth) :
    IsLocallyConstant (fun element : level => data.π (atFinite element.val) vector.val) := by
  obtain ⟨_, stabilizer, openness, _, fixed⟩ := (data.smooth_exact vector.val).mp vector.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro element
  refine ⟨{other : level | element.val⁻¹ * other.val ∈ stabilizer},
    openness.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
  · change element.val⁻¹ * element.val ∈ stabilizer
    rw [inv_mul_cancel]
    exact stabilizer.one_mem
  · intro other membership
    have fixedDifference := fixed ⟨element.val⁻¹ * other.val, membership⟩
    have product := action_mul data element.val (element.val⁻¹ * other.val) vector.val
    rw [mul_inv_cancel_left, fixedDifference] at product
    exact product

theorem smooth_orbit_finite (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) :
    (Set.range (fun element : level => data.π (atFinite element.val) vector.val)).Finite := by
  let : CompactSpace level := isCompact_iff_compactSpace.mp compactness
  exact (smooth_orbit_locallyConstant data level vector).range_finite

noncomputable def orbitFinset (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) : Finset data.H :=
  (smooth_orbit_finite data level compactness vector).toFinset

theorem mem_orbitFinset (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (value : data.H) :
    value ∈ orbitFinset data level compactness vector ↔
      ∃ element : level, data.π (atFinite element.val) vector.val = value := by
  simp only [orbitFinset, Set.Finite.mem_toFinset, Set.mem_range]

theorem orbitFinset_nonempty (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) : (orbitFinset data level compactness vector).Nonempty := by
  refine ⟨vector.val, (mem_orbitFinset data level compactness vector vector.val).mpr ⟨1, ?_⟩⟩
  change data.π (atFinite 1) vector.val = vector.val
  rw [atFinite_one, map_one, Module.End.one_apply]

theorem orbitFinset_stable (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (element : level) (value : data.H)
    (membership : value ∈ orbitFinset data level compactness vector) :
    data.π (atFinite element.val) value ∈ orbitFinset data level compactness vector := by
  obtain ⟨other, rfl⟩ := (mem_orbitFinset data level compactness vector value).mp membership
  apply (mem_orbitFinset data level compactness vector _).mpr
  exact ⟨element * other, action_mul data element.val other.val vector.val⟩

theorem orbitFinset_sum_fixed (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (element : level) :
    data.π (atFinite element.val) (∑ value ∈ orbitFinset data level compactness vector, value) =
      ∑ value ∈ orbitFinset data level compactness vector, value := by
  classical
  rw [map_sum]
  apply Finset.sum_bij (fun value _ => data.π (atFinite element.val) value)
  · exact orbitFinset_stable data level compactness vector element
  · intro first _ second _ equality
    exact action_injective data element.val equality
  · intro value membership
    refine ⟨data.π (atFinite element.val⁻¹) value, ?_, action_inv_cancel data element.val value⟩
    exact orbitFinset_stable data level compactness vector element⁻¹ value membership
  · intro _ _
    rfl

noncomputable def orbitAverage (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) : data.H :=
  ((orbitFinset data level compactness vector).card : ℂ)⁻¹ •
    ∑ value ∈ orbitFinset data level compactness vector, value

theorem orbitAverage_smooth (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) : orbitAverage data level compactness vector ∈ data.smooth := by
  apply data.smooth.smul_mem
  apply data.smooth.sum_mem
  intro value membership
  obtain ⟨element, rfl⟩ := (mem_orbitFinset data level compactness vector value).mp membership
  exact data.smooth_stable _ _ vector.property

theorem orbitAverage_fixed (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) : orbitAverage data level compactness vector ∈ fixedSubspace data level := by
  intro element
  dsimp only [orbitAverage]
  rw [map_smul, orbitFinset_sum_fixed]

theorem orbitAverage_distance_le (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (target : data.H) (targetFixed : target ∈ fixedSubspace data level) :
    ‖orbitAverage data level compactness vector - target‖ ≤ ‖vector.val - target‖ := by
  let orbit := orbitFinset data level compactness vector
  have positiveCard : 0 < orbit.card := Finset.card_pos.mpr
    (orbitFinset_nonempty data level compactness vector)
  have complexCardNonzero : (orbit.card : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positiveCard)
  have realCardNonzero : (orbit.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positiveCard)
  have subtract : orbitAverage data level compactness vector - target =
      (orbit.card : ℂ)⁻¹ • ∑ value ∈ orbit, (value - target) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ complexCardNonzero]
    rfl
  have distanceEquality (value : data.H) (membership : value ∈ orbit) :
      ‖value - target‖ = ‖vector.val - target‖ := by
    obtain ⟨element, rfl⟩ := (mem_orbitFinset data level compactness vector value).mp membership
    simpa only [map_sub, targetFixed element] using
      data.unitary (atFinite element.val) (vector.val - target)
  rw [subtract, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    (orbit.card : ℝ)⁻¹ * ‖∑ value ∈ orbit, (value - target)‖ ≤
        (orbit.card : ℝ)⁻¹ * ∑ value ∈ orbit, ‖value - target‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (orbit.card : ℝ)⁻¹ * ((orbit.card : ℝ) * ‖vector.val - target‖) := by
      congr 1
      calc
        ∑ value ∈ orbit, ‖value - target‖ = ∑ _value ∈ orbit, ‖vector.val - target‖ :=
          Finset.sum_congr rfl distanceEquality
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ‖vector.val - target‖ := by rw [← mul_assoc, inv_mul_cancel₀ realCardNonzero, one_mul]

theorem exists_smooth_fixed_approximation {degree : ℕ} (data : InducingData degree)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (target : data.cusp.H) (targetFixed : target ∈ fixedSubspace data.cusp level)
    (epsilon : ℝ) (positiveEpsilon : 0 < epsilon) :
    ∃ vector : data.cusp.H, vector ∈ data.cusp.smooth ∧ vector ∈ fixedSubspace data.cusp level ∧
      ‖vector - target‖ < epsilon := by
  obtain ⟨vector, smoothVector, approximation⟩ :=
    Metric.mem_closure_iff.mp (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert.smooth_dense data target) epsilon positiveEpsilon
  have normApproximation : ‖vector - target‖ < epsilon := by
    simpa only [dist_eq_norm, norm_sub_rev] using approximation
  refine ⟨orbitAverage data.cusp level compactness ⟨vector, smoothVector⟩,
    orbitAverage_smooth data.cusp level compactness _, orbitAverage_fixed data.cusp level compactness _, ?_⟩
  exact (orbitAverage_distance_le data.cusp level compactness
    ⟨vector, smoothVector⟩ target targetFixed).trans_lt normApproximation

theorem smooth_fixed_closure {degree : ℕ} (data : InducingData degree)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL)) :
    (data.cusp.smooth ⊓ fixedSubspace data.cusp level).topologicalClosure =
      fixedSubspace data.cusp level := by
  apply le_antisymm
  · exact (data.cusp.smooth ⊓ fixedSubspace data.cusp level).topologicalClosure_minimal
      inf_le_right (fixedSubspace_isClosed data.cusp level)
  · intro target targetFixed
    apply Metric.mem_closure_iff.mpr
    intro epsilon positiveEpsilon
    obtain ⟨vector, smoothVector, fixedVector, approximation⟩ :=
      exists_smooth_fixed_approximation data level compactness target targetFixed epsilon positiveEpsilon
    exact ⟨vector, ⟨smoothVector, fixedVector⟩, by simpa only [dist_eq_norm, norm_sub_rev] using approximation⟩

theorem orbitAverage_inner (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (target : data.H) (targetFixed : target ∈ fixedSubspace data level) :
    inner ℂ target (orbitAverage data level compactness vector) = inner ℂ target vector.val := by
  let orbit := orbitFinset data level compactness vector
  have cardNonzero : (orbit.card : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr (orbitFinset_nonempty data level compactness vector)))
  have innerEquality (value : data.H) (membership : value ∈ orbit) :
      inner ℂ target value = inner ℂ target vector.val := by
    obtain ⟨element, rfl⟩ := (mem_orbitFinset data level compactness vector value).mp membership
    let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π (atFinite element.val), data.unitary (atFinite element.val)⟩
    have preservation := isometry.inner_map_map target vector.val
    change inner ℂ (data.π (atFinite element.val) target)
      (data.π (atFinite element.val) vector.val) = _ at preservation
    rwa [targetFixed element] at preservation
  change inner ℂ target ((orbit.card : ℂ)⁻¹ • ∑ value ∈ orbit, value) = _
  rw [inner_smul_right, inner_sum]
  have sumEquality : ∑ value ∈ orbit, inner ℂ target value =
      (orbit.card : ℂ) * inner ℂ target vector.val := by
    calc
      ∑ value ∈ orbit, inner ℂ target value = ∑ _value ∈ orbit, inner ℂ target vector.val :=
        Finset.sum_congr rfl innerEquality
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [sumEquality, inv_mul_cancel_left₀ cardNonzero]

instance fixedSubspace_complete (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    CompleteSpace (fixedSubspace data level) :=
  (fixedSubspace_isClosed data level).isComplete.completeSpace_coe

noncomputable def averagingOperator (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    data.H →L[ℂ] data.H := (fixedSubspace data level).starProjection

theorem averagingOperator_eq_orbitAverage (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) :
    averagingOperator data level vector.val = orbitAverage data level compactness vector := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (orbitAverage_fixed data level compactness vector)
  intro target targetFixed
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right, orbitAverage_inner data level compactness vector target targetFixed, sub_self]

theorem averagingOperator_norm_le (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    ‖averagingOperator data level‖ ≤ 1 := (fixedSubspace data level).starProjection_norm_le

theorem averagingOperator_mem_fixedSubspace (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (vector : data.H) :
    averagingOperator data level vector ∈ fixedSubspace data level :=
  ((fixedSubspace data level).orthogonalProjectionOnto vector).property

theorem averagingOperator_of_fixed (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (vector : data.H) (fixed : vector ∈ fixedSubspace data level) :
    averagingOperator data level vector = vector := Submodule.starProjection_eq_self_iff.mpr fixed

theorem averagingOperator_smooth (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) : averagingOperator data level vector.val ∈ data.smooth := by
  rw [averagingOperator_eq_orbitAverage data level compactness vector]
  exact orbitAverage_smooth data level compactness vector

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging
