module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart3
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteLadderClosure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionLadders
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakKernels
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightWeakKernels
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RaisingGraphApproximation

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part4

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryWeakOrbit`, `SphericalDetection.BinaryFiniteLadderClosure`,
`SphericalDetection.BinaryLadderDecomposition`, `SphericalDetection.BinaryReflectionLadders`,
`SphericalDetection.BinaryWeakKernels`, `SphericalDetection.BinaryWeightWeakKernels`,
`SphericalDetection.BinaryRaisingGraphApproximation`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryWeakOrbit

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspWeakRaisingKernel_holomorphic (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp (2 * halfWeight)
      test.val) vector = 0) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet := by
  apply differentiableOn_of_inner_dense (cusp.smooth : Set cusp.H) (levelThreeCusp_smooth_dense
    cusp spherical)
    _ _ UpperHalfPlane.isOpen_upperHalfPlaneSet (cuspWeightedAffineOrbit_continuousOn cusp
      halfWeight vector)
  intro test member
  exact cuspScalarWeightedAffineOrbit_holomorphic_of_tests cusp halfWeight vector annihilates
    ⟨test, member⟩

theorem cuspWeakRaisingKernel_analytic (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp (2 * halfWeight)
      test.val) vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  cuspAffineOrbitVector_analytic_of_weighted_holomorphic cusp halfWeight vector
    (cuspWeakRaisingKernel_holomorphic cusp spherical halfWeight vector annihilates)

end CloneBinaryWeakOrbit

section CloneBinaryFiniteLadderClosure

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspFiniteRaisingPMap_isClosable (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) :
    (cuspFiniteRaisingPMap cusp level weight).IsClosable :=
  (cuspRaisingPMap_isClosable cusp spherical weight).leIsClosable LinearPMap.domRestrict_le

theorem cuspFiniteRaisingPMap_closure_range_isClosed (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight) :
    IsClosed ((cuspFiniteRaisingPMap cusp level weight).closure.toFun.range : Set cusp.H) :=
  closableLinearPMap_closure_range_isClosed (cuspFiniteRaisingPMap cusp level weight)
    (cuspFiniteRaisingPMap_isClosable cusp spherical level weight) 1
    (fun vector => by simpa using cuspFiniteRaisingPMap_bound cusp level weight positive vector)

theorem cuspFiniteRaisingPMap_closure_weights (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    vector.val ∈ cuspHilbertWeightValues cusp level weight ∧
      ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H) ∈ cuspHilbertWeightValues
        cusp level (weight + 2) := by
  apply closableLinearPMap_closure_constraints (cuspFiniteRaisingPMap cusp level weight)
    (cuspFiniteRaisingPMap_isClosable cusp spherical level weight)
    (cuspHilbertWeightValues cusp level weight) (cuspHilbertWeightValues cusp level (weight + 2))
    (cuspHilbertWeightValues_isClosed cusp level weight) (cuspHilbertWeightValues_isClosed cusp
      level (weight + 2))
    (fun _ member => member.1) _ vector
  intro value
  exact cuspFiniteWeightValues_raising cusp level weight ⟨value.val, value.property.2⟩
    value.property.1

end CloneBinaryFiniteLadderClosure

section CloneBinaryLadderDecomposition

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspFiniteRaising_decomposition (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight)
    (vector : cusp.H) (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2)) :
    ∃ (preimage : (cuspFiniteRaisingPMap cusp level weight).closure.domain) (remainder : cusp.H),
      preimage.val ∈ cuspHilbertWeightValues cusp level weight ∧
      remainder ∈ cuspHilbertWeightValues cusp level (weight + 2) ∧
      remainder ∈ (cuspFiniteRaisingPMap cusp level weight).closure.toFun.rangeᗮ ∧
      vector = ((cuspFiniteRaisingPMap cusp level weight).closure preimage : cusp.H) + remainder ∧
      ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
        inner ℂ remainder (cuspRaisingOperator cusp weight smooth).val = 0 := by
  let range := (cuspFiniteRaisingPMap cusp level weight).closure.toFun.range
  let : CompleteSpace range := (cuspFiniteRaisingPMap_closure_range_isClosed cusp spherical level
    weight positive).completeSpace_coe
  obtain ⟨image, image_mem, orthogonal⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K
    := range) vector
  obtain ⟨preimage, image_eq⟩ := image_mem
  change ((cuspFiniteRaisingPMap cusp level weight).closure preimage : cusp.H) = image at image_eq
  have weights := cuspFiniteRaisingPMap_closure_weights cusp spherical level weight preimage
  have image_weight : image ∈ cuspHilbertWeightValues cusp level (weight + 2) := image_eq ▸
    weights.2
  refine ⟨preimage, vector - image, weights.1, Submodule.sub_mem _ member image_weight, orthogonal,
    ?_, ?_⟩
  · rw [image_eq]
    abel
  · intro smooth smooth_mem
    exact (Submodule.mem_orthogonal' range (vector - image)).mp orthogonal _
      (cuspFiniteRaisingPMap_mem_closure_range cusp level weight smooth smooth_mem)

theorem cuspFiniteRaising_exists_weak_kernel_of_not_mem (cusp : CuspidalRepresentation) (spherical
    : LevelThreeCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight)
    (vector : cusp.H) (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2))
    (outside : vector ∉ (cuspFiniteRaisingPMap cusp level weight).closure.toFun.range) :
    ∃ remainder : cusp.H, remainder ≠ 0 ∧ remainder ∈ cuspHilbertWeightValues cusp level (weight +
      2) ∧
      ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
        inner ℂ remainder (cuspRaisingOperator cusp weight smooth).val = 0 := by
  obtain ⟨preimage, remainder, _, remainder_mem, _, decomposition, annihilates⟩ :=
    cuspFiniteRaising_decomposition cusp spherical level weight positive vector member
  refine ⟨remainder, ?_, remainder_mem, annihilates⟩
  intro zero
  rw [zero, add_zero] at decomposition
  apply outside
  exact ⟨preimage, decomposition.symm⟩

end CloneBinaryLadderDecomposition

section CloneBinaryReflectionLadders

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

theorem cusp_exists_levelThree_smooth_of_lowering_zero (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (halfWeight : ℤ) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ (2 * halfWeight) • vector)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (lowering_zero : cuspLoweringVector cusp (2 * halfWeight) vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * (-halfWeight)) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp (-halfWeight) spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  have reflected_nonzero : cusp.π (atInfinity UpperHalfPlane.J) vector ≠ 0 := by
    exact (map_ne_zero_iff (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J))
      (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J)).injective).mpr nonzero
  have reflected_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) (cusp.π (atInfinity UpperHalfPlane.J) vector) =
        (angle : ℂ) ^ (2 * (-halfWeight)) • cusp.π (atInfinity UpperHalfPlane.J) vector := by
    simpa only [mul_neg] using cuspReflection_rotation cusp (2 * halfWeight) vector rotation
  have reflected_regular := cuspAffineOrbitVector_reflection_contDiffOn cusp vector regular
  have reflected_zero : cuspRaisingVector cusp (2 * (-halfWeight)) (cusp.π (atInfinity
    UpperHalfPlane.J) vector) = 0 := by
    rw [mul_neg, cuspRaisingVector_reflection cusp (2 * halfWeight) vector
      ((regular.differentiableOn (by simp)).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp))),
          lowering_zero, map_zero, neg_zero]
  exact cusp_exists_levelThree_smooth_raising_zero cusp spherical central_positive
    (cusp.π (atInfinity UpperHalfPlane.J) vector) (-halfWeight) reflected_nonzero
    reflected_rotation reflected_regular reflected_zero

end CloneBinaryReflectionLadders

section CloneBinaryWeakKernels

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspWeakLoweringKernel_analytic (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val)
      vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have reflected := cuspWeakRaisingKernel_analytic cusp spherical (-halfWeight)
    (cusp.π (atInfinity UpperHalfPlane.J) vector) (cuspWeakLoweringKernel_reflection cusp
      halfWeight vector annihilates)
  have reflected_regular : ContDiffOn ℝ ⊤
      (cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector))
        UpperHalfPlane.upperHalfPlaneSet :=
    reflected.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  have regular := cuspAffineOrbitVector_reflection_contDiffOn cusp _ reflected_regular
  rw [cuspReflection_involution] at regular
  intro point positive
  exact (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive)).analyticAt

theorem cuspWeakLoweringKernel_lowering_zero_of_smooth_tests (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val)
      vector = 0) :
    cuspLoweringVector cusp (2 * halfWeight) vector = 0 := by
  have analytic := cuspWeakLoweringKernel_analytic cusp spherical halfWeight vector annihilates
  have regular : vector ∈ cuspAffineSmoothValues cusp :=
    analytic.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  apply (levelThreeCusp_smooth_dense cusp spherical).eq_zero_of_inner_right ℂ
  intro test member
  have skew := cuspRaisingOperator_skew cusp (2 * halfWeight)
    ⟨test, cuspSmooth_le_affineSmooth cusp member⟩ ⟨vector, regular⟩
  change inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test) vector +
    inner ℂ test (cuspLoweringVector cusp (2 * halfWeight) vector) = 0 at skew
  rw [annihilates ⟨test, member⟩, zero_add] at skew
  exact skew

theorem cuspWeakLoweringKernel_exists_levelThree (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.H) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ (2 * halfWeight) • vector)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val)
      vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * (-halfWeight)) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp (-halfWeight) spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  exact cusp_exists_levelThree_smooth_of_lowering_zero cusp spherical central_positive vector
    halfWeight nonzero rotation
    ((cuspWeakLoweringKernel_analytic cusp spherical halfWeight vector annihilates).contDiffOn
      UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn)
    (cuspWeakLoweringKernel_lowering_zero_of_smooth_tests cusp spherical halfWeight vector
      annihilates)

end CloneBinaryWeakKernels

section CloneBinaryWeightWeakKernels

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspWeightWeakLoweringKernel_exists_levelThree (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL)) (weight halfWeight : ℤ)
    (weight_eq : weight + 2 = 2 * halfWeight) (vector : cusp.H) (nonzero : vector ≠ 0)
    (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2))
    (annihilates : ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp
      level weight →
      inner ℂ vector (cuspRaisingOperator cusp weight smooth).val = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * (-halfWeight)) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp (-halfWeight) spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  apply cuspWeakLoweringKernel_exists_levelThree cusp spherical central_positive halfWeight vector
    nonzero
  · simpa only [weight_eq] using member.2
  · simpa only [weight_eq] using
      cuspWeightFiniteLevel_raising_tests cusp level level_open level_compact weight vector member
        annihilates

end CloneBinaryWeightWeakKernels

section CloneBinaryRaisingGraphApproximation

open GeneralEisenstein GeneralEisenstein.Adelic

open Filter

theorem cuspRaising_graph_approximation (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (nonnegative : 0 ≤ weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    ∃ (sequence : ℕ → cuspAffineSmoothValues cusp) (lower_limit : cusp.H),
      (∀ index, sequence index ∈ cuspFiniteWeightValues cusp level weight) ∧
      Tendsto (fun index => (sequence index).val) atTop (nhds vector.val) ∧
      Tendsto (fun index => (cuspRaisingOperator cusp weight (sequence index)).val) atTop
        (nhds ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)) ∧
      Tendsto (fun index => (cuspLoweringOperator cusp weight (sequence index)).val) atTop (nhds
        lower_limit) := by
  have closable := cuspFiniteRaisingPMap_isClosable cusp spherical level weight
  have member : (vector.val, ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)) ∈
      closure ((cuspFiniteRaisingPMap cusp level weight).graph : Set (cusp.H × cusp.H)) := by
    change _ ∈ (cuspFiniteRaisingPMap cusp level weight).graph.topologicalClosure
    rw [closable.graph_closure_eq_closure_graph]
    exact (cuspFiniteRaisingPMap cusp level weight).closure.mem_graph vector
  obtain ⟨pairs, pairs_mem, pairs_limit⟩ := mem_closure_iff_seq_limit.mp member
  choose original first second using fun index => (cuspFiniteRaisingPMap cusp level
    weight).mem_graph_iff.mp (pairs_mem index)
  let sequence : ℕ → cuspAffineSmoothValues cusp := fun index => ⟨(original index).val, (original
    index).property.2⟩
  have sequence_mem (index : ℕ) : sequence index ∈ cuspFiniteWeightValues cusp level weight :=
    (original index).property.1
  have first_eq : (fun index => (sequence index).val) = fun index => (pairs index).1 := funext first
  have second_eq : (fun index => (cuspRaisingOperator cusp weight (sequence index)).val) =
      fun index => (pairs index).2 := funext second
  have first_limit : Tendsto (fun index => (sequence index).val) atTop (nhds vector.val) := by
    rw [first_eq]
    exact (continuous_fst.tendsto _).comp pairs_limit
  have second_limit : Tendsto (fun index => (cuspRaisingOperator cusp weight (sequence index)).val)
    atTop
      (nhds ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)) := by
    rw [second_eq]
    exact (continuous_snd.tendsto _).comp pairs_limit
  have lower_cauchy : CauchySeq (fun index => (cuspLoweringOperator cusp weight (sequence
    index)).val) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon positive
    obtain ⟨bound, bound_property⟩ := Metric.cauchySeq_iff.mp second_limit.cauchySeq epsilon
      positive
    refine ⟨bound, fun first first_large second second_large => ?_⟩
    have norm_bound := cuspLowering_norm_le_raising cusp level weight nonnegative (sequence first -
      sequence second)
      (Submodule.sub_mem _ (sequence_mem first) (sequence_mem second))
    simp only [map_sub, Submodule.coe_sub] at norm_bound
    rw [dist_eq_norm]
    exact lt_of_le_of_lt norm_bound (by
      simpa only [dist_eq_norm] using bound_property first first_large second second_large)
  obtain ⟨lower_limit, lower_tendsto⟩ := cauchySeq_tendsto_of_complete lower_cauchy
  exact ⟨sequence, lower_limit, sequence_mem, first_limit, second_limit, lower_tendsto⟩

theorem cuspRaising_graph_approximation_fderiv (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (nonnegative : 0 ≤ weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    ∃ (sequence : ℕ → cuspAffineSmoothValues cusp) (derivative : ℂ →L[ℝ] cusp.H),
      (∀ index, sequence index ∈ cuspFiniteWeightValues cusp level weight) ∧
      Tendsto (fun index => (sequence index).val) atTop (nhds vector.val) ∧
      Tendsto (fun index => fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I)
        atTop (nhds derivative) ∧
      derivative 1 + Complex.I • derivative Complex.I + (Complex.I * (weight : ℂ) / 2) • vector.val
        =
        ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H) := by
  obtain ⟨sequence, lower_limit, members, first_limit, raising_limit, lowering_limit⟩ :=
    cuspRaising_graph_approximation cusp spherical level weight nonnegative vector
  let raised := ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)
  let horizontal := (1 / 2 : ℂ) • (raised + lower_limit - (Complex.I * (weight : ℂ)) • vector.val)
  let vertical := (-Complex.I / 2) • (raised - lower_limit)
  have horizontal_limit : Tendsto (fun index => (cuspAffineDifferential cusp 1 (sequence
    index)).val)
      atTop (nhds horizontal) := by
    have identity (index : ℕ) := congrArg Subtype.val (cuspAffineDifferential_horizontal_ladders
      cusp weight (sequence index))
    simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub] at identity
    simp_rw [identity]
    exact ((raising_limit.add lowering_limit).sub (first_limit.const_smul _)).const_smul _
  have vertical_limit : Tendsto (fun index => (cuspAffineDifferential cusp Complex.I (sequence
    index)).val)
      atTop (nhds vertical) := by
    have identity (index : ℕ) := congrArg Subtype.val (cuspAffineDifferential_vertical_ladders cusp
      weight (sequence index))
    simp only [Submodule.coe_smul, Submodule.coe_sub] at identity
    simp_rw [identity]
    exact (raising_limit.sub lowering_limit).const_smul _
  have derivative_limit := (realCoordinateCLM_continuous.tendsto (horizontal, vertical)).comp
    (horizontal_limit.prodMk_nhds vertical_limit)
  refine ⟨sequence, realCoordinateCLM horizontal vertical, members, first_limit, ?_, ?_⟩
  · simpa only [Function.comp_def, cuspAffineDifferential_apply, realCoordinateCLM_fderiv]
      using derivative_limit
  · simp only [realCoordinateCLM, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im,
      one_smul, zero_smul, add_zero, zero_add]
    change horizontal + Complex.I • vertical + (Complex.I * (weight : ℂ) / 2) • vector.val = raised
    dsimp only [horizontal, vertical]
    rw [smul_smul]
    have scalar : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]
    rw [scalar]
    module

end CloneBinaryRaisingGraphApproximation

end TernaryPeriodPolynomials.MultiplicityOne
