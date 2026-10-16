module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart5
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeExtremalReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineDerivativeLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskOrbit

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part6

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryRelativeComparison`,
`SphericalDetection.BinaryRelativeExtremalReduction`,
`SphericalDetection.BinaryAffineDerivativeLimit`,
`SphericalDetection.BinaryCohomologicalHolomorphic`, `SphericalDetection.BinaryDiskOrbit`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryRelativeComparison

open GeneralEisenstein GeneralEisenstein.Adelic

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryRelativePair_coboundary_iff (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (lower upper : binarySmoothValues cusp index)
    (lower_value : binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical
      basis level cycle)
    (upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
          Complex.I) :
    groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle = 0 ↔
      ∃ primitive : binarySmoothValues cusp index,
        (∀ element : level, ∀ position, cusp.π (atFinite element.val) (primitive position).val =
          (primitive position).val) ∧
        (∀ angle : Circle, binaryHilbertOperator cusp basis (binaryRotations angle)
          (binarySmoothValues_val cusp primitive) =
          binarySmoothValues_val cusp primitive) ∧
        binaryRelativeLowering cusp basis 0 primitive = lower ∧
        binaryRelativeRaising cusp basis 0 primitive = upper := by
  have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by
    simp)
  constructor
  · intro zero
    obtain ⟨finite_primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
    have potential : binaryUpperPotential cusp spherical basis level cycle =
        fun point => binaryAffineOrbitVector cusp basis finite_primitive.val point -
          finite_primitive.val := by
      funext point
      exact (congrArg Subtype.val (congrFun boundary (invertibleMatrix (binaryUpperSectionMatrix
        point)))).symm
    have primitive_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (binaryAffineOrbitVector cusp basis finite_primitive.val) UpperHalfPlane.upperHalfPlaneSet
          := by
      apply (regular.add (contDiffOn_const (c := finite_primitive.val))).congr
      intro point _
      rw [potential]
      simp only [sub_add_cancel]
    let primitive : binarySmoothValues cusp index := fun position =>
      ⟨finite_primitive.val position, cuspAffineOrbitVector_coordinate_contDiffOn cusp basis _
        primitive_regular position⟩
    have primitive_value : binarySmoothValues_val cusp primitive = finite_primitive.val := rfl
    have derivative := (((primitive_regular.differentiableOn (by simp)).differentiableAt
      neighborhood).hasFDerivAt.sub_const
      finite_primitive.val).fderiv
    have lower_derivative : binarySmoothValues_val cusp (binaryRelativeLowering cusp basis 0
      primitive) =
        binarySmoothValues_val cusp lower := by
      rw [binaryRelativeLowering_actual, lower_value, binaryHolomorphicTangent, potential,
        derivative, primitive_value]
      simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero]
    have upper_derivative : binarySmoothValues_val cusp (binaryRelativeRaising cusp basis 0
      primitive) =
        binarySmoothValues_val cusp upper := by
      rw [binaryRelativeRaising_actual, upper_value, potential, derivative, primitive_value]
      simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero]
    refine ⟨primitive, finite_primitive.property, ?_,
      binarySmoothValues_val_injective cusp lower_derivative, binarySmoothValues_val_injective cusp
        upper_derivative⟩
    intro angle
    have identity := congrArg Subtype.val (congrFun boundary (binaryRotations angle))
    change binaryHilbertOperator cusp basis (binaryRotations angle) finite_primitive.val -
      finite_primitive.val =
      (cycle (binaryRotations angle) : binaryHilbertFiniteValues cusp level).val at identity
    rw [rotations_zero] at identity
    exact sub_eq_zero.mp identity
  · rintro ⟨primitive, primitive_finite, primitive_rotation, primitive_lower, primitive_upper⟩
    by_contra nonzero
    let finite_primitive : binaryHilbertFiniteValues (index := index) cusp level :=
      ⟨binarySmoothValues_val cusp primitive, primitive_finite⟩
    let shifted := shiftCocycle (binaryHilbertFiniteRep cusp spherical basis level) cycle
      finite_primitive
    have shifted_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
      shifted ≠ 0 := by
      intro zero
      exact nonzero ((shiftCocycle_H1 _ cycle finite_primitive).symm.trans zero)
    have primitive_regular := binarySmoothValues_regular cusp basis primitive
    have shifted_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (binaryUpperPotential cusp spherical basis level shifted) UpperHalfPlane.upperHalfPlaneSet
          := by
      rw [show shifted = shiftCocycle _ cycle finite_primitive from rfl, binaryUpperPotential_shift]
      exact regular.sub (primitive_regular.sub contDiffOn_const)
    have shifted_rotations (angle : Circle) : shifted (binaryRotations angle) = 0 := by
      apply shiftCocycle_zero_of_fixed _ _ _ _ (rotations_zero angle)
      exact Subtype.ext (primitive_rotation angle)
    have shifted_central := binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical
      cohomological basis level
      level_open level_compact shifted
    have shifted_derivative := binaryUpperPotential_shift_fderiv cusp spherical basis level cycle
      finite_primitive
      ((regular.differentiableOn (by simp)).differentiableAt neighborhood)
      ((primitive_regular.differentiableOn (by simp)).differentiableAt neighborhood)
    have lower_derivative := congrArg (binarySmoothValues_val cusp) primitive_lower
    have upper_derivative := congrArg (binarySmoothValues_val cusp) primitive_upper
    rw [binaryRelativeLowering_actual, lower_value, binaryHolomorphicTangent] at lower_derivative
    rw [binaryRelativeRaising_actual, upper_value] at upper_derivative
    simp only [Int.cast_zero, mul_zero, zero_div, zero_smul,
      add_zero] at lower_derivative upper_derivative
    let difference := fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I
    have lower_zero : difference 1 - Complex.I • difference Complex.I = 0 := by
      dsimp only [difference]
      rw [show shifted = shiftCocycle _ cycle finite_primitive from rfl, shifted_derivative]
      change (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
        primitive)) Complex.I 1) -
        Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
          primitive)) Complex.I Complex.I) = 0
      have zero := sub_eq_zero.mpr lower_derivative.symm
      convert zero using 1
      module
    have upper_zero : difference 1 + Complex.I • difference Complex.I = 0 := by
      dsimp only [difference]
      rw [show shifted = shiftCocycle _ cycle finite_primitive from rfl, shifted_derivative]
      change (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
        primitive)) Complex.I 1) +
        Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
          primitive)) Complex.I Complex.I) = 0
      have zero := sub_eq_zero.mpr upper_derivative.symm
      convert zero using 1
      module
    have zero := realLinear_eq_zero_of_tangent_pair difference.toLinearMap lower_zero upper_zero
    apply binaryUpperPotential_fderiv_ne_zero_of_rotations cusp spherical basis level shifted
      shifted_nonzero
      (shifted_regular.differentiableOn (by simp)) shifted_rotations shifted_central
    apply ContinuousLinearMap.ext
    exact LinearMap.congr_fun zero

end CloneBinaryRelativeComparison

section CloneBinaryRelativeExtremalReduction

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cohomological_extremal_or_raising_obstruction (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ level : Subgroup BinaryFiniteGL,
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      ((∃ vector : cuspAffineSmoothValues cusp, vector ≠ 0 ∧
          vector ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) ∧
          cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) vector = 0) ∨
        ∃ vector : cuspAffineSmoothValues cusp,
          vector ∈ cuspFiniteWeightValues cusp level (2 + (degree + 1 : ℕ)) ∧
          ¬∃ preimage : cuspAffineSmoothValues cusp,
            preimage ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ) ∧
            cuspRaisingOperator cusp (degree + 1 : ℕ) preimage = vector) := by
  obtain ⟨level, cycle, lower, upper, level_open, level_compact, nonzero, regular, rotations_zero,
    _, lower_mem, upper_mem, lower_value, upper_value, closed, support, _⟩ :=
    cohomological_exists_relative_normal_form cusp spherical cohomological
  refine ⟨level, level_open, level_compact, ?_⟩
  by_cases lifts : ∃ preimage : cuspAffineSmoothValues cusp,
      preimage ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ) ∧
      cuspRaisingOperator cusp (degree + 1 : ℕ) preimage = upper (Fin.last (degree + 1))
  · obtain ⟨preimage, preimage_mem, preimage_raising⟩ := lifts
    left
    apply binaryRelative_extremal_of_upper_lift cusp degree level lower upper lower_mem closed
      support _
      preimage preimage_mem preimage_raising
    exact mt (binaryRelativePair_coboundary_iff cusp spherical cohomological (binaryWeightBasis
      (degree + 1))
      level level_open level_compact cycle regular rotations_zero lower upper lower_value
        upper_value).mpr nonzero
  · right
    refine ⟨upper (Fin.last (degree + 1)), ?_, lifts⟩
    have weight : binaryUnitaryWeight degree 2 (Fin.last (degree + 1)) = 2 + (degree + 1 : ℕ) := by
      simp only [binaryUnitaryWeight, Fin.val_last]
      omega
    rw [← weight]
    exact upper_mem _

end CloneBinaryRelativeExtremalReduction

section CloneBinaryAffineDerivativeLimit

open GeneralEisenstein GeneralEisenstein.Adelic

open Filter

theorem cuspFiniteRaisingPMap_closure_differentiable (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (nonnegative : 0 ≤ weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector.val) UpperHalfPlane.upperHalfPlaneSet ∧
      cuspRaisingVector cusp weight vector.val = ((cuspFiniteRaisingPMap cusp level weight).closure
        vector : cusp.H) := by
  obtain ⟨sequence, derivative, _, vector_limit, derivative_limit, raising_eq⟩ :=
    cuspRaising_graph_approximation_fderiv cusp spherical level weight nonnegative vector
  have derivative_at := cuspAffineOrbitVector_hasFDerivAt_of_limit cusp sequence vector.val
    derivative vector_limit derivative_limit
  constructor
  · intro point positive
    exact (derivative_at point positive).differentiableAt.differentiableWithinAt
  · have basepoint := (derivative_at Complex.I (by simp)).fderiv
    rw [cuspAffineDerivativeTranslate_I] at basepoint
    rw [cuspRaisingVector, basepoint]
    exact raising_eq

theorem cohomological_extremal_or_analytic_obstruction (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ level : Subgroup BinaryFiniteGL,
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      ((∃ vector : cuspAffineSmoothValues cusp, vector ≠ 0 ∧
          vector ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) ∧
          cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) vector = 0) ∨
        (∃ vector : cusp.H, vector ≠ 0 ∧ vector ∈ cuspHilbertWeightValues cusp level ((degree + 1 :
          ℕ) + 2) ∧
          ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level
            (degree + 1 : ℕ) →
            inner ℂ vector (cuspRaisingOperator cusp (degree + 1 : ℕ) smooth).val = 0) ∨
        ∃ vector : cusp.H, vector ∈ cuspHilbertWeightValues cusp level (degree + 1 : ℕ) ∧
          DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet ∧
          vector ∉ cuspAffineSmoothValues cusp ∧
          cuspRaisingVector cusp (degree + 1 : ℕ) vector ∈ cuspAffineSmoothValues cusp) := by
  obtain ⟨level, level_open, level_compact, alternatives⟩ :=
    cohomological_extremal_or_raising_obstruction cusp spherical cohomological
  refine ⟨level, level_open, level_compact, ?_⟩
  rcases alternatives with extremal | ⟨vector, member, no_smooth_preimage⟩
  · exact Or.inl extremal
  · right
    have positive : (0 : ℤ) < (degree + 1 : ℕ) := by omega
    have vector_weight : vector.val ∈ cuspHilbertWeightValues cusp level ((degree + 1 : ℕ) + 2) :=
      by
      have hilbert_member : vector.val ∈ cuspHilbertWeightValues cusp level (2 + (degree + 1 : ℕ))
        := member
      simpa only [add_comm] using hilbert_member
    by_cases in_range : vector.val ∈ (cuspFiniteRaisingPMap cusp level (degree + 1 :
      ℕ)).closure.toFun.range
    · right
      obtain ⟨preimage, image_eq⟩ := in_range
      change ((cuspFiniteRaisingPMap cusp level (degree + 1 : ℕ)).closure preimage : cusp.H) =
        vector.val at image_eq
      have weights := cuspFiniteRaisingPMap_closure_weights cusp spherical level (degree + 1 : ℕ)
        preimage
      have actual := cuspFiniteRaisingPMap_closure_differentiable cusp spherical level (degree + 1
        : ℕ) positive.le preimage
      have raised : cuspRaisingVector cusp (degree + 1 : ℕ) preimage.val = vector.val :=
        actual.2.trans image_eq
      refine ⟨preimage.val, weights.1, actual.1, ?_, raised.symm ▸ vector.property⟩
      intro regular
      apply no_smooth_preimage
      refine ⟨⟨preimage.val, regular⟩, weights.1, ?_⟩
      exact Subtype.ext raised
    · left
      exact cuspFiniteRaising_exists_weak_kernel_of_not_mem cusp spherical level (degree + 1 : ℕ)
        positive
        vector.val vector_weight in_range

end CloneBinaryAffineDerivativeLimit

section CloneBinaryCohomologicalHolomorphic

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cohomological_holomorphic_or_regularity_obstruction (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (odd : Odd degree) (cohomological :
      Cohomological cusp degree) :
    (∃ (halfWeight : ℤ) (vector : cusp.smooth), 2 * halfWeight = -((degree : ℤ) + 3) ∧
      vector ≠ 0 ∧ vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ (2 * halfWeight) • vector.val) ∧
      cuspRaisingVector cusp (2 * halfWeight) vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
        UpperHalfPlane.upperHalfPlaneSet) ∨
    ∃ (level : Subgroup BinaryFiniteGL) (vector : cusp.H),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      vector ∈ cuspHilbertWeightValues cusp level (degree + 1 : ℕ) ∧
      DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet ∧
      vector ∉ cuspAffineSmoothValues cusp ∧
      cuspRaisingVector cusp (degree + 1 : ℕ) vector ∈ cuspAffineSmoothValues cusp := by
  obtain ⟨level, level_open, level_compact, alternatives⟩ :=
    cohomological_extremal_or_analytic_obstruction cusp spherical cohomological
  have central_positive := cohomological_centralCharacter_positive cusp cohomological
  obtain ⟨index, degree_eq⟩ := odd
  let halfWeight : ℤ := (index : ℤ) + 2
  have weight_eq : ((degree + 1 : ℕ) : ℤ) + 2 = 2 * halfWeight := by
    dsimp [halfWeight]
    omega
  have negative_eq : -2 - ((degree + 1 : ℕ) : ℤ) = 2 * (-halfWeight) := by omega
  have target_eq : 2 * (-halfWeight) = -((degree : ℤ) + 3) := by omega
  rcases alternatives
    with ⟨vector, nonzero, member, killed⟩ | ⟨vector, nonzero, member, annihilates⟩ |
    ⟨vector, member, differentiable, not_smooth, raised_smooth⟩
  · left
    have value_nonzero : vector.val ≠ 0 := fun equality => nonzero (Subtype.ext equality)
    have rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • vector.val := by
      simpa only [negative_eq] using member.2
    have raising_zero : cuspRaisingVector cusp (2 * (-halfWeight)) vector.val = 0 := by
      have equality := congrArg Subtype.val killed
      change cuspRaisingVector cusp (-2 - (degree + 1 : ℕ)) vector.val = 0 at equality
      simpa only [negative_eq] using equality
    obtain ⟨result, result_nonzero, fixed, rotation, killed, holomorphic⟩ :=
      cusp_exists_levelThree_smooth_raising_zero cusp spherical central_positive vector.val
        (-halfWeight)
        value_nonzero rotation vector.property raising_zero
    exact ⟨-halfWeight, result, target_eq, result_nonzero, fixed, rotation, killed, holomorphic⟩
  · left
    obtain ⟨result, result_nonzero, fixed, rotation, killed, holomorphic⟩ :=
      cuspWeightWeakLoweringKernel_exists_levelThree cusp spherical central_positive level
        level_open level_compact
        (degree + 1 : ℕ) halfWeight weight_eq vector nonzero member annihilates
    exact ⟨-halfWeight, result, target_eq, result_nonzero, fixed, rotation, killed, holomorphic⟩
  · exact Or.inr ⟨level, vector, level_open, level_compact, member, differentiable, not_smooth,
      raised_smooth⟩

/-- The actual nonzero cohomology class supplies an exact spherical holomorphic vector. -/
theorem cohomological_exists_levelThree_holomorphic (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (odd : Odd degree) (cohomological :
      Cohomological cusp degree) :
    ∃ (halfWeight : ℤ) (vector : cusp.smooth), 2 * halfWeight = -((degree : ℤ) + 3) ∧
      vector ≠ 0 ∧ vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ (2 * halfWeight) • vector.val) ∧
      cuspRaisingVector cusp (2 * halfWeight) vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  rcases cohomological_holomorphic_or_regularity_obstruction cusp spherical odd cohomological
    with result | obstruction
  · exact result
  · obtain ⟨_, vector, _, _, _, differentiable, not_smooth, raised_smooth⟩ := obstruction
    obtain ⟨index, degree_eq⟩ := odd
    have weight_eq : ((degree + 1 : ℕ) : ℤ) = 2 * ((index : ℤ) + 1) := by omega
    rw [weight_eq] at raised_smooth
    exact False.elim (not_smooth (cuspAffineOrbitVector_contDiffOn_of_raising_smooth cusp ((index :
      ℤ) + 1)
      vector differentiable raised_smooth))

end CloneBinaryCohomologicalHolomorphic

section CloneBinaryDiskOrbit

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspDiskOrbit_levelThree (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (spherical : vector ∈ levelThreeValues cusp) (point : ℂ) :
    cuspDiskOrbit cusp halfWeight vector point ∈ levelThreeValues cusp := by
  unfold cuspDiskOrbit cuspWeightedAffineOrbit cuspAffineOrbitVector
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (levelThreeValues cusp).smul_mem _ ((levelThreeValues cusp).smul_mem _
    (levelThreeValues_real_stable cusp _ vector spherical))

end CloneBinaryDiskOrbit

end TernaryPeriodPolynomials.MultiplicityOne
