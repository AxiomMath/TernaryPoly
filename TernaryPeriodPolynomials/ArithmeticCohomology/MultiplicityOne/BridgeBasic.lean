module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.PrincipalLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalWeights

@[expose] public section


/-!
# Level-three port: basic projection API

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinarySphericalProjection`, `SphericalDetection.BinarySphericalWeights`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section Prelude

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel PlaneLevelVector)

/-- A nonzero smooth vector fixed by the level-three group of the good plane
(`{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}`); the level-three analogue of `SphericalCusp`. -/
def LevelThreeCusp (σ : CuspidalRepresentation) : Prop :=
  ∃ v : σ.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues σ

theorem planeLevelVector_true_iff_levelThreeCusp (σ : CuspidalRepresentation) :
    PlaneLevelVector σ true ↔ LevelThreeCusp σ :=
  planeLevelVector_true_iff σ

/-- The principal congruence subgroup of level three: an open compact subgroup contained in the
level-three group, used to certify smoothness of level-three vectors. -/
def levelThreeSmoothLevel : Subgroup BinaryFiniteGL :=
  EisensteinRegularization.Helpers.binaryPrincipalLevel

theorem levelThreeSmoothLevel_isOpen : IsOpen (levelThreeSmoothLevel : Set BinaryFiniteGL) :=
  EisensteinRegularization.Helpers.binaryPrincipalLevel_isOpen

theorem levelThreeSmoothLevel_isCompact : IsCompact (levelThreeSmoothLevel : Set BinaryFiniteGL) :=
  EisensteinRegularization.Helpers.binaryPrincipalLevel_isCompact

theorem levelThreeValues_fixed_smoothLevel (cusp : CuspidalRepresentation) (vector : cusp.H)
    (member : vector ∈ levelThreeValues cusp) (g : BinaryFiniteGL)
    (level : g ∈ levelThreeSmoothLevel) : cusp.π (atFinite g) vector = vector := by
  obtain ⟨k, reduced, rfl⟩ := level
  have reduced_one : GeneralLinearGroup.map integralReduction k = 1 := reduced
  have in_level : PlaneLeviLevel k := by
    unfold PlaneLeviLevel
    rw [reduced_one]
    simp
  exact mem_levelThreeValues.mp member k in_level

end Prelude

section CloneBinarySphericalProjection

open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open GeneralEisenstein GeneralEisenstein.Adelic Matrix

theorem levelThreeValues_closed (cusp : CuspidalRepresentation) :
    IsClosed (levelThreeValues cusp : Set cusp.H) := by
  have equality : (levelThreeValues cusp : Set cusp.H) =
      ⋂ element : {k : GeneralLinearGroup (Fin 2) IntegralAdeles // PlaneLeviLevel k},
        {vector : cusp.H |
          cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding element.val)) vector =
            vector} := by
    ext vector
    constructor
    · intro member
      have fixed : vector ∈ levelThreeValues cusp := member
      refine Set.mem_iInter.mpr fun element => ?_
      exact mem_levelThreeValues.mp fixed element.val element.property
    · intro member
      show vector ∈ levelThreeValues cusp
      refine mem_levelThreeValues.mpr fun k level => ?_
      exact Set.mem_iInter.mp member ⟨k, level⟩
  rw [equality]
  refine isClosed_iInter fun element => ?_
  exact isClosed_eq (cuspUnitaryOperator cusp
    (atFinite (GeneralLinearGroup.map integralEmbedding element.val))).continuous continuous_id

instance levelThreeValues_completeSpace (cusp : CuspidalRepresentation) :
    CompleteSpace (levelThreeValues cusp) := by
  let : IsClosed (levelThreeValues cusp : Set cusp.H) := levelThreeValues_closed cusp
  infer_instance

def levelThreeProjection (cusp : CuspidalRepresentation) : cusp.H →L[ℂ] cusp.H :=
  (levelThreeValues cusp).starProjection

theorem levelThreeProjection_eq_self_iff (cusp : CuspidalRepresentation) (vector : cusp.H) :
    levelThreeProjection cusp vector = vector ↔ vector ∈ levelThreeValues cusp :=
  Submodule.starProjection_eq_self_iff

theorem levelThreeProjection_mem (cusp : CuspidalRepresentation) (vector : cusp.H) :
    levelThreeProjection cusp vector ∈ levelThreeValues cusp := by
  change (levelThreeValues cusp).starProjection vector ∈ levelThreeValues cusp
  have member : (levelThreeValues cusp).starProjection vector ∈
      (levelThreeValues cusp).starProjection.toLinearMap.range := ⟨vector, rfl⟩
  rwa [Submodule.range_starProjection] at member

theorem levelThreeProjection_ne_zero (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) : levelThreeProjection cusp ≠ 0 := by
  intro zero
  obtain ⟨vector, nonzero, fixed⟩ := spherical
  have identity := (levelThreeProjection_eq_self_iff cusp vector.val).mpr fixed
  rw [zero, _root_.zero_apply] at identity
  exact nonzero (Subtype.ext identity.symm)

theorem levelThreeValues_real_stable (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL) (vector : cusp.H) (fixed : vector ∈ levelThreeValues cusp) :
    cusp.π (atInfinity matrix) vector ∈ levelThreeValues cusp := by
  refine mem_levelThreeValues.mpr fun element level => ?_
  change (cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding element)) *
    cusp.π (atInfinity matrix)) vector = _
  rw [← map_mul, (atInfinity_commute_atFinite matrix
    (GeneralLinearGroup.map integralEmbedding element)).symm.eq, map_mul, Module.End.mul_apply,
    mem_levelThreeValues.mp fixed element level]

theorem levelThreeValues_real_map (cusp : CuspidalRepresentation) (matrix : BinaryRealGL) :
    (levelThreeValues cusp).map (cusp.π (atInfinity matrix)) = levelThreeValues cusp := by
  apply le_antisymm
  · rintro _ ⟨vector, fixed, rfl⟩
    exact levelThreeValues_real_stable cusp matrix vector fixed
  · intro vector fixed
    refine ⟨cusp.π (atInfinity matrix⁻¹) vector,
      levelThreeValues_real_stable cusp matrix⁻¹ vector fixed, ?_⟩
    change (cusp.π (atInfinity matrix) * cusp.π (atInfinity matrix⁻¹)) vector = vector
    rw [← map_mul, ← atInfinity_mul, mul_inv_cancel, atInfinity_one, map_one]
    rfl

theorem levelThreeProjection_real (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL) (vector : cusp.H) :
    levelThreeProjection cusp (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (levelThreeProjection cusp vector) := by
  have naturality := Submodule.starProjection_map_apply
    (cuspUnitaryIsometryEquiv cusp (atInfinity matrix)) (levelThreeValues cusp)
    (cuspUnitaryIsometryEquiv cusp (atInfinity matrix) vector)
  rw [LinearIsometryEquiv.symm_apply_apply] at naturality
  have map_eq : (levelThreeValues cusp).map
      (cuspUnitaryIsometryEquiv cusp (atInfinity matrix)).toLinearEquiv.toLinearMap =
      levelThreeValues cusp := levelThreeValues_real_map cusp matrix
  simp only [map_eq] at naturality
  exact naturality

theorem levelThreeProjection_finite_nonzero (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) (vector : cusp.H) (nonzero : vector ≠ 0) :
    ∃ finite : BinaryFiniteGL,
      levelThreeProjection cusp (cusp.π (atFinite finite) vector) ≠ 0 := by
  obtain ⟨matrix, detected⟩ := cusp_exists_translate_detected cusp
    (levelThreeProjection cusp) (levelThreeProjection_ne_zero cusp spherical) vector nonzero
  obtain ⟨real, finite, decomposition⟩ := binaryAdelic_exists_real_finite matrix
  refine ⟨finite, ?_⟩
  intro zero
  apply detected
  rw [decomposition, map_mul, Module.End.mul_apply, levelThreeProjection_real, zero, map_zero]

end CloneBinarySphericalProjection

section CloneBinarySphericalWeights

open GeneralEisenstein GeneralEisenstein.Adelic

theorem levelThreeProjection_finite_real (cusp : CuspidalRepresentation)
    (finite : BinaryFiniteGL) (real : BinaryRealGL) (vector : cusp.H) :
    levelThreeProjection cusp
        (cusp.π (atFinite finite) (cusp.π (atInfinity real) vector)) =
      cusp.π (atInfinity real)
        (levelThreeProjection cusp (cusp.π (atFinite finite) vector)) := by
  change levelThreeProjection cusp
      ((cusp.π (atFinite finite) * cusp.π (atInfinity real)) vector) = _
  rw [← map_mul, (atInfinity_commute_atFinite real finite).symm.eq, map_mul,
    Module.End.mul_apply, levelThreeProjection_real]

end CloneBinarySphericalWeights

end TernaryPeriodPolynomials.MultiplicityOne
