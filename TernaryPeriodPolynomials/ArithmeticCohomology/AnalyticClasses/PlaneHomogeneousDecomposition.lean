module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.PlaneCanonicalPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryRelative
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.ChosenRelative

@[expose] public section


/-!
# The source on real-plane simplices: canonical part plus an explicit coboundary

For a plane source cocycle with Codexiom's chosen relative representative
(`relative = sourcePlaneLevelGroupCocycle - δ(radical primitive extension)`), the explicit canonical
primitive gives, for every simplex `Q` of the real plane group `ℝ² ⋊ GL₂(ℝ)`,

`source(Q)(1) = Q₀ · Canon(Q₀⁻¹Q₁, Q₁⁻¹Q₂) + (δ K̂)(Q)`,

with `Canon` the canonical binary relative cocycle of the binary cocycle of `relative` and
`K̂(a, b) = a · K(a⁻¹ b)` the homogeneous form of the explicit total primitive
`K = realPlaneCanonicalPrimitive + radical primitive extension`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Homogeneous

variable {G : Type} [Group G]

/-- The homogeneous form of a one-cochain. -/
def homogeneousOne (representation : Rep ℂ G) (cochain : G → representation) (first second : G) :
    representation :=
  representation.ρ first (cochain (first⁻¹ * second))

theorem homogeneousOne_mul (representation : Rep ℂ G) (cochain : G → representation)
    (element first second : G) :
    homogeneousOne representation cochain (element * first) (element * second) =
      representation.ρ element (homogeneousOne representation cochain first second) := by
  unfold homogeneousOne
  rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

/-- The homogeneous form of a two-coboundary is the simplicial coboundary of the homogeneous
one-cochain. -/
theorem twoBoundaryCycle_homogeneous (representation : Rep ℂ G) (cochain : G → representation)
    (first second third : G) :
    representation.ρ first
        (twoBoundaryCycle representation cochain (first⁻¹ * second, second⁻¹ * third)) =
      homogeneousOne representation cochain second third -
        homogeneousOne representation cochain first third +
        homogeneousOne representation cochain first second := by
  rw [twoBoundaryCycle_apply, map_add, map_sub, ← Module.End.mul_apply, ← map_mul]
  unfold homogeneousOne
  rw [mul_inv_cancel_left, mul_assoc, mul_inv_cancel_left]

end Homogeneous

variable {index : Type} [Fintype index]

/-- The explicit canonical primitive of a finite-level relative cocycle. -/
def realPlaneLevelCanonicalPrimitive (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    RealPlaneGroup → realPlaneCuspidalRep degree cusp character := by
  subst character
  exact realPlaneCanonicalPrimitive degree cusp basis
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)

/-- **Explicit form of Codexiom's canonical comparison at finite level.** -/
theorem realPlaneLevelBinaryRelativeCycle_explicit (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    (realPlaneLevelForgetRelative degree cusp character cycle).val =
      (realPlaneLevelBinaryRelativeCycle degree cusp character trivial basis cycle regular).val +
        twoBoundaryCycle (realPlaneCuspidalRep degree cusp character)
          (realPlaneLevelCanonicalPrimitive degree cusp character trivial basis cycle regular) := by
  subst character
  exact realPlaneBinaryRelativeCycle_explicit degree cusp basis central_positive
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)

variable {n : ℕ}

/-- Forgetting the finite level. -/
def levelVal (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    realPlaneLevelCuspidalRep degree cusp character →ₗ[ℂ]
      realPlaneCuspidalRep degree cusp character :=
  (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).subtype

theorem levelVal_apply (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (vector : realPlaneLevelCuspidalRep degree cusp character) :
    levelVal degree cusp character vector = vector.val := rfl

theorem levelVal_equivariant (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (element : RealPlaneGroup)
    (vector : realPlaneLevelCuspidalRep degree cusp character) :
    levelVal degree cusp character
        ((realPlaneLevelCuspidalRep degree cusp character).ρ element vector) =
      (realPlaneCuspidalRep degree cusp character).ρ element
        (levelVal degree cusp character vector) :=
  rfl

theorem levelVal_twoBoundary (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter)
    (cochain : RealPlaneGroup → realPlaneLevelCuspidalRep degree cusp character)
    (first second : RealPlaneGroup) :
    levelVal degree cusp character
        (twoBoundaryCycle (realPlaneLevelCuspidalRep degree cusp character) cochain
          (first, second)) =
      twoBoundaryCycle (realPlaneCuspidalRep degree cusp character)
        (fun element => levelVal degree cusp character (cochain element)) (first, second) := by
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, map_add, map_sub, levelVal_equivariant]

/-- The explicit total primitive of the source on the real plane group. -/
def sourceTotalPrimitive (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    RealPlaneGroup → realPlaneCuspidalRep n data.cusp data.chi :=
  realPlaneLevelCanonicalPrimitive n data.cusp data.chi trivial basis relative regular +
    fun element => levelVal n data.cusp data.chi (realPlanePrimitiveExtension _ primitive element)

theorem twoBoundaryCycle_add {G : Type} [Group G] (representation : Rep ℂ G)
    (first second : G → representation) (pair : G × G) :
    twoBoundaryCycle representation (first + second) pair =
      twoBoundaryCycle representation first pair + twoBoundaryCycle representation second pair := by
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply]
  simp only [Pi.add_apply, map_add]
  abel

/-- **The source group cocycle is the canonical cocycle plus an explicit coboundary.** -/
theorem sourcePlaneLevelGroupCocycle_explicit (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (first second : RealPlaneGroup) :
    levelVal n data.cusp data.chi
        (sourcePlaneLevelGroupCocycle data source cocycle (first, second)) =
      (realPlaneLevelBinaryRelativeCycle n data.cusp data.chi trivial basis relative regular).val
          (first, second) +
        twoBoundaryCycle (realPlaneCuspidalRep n data.cusp data.chi)
          (sourceTotalPrimitive data trivial basis primitive relative regular) (first, second) := by
  have central := cohomological_centralCharacter_positive data.cusp data.cohomological
  have canonical := congrArg (fun cochain => cochain (first, second))
    (realPlaneLevelBinaryRelativeCycle_explicit n data.cusp data.chi trivial central basis
      relative regular)
  have value := congrArg (fun cochain => cochain (first, second)) formula
  have levelSplit : sourcePlaneLevelGroupCocycle data source cocycle (first, second) =
      relative.val (first, second) +
        twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) (first, second) := by
    change _ = (relative.val : _) (first, second) + _
    rw [value]
    change _ = sourcePlaneLevelGroupCocycle data source cocycle (first, second) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) (first, second) +
        twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) (first, second)
    abel
  have forget : levelVal n data.cusp data.chi (relative.val (first, second)) =
      (realPlaneLevelForgetRelative n data.cusp data.chi relative).val (first, second) := rfl
  rw [levelSplit, map_add, forget, canonical, levelVal_twoBoundary, sourceTotalPrimitive,
    twoBoundaryCycle_add]
  have expand :
      ((realPlaneLevelBinaryRelativeCycle n data.cusp data.chi trivial basis relative regular).val +
        twoBoundaryCycle (realPlaneCuspidalRep n data.cusp data.chi)
          (realPlaneLevelCanonicalPrimitive n data.cusp data.chi trivial basis relative regular))
          (first, second) =
        (realPlaneLevelBinaryRelativeCycle n data.cusp data.chi trivial basis relative regular).val
            (first, second) +
          twoBoundaryCycle (realPlaneCuspidalRep n data.cusp data.chi)
            (realPlaneLevelCanonicalPrimitive n data.cusp data.chi trivial basis relative regular)
            (first, second) := rfl
  rw [expand]
  abel

/-- The value of the source group cocycle as a source value on a real-plane simplex. -/
theorem sourcePlaneLevelGroupCocycle_val (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (first second : RealPlaneGroup) :
    levelVal n data.cusp data.chi
        (sourcePlaneLevelGroupCocycle data source cocycle (first, second)) =
      sourcePlaneCuspidalValues data source cocycle
        (fun index => realPlaneMatrix (![1, first, first * second] index)) 1 := rfl

/-- **The source on a real-plane simplex.** -/
theorem sourcePlaneCuspidalValues_planeSimplex (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (Q : Fin 3 → RealPlaneGroup) :
    sourcePlaneCuspidalValues data source cocycle (fun index => realPlaneMatrix (Q index)) 1 =
      (realPlaneCuspidalRep n data.cusp data.chi).ρ (Q 0)
          ((realPlaneLevelBinaryRelativeCycle n data.cusp data.chi trivial basis relative
              regular).val
            ((Q 0)⁻¹ * Q 1, (Q 1)⁻¹ * Q 2)) +
        (homogeneousOne (realPlaneCuspidalRep n data.cusp data.chi)
            (sourceTotalPrimitive data trivial basis primitive relative regular) (Q 1) (Q 2) -
          homogeneousOne (realPlaneCuspidalRep n data.cusp data.chi)
            (sourceTotalPrimitive data trivial basis primitive relative regular) (Q 0) (Q 2) +
          homogeneousOne (realPlaneCuspidalRep n data.cusp data.chi)
            (sourceTotalPrimitive data trivial basis primitive relative regular) (Q 0) (Q 1)) := by
  have moved : (fun index => realPlaneMatrix (Q index)) =
      fun index => realPlaneMatrix (Q 0) *
        realPlaneMatrix (![1, (Q 0)⁻¹ * Q 1, (Q 0)⁻¹ * Q 1 * ((Q 1)⁻¹ * Q 2)] index) := by
    funext index
    fin_cases index <;> simp [← map_mul]
  rw [moved, sourcePlaneCuspidalValues_equivariant, ← sourcePlaneLevelGroupCocycle_val,
    sourcePlaneLevelGroupCocycle_explicit data trivial basis source cocycle primitive relative
      formula
      regular, map_add, twoBoundaryCycle_homogeneous]

end TernaryPeriodPolynomials.AnalyticClasses
