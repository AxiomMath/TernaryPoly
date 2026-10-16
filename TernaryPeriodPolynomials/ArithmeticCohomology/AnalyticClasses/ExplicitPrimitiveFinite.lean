module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ProjectedTermDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryFinite

@[expose] public section


/-!
# Finite level of the explicit primitives

The explicit split-extension primitive is built from values of the relative cocycle and of the
potentials by the representation, sums and scalars, so it takes values in every invariant submodule
containing those values. For the real-plane canonical primitive and the total source primitive this
gives finite level, hence sphericity of every transported edge.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Generic

variable {N E L : Type} [Group N] [Group E] [Group L]
variable {extension : GroupExtension N E L}

/-- **The explicit primitive takes values in every invariant submodule containing the data.** -/
theorem explicitSplitPrimitive_mem (splitting : extension.Splitting) (representation : Rep ℂ E)
    (W : Submodule ℂ representation)
    (stable : ∀ element vector, vector ∈ W → representation.ρ element vector ∈ W)
    (cycle : relativeTwoCocycles extension.inl representation)
    (cycle_mem : ∀ pair, cycle.val pair ∈ W) (potential : L → representation)
    (potential_mem : ∀ levi, potential levi ∈ W) (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res extension.inl representation) (potential levi) =
        splitEdgeCycle splitting representation levi cycle)
    (central : L) (scalar : ℂ) (element : E) :
    explicitSplitPrimitive splitting representation cycle potential potential_one boundary central
      scalar element ∈ W := by
  have first (pair : E × E) :
      (potentialCorrected representation cycle potential potential_one).val pair ∈ W := by
    rw [potentialCorrected_apply]
    exact W.add_mem (cycle_mem _) (W.add_mem (W.sub_mem (stable _ _ (potential_mem _))
      (potential_mem _)) (potential_mem _))
  have mixed (e : E) : splitMixedPrimitive splitting representation
      (potentialCorrected representation cycle potential potential_one) e ∈ W := first _
  have second (pair : E × E) : (mixedCorrected splitting representation
      (potentialCorrected representation cycle potential potential_one)).val pair ∈ W := by
    rw [mixedCorrected_val]
    change _ + twoBoundaryCycle _ _ pair ∈ W
    rw [twoBoundaryCycle_apply]
    exact W.add_mem (first _) (W.add_mem (W.sub_mem (stable _ _ (mixed _)) (mixed _)) (mixed _))
  have levi (l : L) : (explicitLeviPrimitive splitting representation cycle potential potential_one
      boundary central scalar l).val ∈ W := by
    unfold explicitLeviPrimitive
    change (scalar - 1)⁻¹ • ((explicitDescended splitting representation cycle potential
      potential_one boundary (central, l)).val -
        (explicitDescended splitting representation cycle potential potential_one boundary
          (l, central)).val) ∈ W
    exact W.smul_mem _ (W.sub_mem (second _) (second _))
  unfold explicitSplitPrimitive
  exact W.sub_mem (W.sub_mem (levi _) (mixed _)) (potential_mem _)

end Generic

variable {index : Type} [Fintype index]

theorem realPlaneCuspidalRep_trivial_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (element : RealPlaneGroup) (values : cuspidalTensorValues cusp (HomogeneousPoly degree))
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) :
    (realPlaneCuspidalRep degree cusp trivialCharacter).ρ element values ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) :=
  realPlaneCuspidalRep_finiteLevel degree cusp trivialCharacter element values fixed

theorem latticePotential_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (first second : cuspidalTensorValues cusp (HomogeneousPoly degree))
    (first_mem : first ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (second_mem : second ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) :
    latticePotential degree cusp first second ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) :=
  Submodule.add_mem _ (cuspidalTensorMap_finiteLevel _ _ _ first_mem)
    (cuspidalTensorMap_finiteLevel _ _ _ second_mem)

/-- The canonical binary relative cocycle has finite-level values. -/
theorem realPlaneLevelBinaryRelativeCycle_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (pair : RealPlaneGroup × RealPlaneGroup) :
    (realPlaneLevelBinaryRelativeCycle degree cusp character trivial basis cycle regular).val pair ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
  intro matrix argument
  obtain ⟨first, second⟩ := pair
  rw [realPlaneLevelBinaryRelativeCycle_apply, realPlaneLevelBinaryRelativeCycle_apply]
  have fixed := congrArg (fun values : binaryCuspidalValues cusp degree => values.val argument)
    (realPlaneLevelBinaryCocycle_finiteLevel degree cusp character trivial basis cycle regular
      ⟨GeneralLinearGroup.map integralEmbedding matrix, matrix, rfl⟩ first.right)
  change ((realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular
      first.right).val (argument * atFinite (GeneralLinearGroup.map integralEmbedding matrix))) =
    (realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular
      first.right).val argument at fixed
  rw [fixed]

/-- The explicit canonical primitive of a finite-level relative cocycle has finite-level values. -/
theorem realPlaneLevelCanonicalPrimitive_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (element : RealPlaneGroup) :
    realPlaneLevelCanonicalPrimitive degree cusp character trivial basis cycle regular element ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
  have canonical := realPlaneLevelBinaryRelativeCycle_finiteLevel degree cusp character trivial
    basis cycle regular
  subst character
  have difference (pair : RealPlaneGroup × RealPlaneGroup) :
      (canonicalDifference degree cusp basis (realPlaneLevelForgetRelative degree cusp
        trivialCharacter cycle) (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle
          regular)).val pair ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
    change (cycle.val pair).val - _ ∈ _
    exact Submodule.sub_mem _ (cycle.val pair).property (canonical pair)
  have potential (matrix : BinaryRealGL) :
      canonicalPotential degree cusp basis (realPlaneLevelForgetRelative degree cusp
        trivialCharacter cycle) (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle
          regular) matrix ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
    apply latticePotential_finiteLevel
    · exact Submodule.sub_mem _ (difference _) (difference _)
    · exact Submodule.sub_mem _ (difference _) (difference _)
  exact explicitSplitPrimitive_mem realPlaneSplitting (realPlaneCuspidalRep degree cusp
    trivialCharacter) (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (fun element vector fixed => realPlaneCuspidalRep_finiteLevel degree cusp trivialCharacter
      element vector fixed) _ difference _ potential _ _ binaryTwo _ element

variable {n : ℕ}

/-- **The total source primitive has finite-level values.** -/
theorem sourceTotalPrimitive_finiteLevel (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (element : RealPlaneGroup) :
    sourceTotalPrimitive data trivial basis primitive relative regular element ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) :=
  Submodule.add_mem _
    (realPlaneLevelCanonicalPrimitive_finiteLevel n data.cusp data.chi trivial basis relative
      regular element)
    (realPlanePrimitiveExtension _ primitive element).property

/-- **The edge cochain of the total primitive is at finite level.** -/
theorem totalPrimitiveEdge_finite (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    EdgeFinite data (totalPrimitiveEdge data trivial basis primitive relative regular) := by
  intro V
  exact realPlaneCuspidalRep_finiteLevel n data.cusp data.chi _ _
    (sourceTotalPrimitive_finiteLevel data trivial basis primitive relative regular _)

theorem goodLineForm_basic (w : ℝ × ℝ) {x : RealGL3} (hx : IsBasicVertex x) :
    GoodLineForm (standardGoodLineRealArgument w * x) := by
  rcases hx with rfl | ⟨s, rfl⟩
  · exact goodLineForm_one w
  · exact goodLineForm_radical w s

theorem realPlaneCuspidalRep_inr_unimodular (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (B : BinaryRealGL) (unit : |B.val.det| = 1)
    (values : cuspidalTensorValues cusp (HomogeneousPoly n)) :
    (realPlaneCuspidalRep n cusp character).ρ (SemidirectProduct.inr B) values =
      cuspidalTensorMap cusp (realCoefficientComponent n character (planeLevi B 1))
        (cuspidalTensorTranslation cusp (atInfinity B) values) := by
  apply Subtype.ext
  funext argument
  rw [realPlaneCuspidalRep_apply, SemidirectProduct.right_inr, normPower_atInfinity_unit unit,
    one_smul, realPlaneMatrix_inr]
  rfl

/-- **The edge cochain of the total primitive is Levi equivariant.** -/
theorem totalPrimitiveEdge_levi (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    EdgeLeviEquivariant data (totalPrimitiveEdge data trivial basis primitive relative regular) := by
  intro γ w x y hx hy
  set B : BinaryRealGL :=
    binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) γ * binaryPivotSwap with hB
  have unit : |B.val.det| = 1 := conjugateLevi_unimodular γ
  have matrix : realLeviMatrix (conjugateLeviInteger γ) = B := realLeviMatrix_conjugate γ
  unfold totalPrimitiveEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [goodLineConjugateRealLevi, gsPlaneVertex_levi B _ (goodLineForm_basic w hx).corner_pos,
    gsPlaneVertex_levi B _ (goodLineForm_basic w hy).corner_pos, homogeneousOne_mul, matrix]
  exact realPlaneCuspidalRep_inr_unimodular data.cusp data.chi B unit _

end TernaryPeriodPolynomials.AnalyticClasses
