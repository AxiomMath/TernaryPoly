module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ExplicitSplitPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.RadicalExplicitPotential

@[expose] public section


/-!
# An explicit primitive comparing a real-plane relative cocycle with its canonical form

Codexiom's `realPlaneBinaryRelativeCycle_exists_primitive` produces the primitive relating a
regular relative two-cocycle of the real plane group `ℝ² ⋊ GL₂(ℝ)` to the canonical relative cocycle
of its binary cocycle by an abstract `H2π_eq_zero_iff`. Here the same identity is proved with an
explicit primitive: the edges of the difference are exact radical one-cocycles, whose explicit
potentials (`radicalCocyclePotential`) feed the constructive split-extension primitive
(`explicitSplitPrimitive`), with the central element `2 · 1` acting on the radical invariants by
`2 ^ (degree + 1) ≠ 1`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {index : Type} [Fintype index]
variable (degree : ℕ) (cusp : CuspidalRepresentation)
  (basis : Module.Basis index ℂ (HomogeneousPoly degree))

/-- The real-plane relative cocycles. -/
abbrev RealPlaneRelative :=
  relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
    (realPlaneCuspidalRep degree cusp trivialCharacter)

/-- Regularity of the mixed cocycles along the radical axes (Codexiom's hypothesis). -/
abbrev RealPlaneRegular (cycle : RealPlaneRelative degree cusp) : Prop :=
  ∀ matrix coordinate, DifferentiableAt ℝ
    (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
      (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0

/-- The difference of a regular relative cocycle and its canonical binary relative cocycle. -/
def canonicalDifference (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle) :
    RealPlaneRelative degree cusp :=
  cycle - realPlaneBinaryRelativeCycle degree cusp basis cycle regular

theorem canonicalDifference_edge_zero (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (matrix : BinaryRealGL) :
    groupCohomology.H1π _ (splitEdgeCycle realPlaneSplitting
      (realPlaneCuspidalRep degree cusp trivialCharacter) matrix
      (canonicalDifference degree cusp basis cycle regular)) = 0 := by
  have edge := congrArg (fun cocycle => cocycle matrix)
    (realPlaneBinaryRelativeCycle_edge degree cusp basis cycle regular)
  change groupCohomology.H1π _ (splitEdgeCycle realPlaneSplitting _ matrix
      (realPlaneBinaryRelativeCycle degree cusp basis cycle regular)) =
    groupCohomology.H1π _ (splitEdgeCycle realPlaneSplitting _ matrix cycle) at edge
  have split := (splitEdgeCycle realPlaneSplitting
    (realPlaneCuspidalRep degree cusp trivialCharacter) matrix).map_sub cycle
      (realPlaneBinaryRelativeCycle degree cusp basis cycle regular)
  unfold canonicalDifference
  erw [split, map_sub, edge, sub_self]

/-- The explicit Levi potentials of the canonical difference. -/
def canonicalPotential (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (matrix : BinaryRealGL) : realPlaneCuspidalRep degree cusp trivialCharacter :=
  radicalCocyclePotential degree cusp
    (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix
      (canonicalDifference degree cusp basis cycle regular))

theorem canonicalPotential_one (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle) :
    canonicalPotential degree cusp basis cycle regular 1 = 0 := by
  unfold canonicalPotential radicalCocyclePotential radicalCocycleValue
  rw [splitEdgeCycle_one]
  exact latticePotential_zero degree cusp

theorem canonicalPotential_boundary (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (matrix : BinaryRealGL) :
    oneBoundaryCycle (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneCuspidalRep degree cusp trivialCharacter))
        (canonicalPotential degree cusp basis cycle regular matrix) =
      splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix
        (canonicalDifference degree cusp basis cycle regular) :=
  radicalCocyclePotential_boundary degree cusp _
    (canonicalDifference_edge_zero degree cusp basis cycle regular matrix)

/-- The central element `2 · 1` of `GL₂(ℝ)`. -/
def binaryTwo : BinaryRealGL :=
  GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (2 : ℝ) (by norm_num))

/-- **The explicit canonical primitive.** -/
def realPlaneCanonicalPrimitive (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle) :
    RealPlaneGroup → realPlaneCuspidalRep degree cusp trivialCharacter :=
  explicitSplitPrimitive realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter)
    (canonicalDifference degree cusp basis cycle regular)
    (canonicalPotential degree cusp basis cycle regular)
    (canonicalPotential_one degree cusp basis cycle regular)
    (canonicalPotential_boundary degree cusp basis cycle regular) binaryTwo
    ((2 : ℂ) ^ (degree + 1))

/-- **A regular relative cocycle is its canonical binary relative cocycle plus the coboundary of the
explicit canonical primitive.** -/
theorem realPlaneBinaryRelativeCycle_explicit
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle) :
    cycle.val = (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val +
      twoBoundaryCycle (realPlaneCuspidalRep degree cusp trivialCharacter)
        (realPlaneCanonicalPrimitive degree cusp basis cycle regular) := by
  have explicit := relativeTwoCocycle_eq_explicitBoundary realPlaneSplitting
    (realPlaneCuspidalRep degree cusp trivialCharacter)
    (canonicalDifference degree cusp basis cycle regular)
    (canonicalPotential degree cusp basis cycle regular)
    (canonicalPotential_one degree cusp basis cycle regular)
    (canonicalPotential_boundary degree cusp basis cycle regular) binaryTwo
    (GeneralLinearGroup.scalar_commute _) ((2 : ℂ) ^ (degree + 1))
    (by exact_mod_cast ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by omega : degree + 1 ≠ 0)))
    (fun vector => by
      have value := realPlaneInvariant_positive_scalar degree cusp central_positive
        (Units.mk0 (2 : ℝ) (by norm_num)) (by norm_num) vector
      have two : (((Units.mk0 (2 : ℝ) (by norm_num) : ℝˣ) : ℝ) : ℂ) = 2 := by norm_num
      rw [two] at value
      exact value)
  have key : twoBoundaryCycle (realPlaneCuspidalRep degree cusp trivialCharacter)
      (realPlaneCanonicalPrimitive degree cusp basis cycle regular) =
      cycle.val - (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val :=
    explicit.symm
  rw [key]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
