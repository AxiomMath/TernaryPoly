module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.CanonicalControl
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ExplicitPrimitiveFinite

@[expose] public section


/-!
# Control of the explicit total primitive

The constructive split-extension primitive `explicitSplitPrimitive` of a relative two-cocycle `d`
of `ℝ² ⋊ GL₂(ℝ)` is a finite combination of values of `d`, of the given Levi potentials and of the
real plane action, at group elements depending continuously on the input. Hence it is controlled
when `d` and the potentials are. Applied to the canonical difference of a controlled relative
cocycle (whose Levi potentials are the explicit lattice potentials of two mixed values), this
controls the explicit canonical primitive, and with Codexiom's radical primitive the total source
primitive `sourceTotalPrimitive` of the chosen relative of a plane source cocycle.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {degree : ℕ} {cusp : CuspidalRepresentation}

local notation "PlaneRep" => realPlaneCuspidalRep degree cusp trivialCharacter

theorem LeviControlled.right {potential : BinaryRealGL → cuspidalTensorValues cusp (HomogeneousPoly
    degree)}
    (controlled : LeviControlled cusp potential) :
    OneControlled cusp (fun element => potential element.right) :=
  fun X _ _ hp => controlled X _ hp.2

theorem splitRadicalCoordinate_realPlane (element : RealPlaneGroup) :
    splitRadicalCoordinate realPlaneSplitting element = element.left := by
  have pair := splitRadicalCoordinate_pair realPlaneSplitting element.left element.right
  have decomposition : (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl element.left
      *
      realPlaneSplitting element.right = element := SemidirectProduct.inl_left_mul_inr_right element
  rwa [decomposition] at pair

/-- The potential-corrected cocycle of a controlled cocycle. -/
theorem potentialCorrected_pairControlled (cycle : RealPlaneRelative degree cusp)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree))))
    (potential : BinaryRealGL → PlaneRep) (potentialControlled : LeviControlled cusp potential)
    (potential_one : potential 1 = 0) :
    PairControlled cusp (fun pair =>
      ((potentialCorrected PlaneRep cycle potential potential_one).val pair :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  intro X _ p q hp hq
  simp only [potentialCorrected_apply]
  have right := potentialControlled.right
  exact (controlled X p q hp hq).add ((((right X q hq).plane hp).sub (right X _ (hp.mul hq))).add
    (right X p hp))

/-- The mixed primitive of a controlled cocycle. -/
theorem splitMixedPrimitive_oneControlled (cycle : RealPlaneRelative degree cusp)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    OneControlled cusp (fun element =>
      (splitMixedPrimitive realPlaneSplitting PlaneRep cycle element :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  intro X _ p hp
  have equality (element : RealPlaneGroup) :
      splitMixedPrimitive realPlaneSplitting PlaneRep cycle element =
        cycle.val (SemidirectProduct.inl element.left, SemidirectProduct.inr element.right) := by
    unfold splitMixedPrimitive
    rw [splitRadicalCoordinate_realPlane]
    rfl
  simp only [equality]
  exact controlled X _ _ hp.left_inl hp.right_inr

/-- The mixed-corrected cocycle of a controlled cocycle. -/
theorem mixedCorrected_pairControlled (cycle : RealPlaneRelative degree cusp)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    PairControlled cusp (fun pair =>
      ((mixedCorrected realPlaneSplitting PlaneRep cycle).val pair :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  intro X _ p q hp hq
  exact (controlled X p q hp hq).add (twoBoundaryCycle_pairControlled
    (splitMixedPrimitive_oneControlled cycle controlled) X p q hp hq)

/-- **The explicit split primitive of a controlled cocycle with controlled potentials.** -/
theorem explicitSplitPrimitive_oneControlled (cycle : RealPlaneRelative degree cusp)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree))))
    (potential : BinaryRealGL → PlaneRep) (potentialControlled : LeviControlled cusp potential)
    (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        PlaneRep) (potential levi) = splitEdgeCycle realPlaneSplitting PlaneRep levi cycle)
    (central : BinaryRealGL) (scalar : ℂ) :
    OneControlled cusp (fun element =>
      (explicitSplitPrimitive realPlaneSplitting PlaneRep cycle potential potential_one boundary
        central scalar element : cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  intro X _ p hp
  have first := potentialCorrected_pairControlled cycle controlled potential potentialControlled
    potential_one
  have second := mixedCorrected_pairControlled _ first
  have levi : Controlled cusp (fun x => ((explicitLeviPrimitive realPlaneSplitting PlaneRep cycle
      potential potential_one boundary central scalar (p x).right).val :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
    change Controlled cusp (fun x => (scalar - 1)⁻¹ •
      ((mixedCorrected realPlaneSplitting PlaneRep
          (potentialCorrected PlaneRep cycle potential potential_one)).val
          (SemidirectProduct.inr central, SemidirectProduct.inr (p x).right) -
        (mixedCorrected realPlaneSplitting PlaneRep
          (potentialCorrected PlaneRep cycle potential potential_one)).val
          (SemidirectProduct.inr (p x).right, SemidirectProduct.inr central)))
    exact ((second X _ _ (planeContinuous_const _) hp.right_inr).sub
      (second X _ _ hp.right_inr (planeContinuous_const _))).const_smul _
  exact (levi.sub (splitMixedPrimitive_oneControlled _ first X p hp)).sub
    (potentialControlled.right X p hp)

variable {index : Type} [Fintype index] (basis : Module.Basis index ℂ (HomogeneousPoly degree))

theorem canonicalDifference_pairControlled (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    PairControlled cusp (fun pair =>
      ((canonicalDifference degree cusp basis cycle regular).val pair :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) :=
  controlled.sub (realPlaneBinaryRelativeCycle_pairControlled basis cycle regular controlled)

theorem canonicalPotential_leviControlled (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    LeviControlled cusp (canonicalPotential degree cusp basis cycle regular) := by
  intro X _ B hB
  have difference := canonicalDifference_pairControlled basis cycle regular controlled
  change Controlled cusp (fun x => latticePotential degree cusp
    (realPlaneMixedCocycle degree cusp (B x) (canonicalDifference degree cusp basis cycle regular)
      (realRadicalAxis 0 1))
    (realPlaneMixedCocycle degree cusp (B x) (canonicalDifference degree cusp basis cycle regular)
      (realRadicalAxis 1 1)))
  unfold latticePotential
  exact ((mixedCocycle_controlled _ difference hB continuous_const).map_const
    (homogeneousBasis degree) _).add
    ((mixedCocycle_controlled _ difference hB continuous_const).map_const (homogeneousBasis degree)
        _)

/-- **The explicit canonical primitive of a controlled relative cocycle is controlled.** -/
theorem realPlaneCanonicalPrimitive_oneControlled (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    OneControlled cusp (fun element =>
      (realPlaneCanonicalPrimitive degree cusp basis cycle regular element :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) :=
  explicitSplitPrimitive_oneControlled _ (canonicalDifference_pairControlled basis cycle regular
      controlled)
    _ (canonicalPotential_leviControlled basis cycle regular controlled) _ _ _ _

end TernaryPeriodPolynomials.EdgeControl
