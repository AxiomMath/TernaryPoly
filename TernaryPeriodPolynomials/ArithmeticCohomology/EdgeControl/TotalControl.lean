module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.ExplicitControl
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay

@[expose] public section


/-!
# Control of the total source primitive of a chosen relative representative

For a plane source cocycle and Codexiom's chosen relative representative
`relative = sourcePlaneLevelGroupCocycle − δ(radical primitive extension)`, with the radical
primitive having jointly analytic Hilbert orbits, the relative cocycle is controlled (the source
part by the source-cochain cusp vectors, the primitive part by the stage realizations), hence so
are the explicit canonical primitive and the total primitive `sourceTotalPrimitive`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ} {index : Type} [Fintype index]

theorem realPlaneCuspidalRep_character (cusp : CuspidalRepresentation) {character :
    RankOneCharacter}
    (trivial : character = trivialCharacter) (element : RealPlaneGroup)
    (values : cuspidalTensorValues cusp (HomogeneousPoly n)) :
    ((realPlaneCuspidalRep n cusp character).ρ element values :
        cuspidalTensorValues cusp (HomogeneousPoly n)) =
      ((realPlaneCuspidalRep n cusp trivialCharacter).ρ element values :
        cuspidalTensorValues cusp (HomogeneousPoly n)) := by
  subst trivial
  rfl

/-- **The plane action for a trivial character along continuous paths preserves control.** -/
theorem Controlled.plane_character {X : Type*} [TopologicalSpace X] {cusp : CuspidalRepresentation}
    {character : RankOneCharacter} (trivial : character = trivialCharacter)
    {family : X → cuspidalTensorValues cusp (HomogeneousPoly n)} (controlled : Controlled cusp
        family)
    {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    Controlled cusp (fun x => ((realPlaneCuspidalRep n cusp character).ρ (p x) (family x) :
      cuspidalTensorValues cusp (HomogeneousPoly n))) := by
  simp only [realPlaneCuspidalRep_character cusp trivial]
  exact controlled.plane hp

/-- **The radical primitive extension is controlled.** -/
theorem primitiveExtension_oneControlled (data : InducingData n)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (primitive (Multiplicative.ofAdd point.2)).val)) (1, center)) :
    OneControlled data.cusp (fun element =>
      ((realPlanePrimitiveExtension _ primitive element).val :
        cuspidalTensorValues data.cusp (HomogeneousPoly n))) := by
  intro X _ p hp
  have controlled := controlled_of_hilbertAnalytic data.cusp (continuousStages data) basis
    (fun v => (primitive (Multiplicative.ofAdd v)).val) (fun v => (primitive _).property) analytic
    hp.1
  exact controlled

/-- **Codexiom's chosen relative representative is controlled.** -/
theorem chosenRelative_pairControlled (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive)) :
    PairControlled data.cusp (fun pair =>
      ((relative.val pair).val : cuspidalTensorValues data.cusp (HomogeneousPoly n))) := by
  intro X _ p q hp hq
  have value (first second : RealPlaneGroup) :
      ((relative.val (first, second)).val : cuspidalTensorValues data.cusp (HomogeneousPoly n)) =
        (show cuspidalTensorValues data.cusp (HomogeneousPoly n) from
          sourcePlaneGroupCocycle data source cocycle (first, second)) -
        ((show cuspidalTensorValues data.cusp (HomogeneousPoly n) from
          (realPlaneCuspidalRep n data.cusp data.chi).ρ first
            (realPlanePrimitiveExtension _ primitive second).val) -
          (realPlanePrimitiveExtension _ primitive (first * second)).val +
          (realPlanePrimitiveExtension _ primitive first).val) := by
    rw [formula]
    rfl
  simp only [value]
  have extension := primitiveExtension_oneControlled data basis primitive analytic
  exact (sourcePlaneGroupCocycle_controlled data source cocycle hp hq).sub
    ((((extension X q hq).plane_character trivial hp).sub (extension X _ (hp.mul hq))).add
      (extension X p hp))

/-- The level canonical primitive of a controlled relative cocycle is controlled. -/
theorem realPlaneLevelCanonicalPrimitive_oneControlled (cusp : CuspidalRepresentation)
    {character : RankOneCharacter} (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n cusp character))
    (regular : RealPlaneLevelMixedRegular n cusp character basis relative)
    (controlled : PairControlled cusp (fun pair =>
      ((relative.val pair).val : cuspidalTensorValues cusp (HomogeneousPoly n)))) :
    OneControlled cusp (fun element =>
      (realPlaneLevelCanonicalPrimitive n cusp character trivial basis relative regular element :
        cuspidalTensorValues cusp (HomogeneousPoly n))) := by
  subst trivial
  exact realPlaneCanonicalPrimitive_oneControlled basis _
    (realPlaneLevelMixedCocycle_differentiable n cusp basis relative regular) controlled

/-- **The total source primitive of a chosen relative representative is controlled.** -/
theorem sourceTotalPrimitive_oneControlled (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    OneControlled data.cusp (fun element =>
      (sourceTotalPrimitive data trivial basis primitive relative regular element :
        cuspidalTensorValues data.cusp (HomogeneousPoly n))) :=
  (realPlaneLevelCanonicalPrimitive_oneControlled data.cusp trivial basis relative regular
    (chosenRelative_pairControlled data trivial basis source cocycle primitive analytic relative
      formula)).add (primitiveExtension_oneControlled data basis primitive analytic)

end TernaryPeriodPolynomials.EdgeControl
