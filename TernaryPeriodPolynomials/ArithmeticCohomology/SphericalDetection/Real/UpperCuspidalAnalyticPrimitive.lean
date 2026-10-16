module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.AnalyticRadicalAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RadicalPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realUpperCuspidalAxisPrimitive (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp)) (unit_zero : cycle (1, 1) = 0)
    (lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero) :
    RealPlaneRadical → cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  let coefficients : Fin 2 → ℝ → cuspidalTensorValues cusp (HomogeneousPoly degree) :=
    fun coordinate parameter => (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient
  let cycleValues : RealPlaneRadical × RealPlaneRadical → cuspidalTensorValues cusp (HomogeneousPoly degree) := cycle
  fun radical => -(coefficients 0 (radical.toAdd 0) +
    cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
      ((realUpperRadicalRep degree).ρ (realRadicalAxis 0 (radical.toAdd 0))) (coefficients 1 (radical.toAdd 1)) +
    cycleValues (realRadicalAxis 0 (radical.toAdd 0), realRadicalAxis 1 (radical.toAdd 1)))

theorem realUpperCuspidalAxisPrimitive_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp)) (unit_zero : cycle (1, 1) = 0)
    (lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero)
    (fixed : ∀ first second, cycle (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (lift_fixed : ∀ coordinate parameter, (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) (radical : RealPlaneRadical) :
    realUpperCuspidalAxisPrimitive degree cusp cycle unit_zero lifts radical ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  dsimp only [realUpperCuspidalAxisPrimitive]
  apply (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).neg_mem
  apply (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).add_mem
  · apply (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).add_mem
    · exact lift_fixed 0 (radical.toAdd 0)
    · exact cuspidalTensorMap_finiteLevel cusp ((realUpperRadicalRep degree).ρ (realRadicalAxis 0 (radical.toAdd 0)))
        (lifts 1 (Multiplicative.ofAdd (radical.toAdd 1))).coefficient (lift_fixed 1 (radical.toAdd 1))
  · exact fixed _ _

theorem realUpperCuspidalAxisPrimitive_boundary (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp)) (unit_zero : cycle (1, 1) = 0)
    (lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero)
    (projects : ∀ coordinate element, (lifts coordinate element).element = realRadicalAxisHom coordinate element)
    (commute : ∀ first second, Commute (lifts 0 first) (lifts 1 second)) (first second : RealPlaneRadical) :
    cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
        ((realUpperRadicalRep degree).ρ first) (realUpperCuspidalAxisPrimitive degree cusp cycle unit_zero lifts second) -
        realUpperCuspidalAxisPrimitive degree cusp cycle unit_zero lifts (first * second) +
        realUpperCuspidalAxisPrimitive degree cusp cycle unit_zero lifts first = cycle (first, second) := by
  let splitting := ((lifts 0).noncommCoprod (lifts 1) commute).comp realRadicalCoordinatesHom
  have splitting_projects (element : RealPlaneRadical) :
      twoCocycleExtensionProjection (realUpperCuspidalRep degree cusp) cycle unit_zero (splitting element) = element := by
    change (lifts 0 (Multiplicative.ofAdd (element.toAdd 0))).element *
      (lifts 1 (Multiplicative.ofAdd (element.toAdd 1))).element = element
    rw [projects, projects]
    exact realRadicalAxis_product element
  have formula (radical : RealPlaneRadical) :
      realUpperCuspidalAxisPrimitive degree cusp cycle unit_zero lifts radical = -(splitting radical).coefficient := by
    change _ = -((lifts 0 (Multiplicative.ofAdd (radical.toAdd 0))).coefficient +
      (realUpperCuspidalRep degree cusp).ρ (lifts 0 (Multiplicative.ofAdd (radical.toAdd 0))).element
        (lifts 1 (Multiplicative.ofAdd (radical.toAdd 1))).coefficient +
      cycle ((lifts 0 (Multiplicative.ofAdd (radical.toAdd 0))).element,
        (lifts 1 (Multiplicative.ofAdd (radical.toAdd 1))).element))
    rw [projects, projects]
    rfl
  simp only [formula]
  exact twoCocycleExtension_section_boundary (realUpperCuspidalRep degree cusp) cycle unit_zero splitting splitting_projects first second

theorem realUpperCuspidalAxisPrimitive_orbital_analyticAt {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp)) (unit_zero : cycle (1, 1) = 0)
    (lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero)
    (analytic : ∀ center : (Fin 2 → ℝ) × (Fin 2 → ℝ), AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (Multiplicative.ofAdd point.2.1, Multiplicative.ofAdd point.2.2)))) (1, center))
    (lift_analytic : ∀ coordinate center, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (lifts coordinate (Multiplicative.ofAdd point.2)).coefficient)) (1, center))
    (center : Fin 2 → ℝ) :
    AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis
          (realUpperCuspidalAxisPrimitive degree cusp cycle unit_zero lifts (Multiplicative.ofAdd point.2)))) (1, center) := by
  have axis_analytic (coordinate : Fin 2) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (Fin 2 → ℝ) => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (lifts coordinate (Multiplicative.ofAdd (point.2 coordinate))).coefficient)) (1, center) := by
    have input_regular : ContDiff ℝ ⊤ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) => (point.1, point.2 coordinate)) :=
      contDiff_fst.prodMk ((contDiff_apply ℝ ℝ coordinate).comp contDiff_snd)
    exact (lift_analytic coordinate (center coordinate)).comp
      (f := fun point : BinaryRealMatrix × (Fin 2 → ℝ) => (point.1, point.2 coordinate))
      (x := (1, center)) input_regular.contDiffAt.analyticAt
  have action_analytic := realUpperCuspidalAxisAction_orbital_analyticAt degree cusp basis 0
    (fun point : Fin 2 → ℝ => point 0)
    (fun point : Fin 2 → ℝ => (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient) center
    (contDiff_apply ℝ ℝ 0).contDiffAt.analyticAt (axis_analytic 1)
  have input_regular : ContDiff ℝ ⊤ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      (point.1, ((realRadicalAxis 0 (point.2 0)).toAdd, (realRadicalAxis 1 (point.2 1)).toAdd))) :=
    contDiff_fst.prodMk
      (((realRadicalAxisCoordinates_contDiff_top 0).comp ((contDiff_apply ℝ ℝ 0).comp contDiff_snd)).prodMk
        ((realRadicalAxisCoordinates_contDiff_top 1).comp ((contDiff_apply ℝ ℝ 1).comp contDiff_snd)))
  have mixed_analytic := (analytic ((realRadicalAxis 0 (center 0)).toAdd, (realRadicalAxis 1 (center 1)).toAdd)).comp
    (x := (1, center))
    (f := fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      (point.1, ((realRadicalAxis 0 (point.2 0)).toAdd, (realRadicalAxis 1 (point.2 1)).toAdd)))
    input_regular.contDiffAt.analyticAt
  convert (((axis_analytic 0).add action_analytic).add mixed_analytic).neg using 1
  funext point
  let embedding : realUpperCuspidalRep degree cusp →ₗ[ℂ] (index → cusp.H) := cuspidalTensorHilbertEmbedding cusp basis
  change binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
    (embedding (-((lifts 0 (Multiplicative.ofAdd (point.2 0))).coefficient +
      (realUpperCuspidalRep degree cusp).ρ (realRadicalAxis 0 (point.2 0)) (lifts 1 (Multiplicative.ofAdd (point.2 1))).coefficient +
      cycle (realRadicalAxis 0 (point.2 0), realRadicalAxis 1 (point.2 1))))) = _
  rw [map_neg, map_add, map_add, map_neg, map_add, map_add]
  rfl

theorem realUpperCuspidalTwoCocycle_axis_orbital_analyticAt {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp))
    (analytic : ∀ center : (Fin 2 → ℝ) × (Fin 2 → ℝ), AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (Multiplicative.ofAdd point.2.1, Multiplicative.ofAdd point.2.2)))) (1, center))
    (coordinate : Fin 2) (first : ℝ) :
    AnalyticAt ℝ (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
        (cuspidalTensorHilbertEmbedding cusp basis
          (cycle (realRadicalAxis coordinate point.1.2, realRadicalAxis coordinate point.2)))) ((1, first), 0) := by
  have input_regular : ContDiff ℝ ⊤ (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
      (point.1.1, ((realRadicalAxis coordinate point.1.2).toAdd, (realRadicalAxis coordinate point.2).toAdd))) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      (((realRadicalAxisCoordinates_contDiff_top coordinate).comp (contDiff_snd.comp contDiff_fst)).prodMk
        ((realRadicalAxisCoordinates_contDiff_top coordinate).comp contDiff_snd))
  have composed := (analytic ((realRadicalAxis coordinate first).toAdd, (realRadicalAxis coordinate 0).toAdd)).comp
    (f := fun point : (BinaryRealMatrix × ℝ) × ℝ =>
      (point.1.1, ((realRadicalAxis coordinate point.1.2).toAdd, (realRadicalAxis coordinate point.2).toAdd)))
    (x := ((1, first), 0)) input_regular.contDiffAt.analyticAt
  convert composed using 1
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
