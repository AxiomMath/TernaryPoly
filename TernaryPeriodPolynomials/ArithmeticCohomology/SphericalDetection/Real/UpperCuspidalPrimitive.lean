module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperCuspidalAxisLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentSmoothAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {index : Type} [Fintype index]

theorem realUpperCuspidalAxisLifts_primitive (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp)) (unit_zero : cycle (1, 1) = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cuspidalTensorHilbertEmbedding cusp basis (cycle (Multiplicative.ofAdd point.1, Multiplicative.ofAdd point.2))))
    (fixed : ∀ first second, cycle (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero)
    (projects : ∀ coordinate element, (lifts coordinate element).element = realRadicalAxisHom coordinate element)
    (lift_fixed : ∀ coordinate parameter, (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (lift_smooth : ∀ coordinate, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter =>
      cuspidalTensorHilbertEmbedding cusp basis (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient))
    (commute : ∀ first second, Commute (lifts 0 first) (lifts 1 second)) :
    ∃ primitive : RealPlaneRadical → cuspidalTensorValues cusp (HomogeneousPoly degree),
      (∀ element, primitive element ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding cusp basis (primitive (Multiplicative.ofAdd point))) ∧
      ∀ first second,
        cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
          ((realUpperRadicalRep degree).ρ first) (primitive second) - primitive (first * second) + primitive first = cycle (first, second) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  let splitting := ((lifts 0).noncommCoprod (lifts 1) commute).comp realRadicalCoordinatesHom
  let coefficients (element : RealPlaneRadical) : cuspidalTensorValues cusp (HomogeneousPoly degree) :=
    (splitting element).coefficient
  let embedding : realUpperCuspidalRep degree cusp →ₗ[ℂ] (index → cusp.H) := cuspidalTensorHilbertEmbedding cusp basis
  have splitting_projects (element : RealPlaneRadical) :
      twoCocycleExtensionProjection (realUpperCuspidalRep degree cusp) cycle unit_zero (splitting element) = element := by
    change (lifts 0 (Multiplicative.ofAdd (element.toAdd 0))).element *
      (lifts 1 (Multiplicative.ofAdd (element.toAdd 1))).element = element
    rw [projects, projects]
    exact realRadicalAxis_product element
  have formula (point : Fin 2 → ℝ) : coefficients (Multiplicative.ofAdd point) =
      (lifts 0 (Multiplicative.ofAdd (point 0))).coefficient +
        (realUpperCuspidalRep degree cusp).ρ (realRadicalAxis 0 (point 0)) (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient +
          cycle (realRadicalAxis 0 (point 0), realRadicalAxis 1 (point 1)) := by
    change (lifts 0 (Multiplicative.ofAdd (point 0))).coefficient +
      (realUpperCuspidalRep degree cusp).ρ (lifts 0 (Multiplicative.ofAdd (point 0))).element
        (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient +
      cycle ((lifts 0 (Multiplicative.ofAdd (point 0))).element,
        (lifts 1 (Multiplicative.ofAdd (point 1))).element) = _
    rw [projects, projects]
    rfl
  refine ⟨fun element => -coefficients element, ?_, ?_, ?_⟩
  · intro element
    apply (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).neg_mem
    change coefficients (Multiplicative.ofAdd element.toAdd) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)
    rw [formula]
    apply (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).add_mem
    · apply (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).add_mem
      · exact lift_fixed 0 (element.toAdd 0)
      · exact cuspidalTensorMap_finiteLevel cusp ((realUpperRadicalRep degree).ρ (realRadicalAxis 0 (element.toAdd 0)))
          (lifts 1 (Multiplicative.ofAdd (element.toAdd 1))).coefficient (lift_fixed 1 (element.toAdd 1))
    · exact fixed _ _
  · have first_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding cusp basis (lifts 0 (Multiplicative.ofAdd (point 0))).coefficient) :=
      (lift_smooth 0).comp (contDiff_apply ℝ ℝ 0)
    have second_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding cusp basis (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient) :=
      (lift_smooth 1).comp (contDiff_apply ℝ ℝ 1)
    have action_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        (realUpperHilbertRep degree cusp basis).ρ (realRadicalAxis 0 (point 0))
          (cuspidalTensorHilbertEmbedding cusp basis (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient)) := by
      have composed := (realNilpotentExponential_contDiff (realUpperHilbertGenerator degree cusp basis 0)
        (basisHilbertCoefficient cusp basis (upperRadicalGenerator degree 0)).continuous
        (degree + 1) (realUpperHilbertGenerator_nilpotent degree cusp basis 0)).comp
          ((contDiff_apply ℝ ℝ 0).prodMk second_smooth)
      convert composed using 1
      funext point
      exact LinearMap.congr_fun (realUpperHilbertRep_axis degree cusp basis 0 (point 0)) _
    have mixed_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis 0 (point 0), realRadicalAxis 1 (point 1)))) := by
      have input_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
          ((realRadicalAxis 0 (point 0)).toAdd, (realRadicalAxis 1 (point 1)).toAdd)) :=
        ((realRadicalAxisCoordinates_contDiff 0).comp (contDiff_apply ℝ ℝ 0)).prodMk
          ((realRadicalAxisCoordinates_contDiff 1).comp (contDiff_apply ℝ ℝ 1))
      convert regular.comp input_regular using 1
      rfl
    convert ((first_smooth.add action_smooth).add mixed_smooth).neg using 1
    funext point
    change embedding (-(splitting (Multiplicative.ofAdd point)).coefficient) = _
    rw [map_neg]
    have formula_rep : (splitting (Multiplicative.ofAdd point)).coefficient =
        (lifts 0 (Multiplicative.ofAdd (point 0))).coefficient +
          (realUpperCuspidalRep degree cusp).ρ (realRadicalAxis 0 (point 0)) (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient +
            cycle (realRadicalAxis 0 (point 0), realRadicalAxis 1 (point 1)) := formula point
    rw [formula_rep, map_add, map_add]
    rw [show embedding ((realUpperCuspidalRep degree cusp).ρ (realRadicalAxis 0 (point 0))
        (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient) =
        (realUpperHilbertRep degree cusp basis).ρ (realRadicalAxis 0 (point 0))
          (cuspidalTensorHilbertEmbedding cusp basis (lifts 1 (Multiplicative.ofAdd (point 1))).coefficient) from
      realUpperCuspidalHilbert_intertwines degree cusp basis _ _]
    rfl
  · exact twoCocycleExtension_section_boundary (realUpperCuspidalRep degree cusp) cycle unit_zero splitting splitting_projects

end TernaryPeriodPolynomials.SphericalDetection.Helpers
