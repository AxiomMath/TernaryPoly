module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ContinuousCohomology
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryRotation (angle : Circle) : BinaryRealGL where
  val := !![(angle : ℂ).re, -(angle : ℂ).im; (angle : ℂ).im, (angle : ℂ).re]
  inv := !![(angle : ℂ).re, (angle : ℂ).im; -(angle : ℂ).im, (angle : ℂ).re]
  val_inv := by
    have norm := Circle.normSq_coe angle
    simp only [Complex.normSq_apply] at norm
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  inv_val := by
    have norm := Circle.normSq_coe angle
    simp only [Complex.normSq_apply] at norm
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

def binaryRotations : Circle →* BinaryRealGL where
  toFun := binaryRotation
  map_one' := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> simp [binaryRotation]
  map_mul' first second := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryRotation, Matrix.mul_apply,
        Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem binaryRotations_continuous : Continuous binaryRotations := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun angle : Circle =>
      !![(angle : ℂ).re, -(angle : ℂ).im; (angle : ℂ).im, (angle : ℂ).re])
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> fun_prop
  · change Continuous (fun angle : Circle =>
      !![(angle : ℂ).re, (angle : ℂ).im; -(angle : ℂ).im, (angle : ℂ).re])
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> fun_prop

local instance : MeasurableSpace Circle := borel Circle

local instance : BorelSpace Circle := ⟨rfl⟩

def binaryRotationMeasure : Measure Circle := Measure.haarMeasure ⊤

instance binaryRotationMeasure_isProbabilityMeasure : IsProbabilityMeasure binaryRotationMeasure where
  measure_univ := by
    simpa only [binaryRotationMeasure, TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle)))

instance binaryRotationMeasure_isHaarMeasure : binaryRotationMeasure.IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryRotationPrimitive (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree)) : index → cusp.H :=
  -(∫ angle, binaryHilbertEmbedding cusp basis (cycle (binaryRotations angle))
    ∂binaryRotationMeasure)

theorem binaryRotationPrimitive_spec (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (angle : Circle) :
    binaryHilbertEmbedding cusp basis (cycle (binaryRotations angle)) =
      binaryHilbertOperator cusp basis (binaryRotations angle)
        (binaryRotationPrimitive cusp basis cycle) - binaryRotationPrimitive cusp basis cycle :=
  binaryHilbertCocycle_compact_primitive cusp basis cycle continuous
    binaryRotations binaryRotations_continuous binaryRotationMeasure angle

theorem binaryRotationPrimitive_fixed (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (matrix : BinaryAdelicGL)
    (fixed : ∀ angle : Circle,
      binaryRightTranslation cusp degree matrix (cycle (binaryRotations angle)) =
        cycle (binaryRotations angle)) :
    binaryHilbertTranslation cusp matrix (binaryRotationPrimitive cusp basis cycle) =
      binaryRotationPrimitive cusp basis cycle := by
  let values : Circle → (index → cusp.H) :=
    fun angle => binaryHilbertEmbedding cusp basis (cycle (binaryRotations angle))
  have integrable : Integrable values binaryRotationMeasure :=
    (continuous.comp binaryRotations_continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace values)
  have intertwines (angle : Circle) : binaryHilbertTranslation cusp matrix (values angle) =
      values angle :=
    (binaryHilbertTranslation_intertwines cusp basis matrix (cycle (binaryRotations angle))).trans
      (congrArg (binaryHilbertEmbedding cusp basis) (fixed angle))
  have integral_fixed : binaryHilbertTranslation cusp matrix (∫ angle, values angle ∂binaryRotationMeasure) =
      ∫ angle, values angle ∂binaryRotationMeasure := by
    rw [← (binaryHilbertTranslation cusp matrix).integral_comp_comm integrable]
    simp only [intertwines]
  change binaryHilbertTranslation cusp matrix (-(∫ angle, values angle ∂binaryRotationMeasure)) =
    -(∫ angle, values angle ∂binaryRotationMeasure)
  rw [map_neg, integral_fixed]

theorem binaryRotationPrimitive_finiteLevel (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (cycle matrix) = cycle matrix)
    (element : level) (position : index) :
    cusp.π (atFinite element.val) (binaryRotationPrimitive cusp basis cycle position) =
      binaryRotationPrimitive cusp basis cycle position :=
  congrFun (binaryRotationPrimitive_fixed cusp basis cycle continuous (atFinite element.val)
    (fun angle => fixed element (binaryRotations angle))) position

end TernaryPeriodPolynomials.SphericalDetection.Helpers
