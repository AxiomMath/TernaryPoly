module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REEuler
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.LatticeMeasure

@[expose] public section


/-!
# R-e: The Haar Jacobian of an affine map of `𝔸_f²`

`integral_finiteAffine`: for ideles `α₁, α₃` and `β, s, t`, `∫ G(α₁v₁+βv₂+s, α₃v₂+t) dv = |α₁|⁻¹|α₃|⁻¹ ∫ G` (a scaling, a shear and a translation; Haar uniqueness and the lattice measures).

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- Multiplication by an idele scales the finite Haar measure by the inverse norm. -/
theorem finiteMeasure_map_mulLeft (α : FiniteAdelesˣ) :
    Measure.map (fun x : FiniteAdeles => α.val * x) finiteMeasure =
      ((adeleNorm (Norm.finiteAdeleUnit α⁻¹) : ℝ≥0) : ℝ≥0∞) • finiteMeasure := by
  have mapped : (Measure.map (ContinuousAddEquiv.mulLeft α) finiteMeasure).IsAddHaarMeasure :=
    (ContinuousAddEquiv.mulLeft α).isAddHaarMeasure_map finiteMeasure
  have unique := Measure.addHaarMeasure_unique (Measure.map (ContinuousAddEquiv.mulLeft α) finiteMeasure)
    finiteUnitCompact
  have measurable : Measurable (ContinuousAddEquiv.mulLeft α : FiniteAdeles → FiniteAdeles) :=
    (ContinuousAddEquiv.mulLeft α).continuous.measurable
  have value : Measure.map (ContinuousAddEquiv.mulLeft α) finiteMeasure (finiteUnitCompact : Set FiniteAdeles) =
      ((adeleNorm (Norm.finiteAdeleUnit α⁻¹) : ℝ≥0) : ℝ≥0∞) := by
    change Measure.map (ContinuousAddEquiv.mulLeft α) finiteMeasure (Set.range integralEmbedding) = _
    rw [Measure.map_apply measurable integralLattice_isOpen.measurableSet,
      ← FiniteLatticeMeasure.lattice_measure α⁻¹]
    congr 1
    ext x
    simp only [Set.mem_preimage, FiniteFourier.lattice, Set.mem_range]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hi' : integralEmbedding i = α.val * x := hi
      rw [hi', Units.inv_mul_cancel_left]
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      change integralEmbedding i = α.val * x
      rw [← hi, Units.mul_inv_cancel_left]
  rw [value] at unique
  exact unique

/-- The scaling constant of an idele on `𝔸_f`. -/
def scaleConstant (α : FiniteAdelesˣ) : ℝ≥0∞ := ((adeleNorm (Norm.finiteAdeleUnit α⁻¹) : ℝ≥0) : ℝ≥0∞)

/-- The shear `(w₁, w₂) ↦ (w₁ + c w₂, w₂)` as a measurable equivalence. -/
def finiteShear (c : FiniteAdeles) : (FiniteAdeles × FiniteAdeles) ≃ᵐ (FiniteAdeles × FiniteAdeles) where
  toFun p := (p.1 + c * p.2, p.2)
  invFun p := (p.1 - c * p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun :=
    ((continuous_fst.add (continuous_const.mul continuous_snd)).prodMk continuous_snd).measurable
  measurable_invFun :=
    ((continuous_fst.sub (continuous_const.mul continuous_snd)).prodMk continuous_snd).measurable

theorem finiteShear_measurePreserving (c : FiniteAdeles) :
    MeasurePreserving (finiteShear c) (finiteMeasure.prod finiteMeasure) (finiteMeasure.prod finiteMeasure) := by
  have swap := (Measure.measurePreserving_swap (μ := finiteMeasure) (ν := finiteMeasure))
  have skew : MeasurePreserving (fun p : FiniteAdeles × FiniteAdeles => (p.1, p.2 + c * p.1))
      (finiteMeasure.prod finiteMeasure) (finiteMeasure.prod finiteMeasure) := by
    have base := MeasurePreserving.skew_product (MeasurePreserving.id finiteMeasure)
      (g := fun a b : FiniteAdeles => b + c * a) (μc := finiteMeasure) (μd := finiteMeasure)
      (by fun_prop) (Eventually.of_forall fun a => (measurePreserving_add_right finiteMeasure (c * a)).map_eq)
    exact base
  have composite := swap.comp (skew.comp swap)
  convert composite using 1
  funext p
  simp [finiteShear]

/-- Coordinatewise multiplication by two ideles. -/
def finiteScale (α₁ α₃ : FiniteAdelesˣ) : (FiniteAdeles × FiniteAdeles) ≃ᵐ (FiniteAdeles × FiniteAdeles) :=
  (ContinuousAddEquiv.mulLeft α₁).toHomeomorph.toMeasurableEquiv.prodCongr
    (ContinuousAddEquiv.mulLeft α₃).toHomeomorph.toMeasurableEquiv

theorem finiteScale_apply (α₁ α₃ : FiniteAdelesˣ) (v : FiniteAdeles × FiniteAdeles) :
    finiteScale α₁ α₃ v = (α₁.val * v.1, α₃.val * v.2) := rfl

theorem finiteScale_map (α₁ α₃ : FiniteAdelesˣ) :
    Measure.map (finiteScale α₁ α₃) (finiteMeasure.prod finiteMeasure) =
      (scaleConstant α₁ * scaleConstant α₃) • finiteMeasure.prod finiteMeasure := by
  have first := finiteMeasure_map_mulLeft α₁
  have second := finiteMeasure_map_mulLeft α₃
  have product := Measure.map_prod_map finiteMeasure finiteMeasure
    (f := fun x : FiniteAdeles => α₁.val * x) (g := fun x : FiniteAdeles => α₃.val * x)
    (ContinuousAddEquiv.mulLeft α₁).continuous.measurable (ContinuousAddEquiv.mulLeft α₃).continuous.measurable
  change Measure.map (Prod.map (fun x : FiniteAdeles => α₁.val * x) (fun x : FiniteAdeles => α₃.val * x))
    (finiteMeasure.prod finiteMeasure) = _
  rw [← product, first, second, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rfl

/-- The affine map `(v₁, v₂) ↦ (α₁ v₁ + β v₂ + s, α₃ v₂ + t)`. -/
def finiteAffine (α₁ α₃ : FiniteAdelesˣ) (β s t : FiniteAdeles) :
    (FiniteAdeles × FiniteAdeles) ≃ᵐ (FiniteAdeles × FiniteAdeles) :=
  (finiteScale α₁ α₃).trans ((finiteShear (β * (α₃⁻¹).val)).trans (MeasurableEquiv.addRight (s, t)))

theorem finiteAffine_apply (α₁ α₃ : FiniteAdelesˣ) (β s t : FiniteAdeles) (v : FiniteAdeles × FiniteAdeles) :
    finiteAffine α₁ α₃ β s t v = (α₁.val * v.1 + β * v.2 + s, α₃.val * v.2 + t) := by
  change (α₁.val * v.1 + β * (α₃⁻¹).val * (α₃.val * v.2) + s, α₃.val * v.2 + t) = _
  rw [mul_assoc, ← mul_assoc (α₃⁻¹).val, Units.inv_mul, one_mul]

theorem finiteAffine_map (α₁ α₃ : FiniteAdelesˣ) (β s t : FiniteAdeles) :
    Measure.map (finiteAffine α₁ α₃ β s t) (finiteMeasure.prod finiteMeasure) =
      (scaleConstant α₁ * scaleConstant α₃) • finiteMeasure.prod finiteMeasure := by
  have shear := (finiteShear_measurePreserving (β * (α₃⁻¹).val))
  have translate : MeasurePreserving (MeasurableEquiv.addRight ((s, t) : FiniteAdeles × FiniteAdeles))
      (finiteMeasure.prod finiteMeasure) (finiteMeasure.prod finiteMeasure) :=
    measurePreserving_add_right (finiteMeasure.prod finiteMeasure) ((s, t) : FiniteAdeles × FiniteAdeles)
  change Measure.map ((MeasurableEquiv.addRight ((s, t) : FiniteAdeles × FiniteAdeles)) ∘
    ((finiteShear (β * (α₃⁻¹).val)) ∘ (finiteScale α₁ α₃))) (finiteMeasure.prod finiteMeasure) = _
  rw [← Measure.map_map (MeasurableEquiv.addRight _).measurable
    ((finiteShear _).measurable.comp (finiteScale α₁ α₃).measurable),
    ← Measure.map_map (finiteShear _).measurable (finiteScale α₁ α₃).measurable,
    finiteScale_map, Measure.map_smul _ (finiteShear _).measurable.aemeasurable, shear.map_eq,
    Measure.map_smul _ (MeasurableEquiv.addRight _).measurable.aemeasurable, translate.map_eq]

theorem integral_finiteAffine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α₁ α₃ : FiniteAdelesˣ) (β s t : FiniteAdeles) (G : FiniteAdeles × FiniteAdeles → E) :
    (∫ v, G (α₁.val * v.1 + β * v.2 + s, α₃.val * v.2 + t) ∂(finiteMeasure.prod finiteMeasure)) =
      (scaleConstant α₁ * scaleConstant α₃).toReal • ∫ u, G u ∂(finiteMeasure.prod finiteMeasure) := by
  have transport := integral_map_equiv (finiteAffine α₁ α₃ β s t) G (μ := finiteMeasure.prod finiteMeasure)
  rw [finiteAffine_map, integral_smul_measure] at transport
  simp_rw [finiteAffine_apply] at transport
  exact transport.symm

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
