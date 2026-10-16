module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Haar
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-!
# (C), step 4: the adelic plane `𝔸² = (ℝ × 𝔸_f)²` as (finite part) × (real part)

Formalized by Claude Sonnet 5.5.
Paper: (`ar:eq:intertwiner`:
"Equivalently this is the product of its real integral and its finite congruence integrals when the datum is
factorizable").

The Haar measure of `𝔸²` is `radicalMeasure = (Lebesgue × finiteMeasure)²` (`finiteMeasure ẐΣ = 1`).
* `radicalEquiv : 𝔸² ≃ᵐ 𝔸_f² × ℝ²` regroups the coordinates and is measure preserving
  (`radicalEquiv_measurePreserving`) for `(finiteMeasure × finiteMeasure) × Lebesgue(Fin 2 → ℝ)`.
* `integral_factorizable`: for a datum `(σ, w) ↦ Ff(σ) • Fr(w)` the integral over `𝔸²` is the product of the finite
  and the real integral.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- Regrouping `(ℝ × 𝔸_f) × (ℝ × 𝔸_f)` into `(ℝ × ℝ) × (𝔸_f × 𝔸_f)`. -/
def rearrEquiv : (Adeles × Adeles) ≃ᵐ (ℝ × ℝ) × (FiniteAdeles × FiniteAdeles) :=
  (MeasurableEquiv.prodAssoc).trans <|
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl FiniteAdeles) MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodAssoc.symm))).trans <|
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm).trans <|
  MeasurableEquiv.prodAssoc.symm

theorem rearrEquiv_apply (u : Adeles × Adeles) :
    rearrEquiv u = ((u.1.1, u.2.1), (u.1.2, u.2.2)) := rfl

theorem rearr_measurePreserving :
    MeasurePreserving rearrEquiv radicalMeasure
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (finiteMeasure.prod finiteMeasure)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : Adeles × Adeles ≃ᵐ ℝ × FiniteAdeles × (ℝ × FiniteAdeles))
      radicalMeasure ((volume : Measure ℝ).prod (finiteMeasure.prod ((volume : Measure ℝ).prod finiteMeasure))) :=
    measurePreserving_prodAssoc (volume : Measure ℝ) finiteMeasure ((volume : Measure ℝ).prod finiteMeasure)
  have h2 : MeasurePreserving
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl FiniteAdeles) MeasurableEquiv.prodComm).trans
        (MeasurableEquiv.prodAssoc.symm) : FiniteAdeles × (ℝ × FiniteAdeles) ≃ᵐ (FiniteAdeles × FiniteAdeles) × ℝ)
      (finiteMeasure.prod ((volume : Measure ℝ).prod finiteMeasure))
      ((finiteMeasure.prod finiteMeasure).prod (volume : Measure ℝ)) := by
    have a := (MeasurePreserving.id (finiteMeasure : Measure FiniteAdeles)).prod
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (finiteMeasure : Measure FiniteAdeles)))
    have b := (measurePreserving_prodAssoc (finiteMeasure : Measure FiniteAdeles) finiteMeasure (volume : Measure ℝ)).symm
      MeasurableEquiv.prodAssoc
    exact b.comp a
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl FiniteAdeles) MeasurableEquiv.prodComm).trans
          (MeasurableEquiv.prodAssoc.symm)) : ℝ × (FiniteAdeles × (ℝ × FiniteAdeles)) ≃ᵐ ℝ × ((FiniteAdeles × FiniteAdeles) × ℝ))
      ((volume : Measure ℝ).prod (finiteMeasure.prod ((volume : Measure ℝ).prod finiteMeasure)))
      ((volume : Measure ℝ).prod ((finiteMeasure.prod finiteMeasure).prod (volume : Measure ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod h2
  have h4 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm :
      ℝ × ((FiniteAdeles × FiniteAdeles) × ℝ) ≃ᵐ ℝ × (ℝ × (FiniteAdeles × FiniteAdeles)))
      ((volume : Measure ℝ).prod ((finiteMeasure.prod finiteMeasure).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (finiteMeasure.prod finiteMeasure))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_swap (μ := finiteMeasure.prod finiteMeasure) (ν := (volume : Measure ℝ)))
  have h5 := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (finiteMeasure.prod finiteMeasure)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp h1))

/-- The finite part first, then the real part `(w₀, w₁) ∈ ℝ²` as a vector. -/
def radicalEquiv : (Adeles × Adeles) ≃ᵐ (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ) :=
  (rearrEquiv.trans MeasurableEquiv.prodComm).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.finTwoArrow).symm)

theorem radicalEquiv_apply (u : Adeles × Adeles) :
    radicalEquiv u = ((u.1.2, u.2.2), ![u.1.1, u.2.1]) := rfl

theorem radicalEquiv_measurePreserving :
    MeasurePreserving radicalEquiv radicalMeasure
      ((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) := by
  have h1 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ).prod (volume : Measure ℝ))
    (ν := finiteMeasure.prod finiteMeasure)).comp rearr_measurePreserving
  have h2 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  exact (MeasurePreserving.id (finiteMeasure.prod finiteMeasure)).prod h2 |>.comp h1

variable {E : Type*} [NormedAddCommGroup E]

theorem radical_integral_eq [NormedSpace ℝ E] (G : (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ) → E) :
    ∫ u, G (radicalEquiv u) ∂radicalMeasure =
      ∫ z, G z ∂((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) :=
  radicalEquiv_measurePreserving.integral_comp' G

theorem radical_integrable_iff (G : (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ) → E) :
    Integrable (fun u => G (radicalEquiv u)) radicalMeasure ↔
      Integrable G ((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) :=
  radicalEquiv_measurePreserving.integrable_comp_emb radicalEquiv.measurableEmbedding

/-- **The product formula**: for a factorizable datum the integral over `𝔸²` is the product of the
finite congruence integral and the real integral. -/
theorem integral_factorizable [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    (Ff : FiniteAdeles × FiniteAdeles → ℂ) (Fr : (Fin 2 → ℝ) → E) :
    ∫ u : Adeles × Adeles, Ff (u.1.2, u.2.2) • Fr ![u.1.1, u.2.1] ∂radicalMeasure =
      (∫ σ, Ff σ ∂(finiteMeasure.prod finiteMeasure)) • ∫ w, Fr w := by
  have := radical_integral_eq (fun z => Ff z.1 • Fr z.2)
  rw [integral_prod_smul] at this
  exact this

end TernaryPeriodPolynomials.Argument.FormClassK
