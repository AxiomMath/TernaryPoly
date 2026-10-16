module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RowDictionary

@[expose] public section


/-!
# (C), step 8: the real shift `w ↦ (r₂ - w₁, r₁ - w₀)` preserves Lebesgue measure on `ℝ²`

Formalized by Claude Sonnet 5.5.

`shiftEquiv r` is the measurable equivalence `shiftV r` of `Fin 2 → ℝ` (the real coordinate of `w₀⁻¹ u(w) = w₀⁻¹ u(r)·qMat (shiftV r w)`);
it is measure preserving, so integrals and integrability of `Φ ∘ shiftV r` are those of `Φ`.
-/

open MeasureTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The shift `shiftV r` as a measurable equivalence. -/
def shiftEquiv (r : ℚ × ℚ) : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
  (MeasurableEquiv.finTwoArrow).trans <|
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft (r.1 : ℝ)) (MeasurableEquiv.subLeft (r.2 : ℝ))).trans
    MeasurableEquiv.prodComm).trans (MeasurableEquiv.finTwoArrow).symm

theorem shiftEquiv_apply (r : ℚ × ℚ) (w : Fin 2 → ℝ) : shiftEquiv r w = shiftV r w := by
  ext i
  fin_cases i <;> rfl

theorem shiftEquiv_measurePreserving (r : ℚ × ℚ) :
    MeasurePreserving (shiftEquiv r) (volume : Measure (Fin 2 → ℝ)) volume := by
  have h1 := volume_preserving_finTwoArrow ℝ
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft (r.1 : ℝ)) (MeasurableEquiv.subLeft (r.2 : ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (Measure.measurePreserving_sub_left volume (r.1 : ℝ)).prod (Measure.measurePreserving_sub_left volume (r.2 : ℝ))
  have h3 : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  have h4 := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  exact h4.comp (h3.comp (h2.comp h1))

theorem integral_shiftV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℚ × ℚ) (Φ : (Fin 2 → ℝ) → E) :
    ∫ w, Φ (shiftV r w) = ∫ v, Φ v := by
  have := (shiftEquiv_measurePreserving r).integral_comp' Φ
  simpa only [shiftEquiv_apply] using this

theorem integrable_shiftV {E : Type*} [NormedAddCommGroup E] (r : ℚ × ℚ) (Φ : (Fin 2 → ℝ) → E) :
    Integrable (fun w => Φ (shiftV r w)) ↔ Integrable Φ := by
  have := (shiftEquiv_measurePreserving r).integrable_comp_emb (shiftEquiv r).measurableEmbedding (g := Φ)
  have e : (fun w => Φ (shiftV r w)) = Φ ∘ shiftEquiv r := by
    funext w; simp [shiftEquiv_apply]
  rw [e]; exact this

end TernaryPeriodPolynomials.Argument.FormClassK
