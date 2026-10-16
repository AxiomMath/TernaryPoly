module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Real-finite Fubini for the adelic radical measure

The radical measure on `𝔸 × 𝔸` is the image of `(ℝ × ℝ) × (𝔸_f × 𝔸_f)` under the coordinate
shuffle. Hence for an integrable function the standard integral splits into a finite outer and a
real inner integral. This is the first step of the large-`Re s` route for the standard
intertwining integrals, where integrability is supplied by `IsStandardContinuation`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.ArchimedeanConstant

/-- The coordinate shuffle `((r₁,f₁),(r₂,f₂)) ↦ ((r₁,r₂),(f₁,f₂))`. -/
def radicalShuffle : (ℝ × FiniteAdeles) × (ℝ × FiniteAdeles) ≃ᵐ (ℝ × ℝ) × (FiniteAdeles × FiniteAdeles) :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl FiniteAdeles)).trans
          MeasurableEquiv.prodAssoc)))).trans MeasurableEquiv.prodAssoc.symm

theorem radicalShuffle_apply (r₁ r₂ : ℝ) (f₁ f₂ : FiniteAdeles) :
    radicalShuffle ((r₁, f₁), (r₂, f₂)) = ((r₁, r₂), (f₁, f₂)) := rfl

theorem radicalShuffle_measurePreserving :
    MeasurePreserving radicalShuffle radicalMeasure
      (((volume : Measure ℝ).prod volume).prod (finiteMeasure.prod finiteMeasure)) := by
  have h1 := measurePreserving_prodAssoc (volume : Measure ℝ) finiteMeasure
    ((volume : Measure ℝ).prod finiteMeasure)
  have h2 := measurePreserving_prodAssoc finiteMeasure (volume : Measure ℝ) finiteMeasure
  have h3 : MeasurePreserving (Prod.map Prod.swap id)
      ((finiteMeasure.prod (volume : Measure ℝ)).prod finiteMeasure)
      (((volume : Measure ℝ).prod finiteMeasure).prod finiteMeasure) :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id finiteMeasure)
  have h4 := measurePreserving_prodAssoc (volume : Measure ℝ) finiteMeasure finiteMeasure
  have hinner : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl FiniteAdeles)).trans
          MeasurableEquiv.prodAssoc))
      (finiteMeasure.prod ((volume : Measure ℝ).prod finiteMeasure))
      ((volume : Measure ℝ).prod (finiteMeasure.prod finiteMeasure)) :=
    h4.comp (h3.comp h2.symm)
  have hmid : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.prodAssoc.symm.trans
          ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl FiniteAdeles)).trans
            MeasurableEquiv.prodAssoc)))
      ((volume : Measure ℝ).prod (finiteMeasure.prod ((volume : Measure ℝ).prod finiteMeasure)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (finiteMeasure.prod finiteMeasure))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod hinner
  have h5 := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (finiteMeasure.prod finiteMeasure)
  exact h5.symm.comp (hmid.comp h1)

/-- **Real-finite Fubini for the radical measure.** -/
theorem radical_integral_split (h : Adeles × Adeles → ℂ) (hi : Integrable h radicalMeasure) :
    ∫ u, h u ∂radicalMeasure =
      ∫ f : FiniteAdeles × FiniteAdeles, ∫ r : ℝ × ℝ, h ((r.1, f.1), (r.2, f.2))
        ∂((volume : Measure ℝ).prod volume) ∂(finiteMeasure.prod finiteMeasure) := by
  have hmp := radicalShuffle_measurePreserving
  set g : (ℝ × ℝ) × (FiniteAdeles × FiniteAdeles) → ℂ :=
    fun p => h ((p.1.1, p.2.1), (p.1.2, p.2.2)) with hg
  have hgi : Integrable g (((volume : Measure ℝ).prod volume).prod (finiteMeasure.prod finiteMeasure)) := by
    have : Integrable (g ∘ radicalShuffle) radicalMeasure := hi
    exact (hmp.integrable_comp_emb radicalShuffle.measurableEmbedding).mp this
  calc ∫ u, h u ∂radicalMeasure = ∫ u, g (radicalShuffle u) ∂radicalMeasure := rfl
    _ = ∫ p, g p ∂(((volume : Measure ℝ).prod volume).prod (finiteMeasure.prod finiteMeasure)) :=
      hmp.integral_comp' g
    _ = _ := integral_prod_symm g hgi

theorem lineUnipotent_adele_split (r₁ r₂ : ℝ) (f₁ f₂ : FiniteAdeles) :
    lineUnipotent ((r₁, f₁) : Adeles) ((r₂, f₂) : Adeles) =
      atInfinity (lineUnipotent r₁ r₂) * atFinite (lineUnipotent f₁ f₂) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, lineUnipotent, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- **The standard integral as a finite average of real standard integrals.** -/
theorem standard_integral_split (F : ℂ → AdelicGL → ℂ) (s : ℂ) (g : AdelicGL)
    (hi : Integrable (standardIntegrand F s g) radicalMeasure) :
    ∫ u, standardIntegrand F s g u ∂radicalMeasure =
      ∫ f : FiniteAdeles × FiniteAdeles, ∫ r : ℝ × ℝ,
        F s (weyl⁻¹ * (atInfinity (lineUnipotent r.1 r.2) * atFinite (lineUnipotent f.1 f.2)) * g)
        ∂((volume : Measure ℝ).prod volume) ∂(finiteMeasure.prod finiteMeasure) := by
  rw [radical_integral_split _ hi]
  simp only [standardIntegrand, lineUnipotent_adele_split]

end TernaryPeriodPolynomials.ArchimedeanConstant
