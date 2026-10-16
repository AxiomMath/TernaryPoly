module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad3
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad5

@[expose] public section


/-!
# The place-three factor of the finite entry integral

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.

Paper: Appendix C entry computation
(about): the factor `1/9` and the global integral over `FiniteAwayThree²`.

* `rearr`: the measurable rearrangement `(α × β) × (γ × δ) ≃ (α × γ) × (β × δ)` and its measure preservation.
* `integral_badRegion_split`: the integral over `badRegion = {‖v₁‖₃ < 1, ‖v₂‖₃ < 1}` of a function invariant under
  integral shifts is `(1/9)` times the integral over `FiniteAwayThree²`; the Haar measure of the finite
  adeles is split as `ℚ₃ × FiniteAwayThree`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

section Rearrangement

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- `((a, b), (c, d)) ↦ ((a, c), (b, d))`. -/
def rearr : ((α × β) × (γ × δ)) ≃ᵐ ((α × γ) × (β × δ)) :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl α).prodCongr
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl δ)).trans MeasurableEquiv.prodAssoc))
      |>.trans MeasurableEquiv.prodAssoc.symm)

theorem rearr_apply (p : (α × β) × (γ × δ)) : (rearr p : (α × γ) × (β × δ)) = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := rfl

theorem rearr_measurePreserving (μ : Measure α) (ν : Measure β) (ρ : Measure γ) (τ : Measure δ)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (rearr : ((α × β) × (γ × δ)) ≃ᵐ ((α × γ) × (β × δ)))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : ((α × β) × (γ × δ)) ≃ᵐ α × (β × (γ × δ)))
      ((μ.prod ν).prod (ρ.prod τ)) (μ.prod (ν.prod (ρ.prod τ))) :=
    measurePreserving_prodAssoc μ ν (ρ.prod τ)
  have h2a : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : β × (γ × δ) ≃ᵐ (β × γ) × δ)
      (ν.prod (ρ.prod τ)) ((ν.prod ρ).prod τ) :=
    (measurePreserving_prodAssoc ν ρ τ).symm _
  have h2b : MeasurePreserving (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl δ) :
      (β × γ) × δ ≃ᵐ (γ × β) × δ) ((ν.prod ρ).prod τ) ((ρ.prod ν).prod τ) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id τ)
  have h2c : MeasurePreserving (MeasurableEquiv.prodAssoc : (γ × β) × δ ≃ᵐ γ × (β × δ))
      ((ρ.prod ν).prod τ) (ρ.prod (ν.prod τ)) :=
    measurePreserving_prodAssoc ρ ν τ
  have h2 := h2c.comp (h2b.comp h2a)
  have h3 := (MeasurePreserving.id μ).prod h2
  have h4 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) ≃ᵐ (α × γ) × (β × δ))
      (μ.prod (ρ.prod (ν.prod τ))) ((μ.prod ρ).prod (ν.prod τ)) :=
    (measurePreserving_prodAssoc μ ρ (ν.prod τ)).symm _
  exact h4.comp (h3.comp h1)

end Rearrangement


section PlaceThreeSplit

open TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers (smallBall smallBall_measure)

/-- The measure of the `3`-adic box `3ℤ₃ × 3ℤ₃` for the normalized Haar measure is `1/9`. -/
theorem smallBall_prod_measure :
    (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure) (smallBall ×ˢ smallBall) = (1 / 9 : ENNReal) := by
  have := normalizedLocalThreeMeasure_haar
  rw [Measure.prod_prod, smallBall_measure normalizedLocalThreeMeasure normalizedLocalThreeMeasure_normalized]
  rw [one_div, one_div, ← ENNReal.mul_inv (by left; norm_num) (by right; norm_num)]
  norm_num

/-- On the bad region an integral-shift invariant function equals its value at the away-from-three part. -/
theorem shift_away (H : FiniteAdeles × FiniteAdeles → ℂ)
    (hH : ∀ v u : FiniteAdeles × FiniteAdeles, u.1 ∈ Set.range integralEmbedding →
      u.2 ∈ Set.range integralEmbedding → H (v + u) = H v) (v : FiniteAdeles × FiniteAdeles)
    (member : v ∈ badRegion) :
    H v = H ((finiteAwayThree v.1).val, (finiteAwayThree v.2).val) := by
  have u1 : finiteAtThreeScalar (finiteThree v.1) ∈ Set.range integralEmbedding :=
    finiteAtThreeScalar_integral (⟨finiteThree v.1, member.1.le⟩ : ℤ_[3])
  have u2 : finiteAtThreeScalar (finiteThree v.2) ∈ Set.range integralEmbedding :=
    finiteAtThreeScalar_integral (⟨finiteThree v.2, member.2.le⟩ : ℤ_[3])
  have := hH ((finiteAwayThree v.1).val, (finiteAwayThree v.2).val)
    (finiteAtThreeScalar (finiteThree v.1), finiteAtThreeScalar (finiteThree v.2)) u1 u2
  rw [← this]
  congr 1
  ext
  · simp [finiteAwayThree_val]
  · simp [finiteAwayThree_val]


/-- Change of variables along the product of the two place-three splits. -/
theorem split_integral (G : (ℚ_[3] × FiniteAwayThree) × (ℚ_[3] × FiniteAwayThree) → ℂ) :
    (∫ v : FiniteAdeles × FiniteAdeles, G ((finiteThree v.1, finiteAwayThree v.1), (finiteThree v.2, finiteAwayThree v.2))
        ∂(finiteMeasure.prod finiteMeasure)) =
      ∫ p, G p ∂((normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure).prod
        (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure)) := by
  have hhaar := normalizedLocalThreeMeasure_haar
  have hS3 : MeasurePreserving (finiteThreeSplit.toHomeomorph.toMeasurableEquiv) finiteMeasure
      (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure) :=
    finiteThreeSplit_measurePreserving
  have hS : MeasurePreserving ((finiteThreeSplit.toHomeomorph.toMeasurableEquiv).prodCongr
      (finiteThreeSplit.toHomeomorph.toMeasurableEquiv)) (finiteMeasure.prod finiteMeasure)
      ((normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure).prod
        (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure)) := hS3.prod hS3
  exact hS.integral_comp' G

/-- Change of variables along the rearrangement `rearr`. -/
theorem rearr_integral (G : (ℚ_[3] × FiniteAwayThree) × (ℚ_[3] × FiniteAwayThree) → ℂ) :
    (∫ p, G p ∂((normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure).prod
        (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure))) =
      ∫ q : (ℚ_[3] × ℚ_[3]) × (FiniteAwayThree × FiniteAwayThree),
        G ((q.1.1, q.2.1), (q.1.2, q.2.2))
        ∂((normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure).prod
          (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
  have hhaar := normalizedLocalThreeMeasure_haar
  have hR := rearr_measurePreserving normalizedLocalThreeMeasure normalizedLocalThreeMeasure
    finiteAwayThreeMeasure finiteAwayThreeMeasure
  exact (hR.integral_comp' G).symm

/-- The box factor `1/9` times the integral over `FiniteAwayThree²`. -/
theorem integral_smallBox (H : (FiniteAwayThree × FiniteAwayThree) → ℂ) :
    (∫ q : (ℚ_[3] × ℚ_[3]) × (FiniteAwayThree × FiniteAwayThree),
        (smallBall ×ˢ smallBall).indicator (fun _ => (1 : ℂ)) q.1 * H q.2
        ∂((normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure).prod
          (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) =
      (1 / 9 : ℂ) * ∫ z, H z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have hhaar := normalizedLocalThreeMeasure_haar
  have hm := integral_prod_mul (μ := normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)
    (ν := finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
    (fun p : ℚ_[3] × ℚ_[3] => (smallBall ×ˢ smallBall).indicator (fun _ => (1 : ℂ)) p) H
  refine hm.trans ?_
  congr 1
  rw [integral_indicator_const _ (smallBall_measurable.prod smallBall_measurable), Measure.real,
    smallBall_prod_measure]
  simp


/-- The `3`-adic parts of a point of the bad region lie in the box `3ℤ₃ × 3ℤ₃`. -/
theorem mem_smallBox (v : FiniteAdeles × FiniteAdeles) (member : v ∈ badRegion) :
    (finiteThree v.1, finiteThree v.2) ∈ smallBall ×ˢ smallBall := by
  have h1 : ‖finiteThree v.1‖ < 1 := member.1
  have h2 : ‖finiteThree v.2‖ < 1 := member.2
  exact Set.mk_mem_prod (show finiteThree v.1 ∈ smallBall from h1) (show finiteThree v.2 ∈ smallBall from h2)

/-- Outside the bad region the `3`-adic parts do not lie in the box. -/
theorem not_mem_smallBox (v : FiniteAdeles × FiniteAdeles) (member : v ∉ badRegion) :
    (finiteThree v.1, finiteThree v.2) ∉ smallBall ×ˢ smallBall := by
  intro h
  apply member
  have h1 : finiteThree v.1 ∈ smallBall := h.1
  have h2 : finiteThree v.2 ∈ smallBall := h.2
  exact ⟨show ‖finiteThree v.1‖ < 1 from h1, show ‖finiteThree v.2‖ < 1 from h2⟩

/-- The integrand on the split coordinates. -/
def splitIntegrand (H : FiniteAdeles × FiniteAdeles → ℂ) :
    (ℚ_[3] × FiniteAwayThree) × (ℚ_[3] × FiniteAwayThree) → ℂ := fun p =>
  (smallBall ×ˢ smallBall).indicator (fun _ => (1 : ℂ)) (p.1.1, p.2.1) * H (p.1.2.val, p.2.2.val)

/-- The indicator of the bad region is the split integrand in the place-three coordinates. -/
theorem indicator_eq_splitIntegrand (H : FiniteAdeles × FiniteAdeles → ℂ)
    (hH : ∀ v u : FiniteAdeles × FiniteAdeles, u.1 ∈ Set.range integralEmbedding →
      u.2 ∈ Set.range integralEmbedding → H (v + u) = H v) (v : FiniteAdeles × FiniteAdeles) :
    badRegion.indicator H v =
      splitIntegrand H ((finiteThree v.1, finiteAwayThree v.1), (finiteThree v.2, finiteAwayThree v.2)) := by
  by_cases member : v ∈ badRegion
  · rw [Set.indicator_of_mem member]
    have hmem := mem_smallBox v member
    simp only [splitIntegrand, Set.indicator_of_mem hmem, one_mul]
    exact shift_away H hH v member
  · rw [Set.indicator_of_notMem member]
    have hmem := not_mem_smallBox v member
    simp only [splitIntegrand, Set.indicator_of_notMem hmem, zero_mul]

/-- **The place-three factor.**  Integral shifts do not change the integrand, so the integral over the
`3`-adic box `‖v₁‖₃, ‖v₂‖₃ < 1` is the measure `1/9` of the box times the integral over `FiniteAwayThree²`. -/
theorem integral_badRegion_split (H : FiniteAdeles × FiniteAdeles → ℂ)
    (hH : ∀ v u : FiniteAdeles × FiniteAdeles, u.1 ∈ Set.range integralEmbedding →
      u.2 ∈ Set.range integralEmbedding → H (v + u) = H v) :
    (∫ v in badRegion, H v ∂(finiteMeasure.prod finiteMeasure)) =
      (1 / 9 : ℂ) * ∫ z : FiniteAwayThree × FiniteAwayThree, H (z.1.val, z.2.val)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  rw [← integral_indicator badRegion_measurable]
  refine (integral_congr_ae (Filter.Eventually.of_forall (indicator_eq_splitIntegrand H hH))).trans ?_
  refine (split_integral (splitIntegrand H)).trans ?_
  refine (rearr_integral (splitIntegrand H)).trans ?_
  exact integral_smallBox (fun z => H (z.1.val, z.2.val))

end PlaceThreeSplit
end TernaryPeriodPolynomials.Argument.BoundaryComparison
