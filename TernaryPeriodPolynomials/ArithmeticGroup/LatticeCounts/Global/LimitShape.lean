module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitSplit
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AwaySplit
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinGlobal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceIntegralEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic

open Classical


/-!
# Global limit, shape lemma (2/2): integrals over `U_S` of functions of the `S`-local coordinates

`map_piS_prod_restrict_UregionS`: the pushforward of `finiteAwayThreeMeasure.prod finiteAwayThreeMeasure` restricted to `U_S = UregionS S` under the local coordinates at `S` is
`(localPi S).prod (localPi S)` (the away factor has measure one).  `setIntegral_UregionS`, `setLIntegral_UregionS`: for `G` on `(∏_{p∈S} K_p)²`,
`∫_{U_S} G(π z) = ∫ G d(localPi S ⊗ localPi S)`.  `UregionS_measurable`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit

/-- Points of `FiniteAwayThree` integral at every place off `S`. -/
def VS (S : Finset FinitePlace) : Set FiniteAwayThree :=
  {x | ∀ w : FinitePlace, w ∉ S → finiteEvaluation w x.val ∈ OS w}

theorem mem_VS_iff (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (x : FiniteAwayThree) :
    x ∈ VS S ↔ ((eS S hS) x).2 ∈ KS S := by
  change _ ↔ (x - iotaS S hS (piS S x)).val ∈ Set.range integralEmbedding
  rw [mem_range_integralEmbedding_iff]
  constructor
  · intro h w
    rw [AddSubgroup.coe_sub, map_sub]
    by_cases hw : w ∈ S
    · rw [show w = (⟨w, hw⟩ : S).1 from rfl, eval_iotaS_of_mem]
      change finiteEvaluation w x.val - finiteAwayThreeEvaluation w x ∈ OS w
      rw [show finiteEvaluation w x.val = finiteAwayThreeEvaluation w x from rfl, sub_self]
      exact (OS w).zero_mem
    · rw [eval_iotaS_of_notMem S hS _ w hw, sub_zero]
      exact h w hw
  · intro h w hw
    have := h w
    rwa [AddSubgroup.coe_sub, map_sub, eval_iotaS_of_notMem S hS _ w hw, sub_zero] at this

theorem KS_measurableSet (S : Finset FinitePlace) : MeasurableSet (KS S) :=
  (integralLattice_isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)).measurableSet

/-- The measurable splitting. -/
def eSM (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) : FiniteAwayThree ≃ᵐ WS S × awayS S :=
  (eS S hS).toHomeomorph.toMeasurableEquiv

theorem eSM_apply (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (x : FiniteAwayThree) :
    eSM S hS x = eS S hS x := rfl

theorem eSM_measurePreserving (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    MeasurePreserving (eSM S hS) finiteAwayThreeMeasure ((localPi S).prod (awayMeasure S)) :=
  MeasurePreserving.symm (eSM S hS).symm (eS_symm_measurePreserving S hS)

theorem VS_eq_preimage (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    VS S = (eSM S hS) ⁻¹' (Set.univ ×ˢ KS S) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, eSM_apply, mem_VS_iff S hS]

theorem VS_measurable (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) : MeasurableSet (VS S) := by
  rw [VS_eq_preimage S hS]
  exact (eSM S hS).measurable (MeasurableSet.univ.prod (KS_measurableSet S))

/-- **The pushforward of the Haar measure restricted to the integral-off-`S` points is the product of the local measures.** -/
theorem map_piS_restrict_VS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    Measure.map (piS S) (finiteAwayThreeMeasure.restrict (VS S)) = localPi S := by
  ext A hA
  rw [Measure.map_apply (continuous_piS S).measurable hA,
    Measure.restrict_apply ((continuous_piS S).measurable hA)]
  have hset : piS S ⁻¹' A ∩ VS S = (eSM S hS) ⁻¹' (A ×ˢ KS S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, mem_VS_iff S hS, eSM_apply]
    rfl
  rw [hset, (eSM_measurePreserving S hS).measure_preimage (hA.prod (KS_measurableSet S)).nullMeasurableSet,
    Measure.prod_prod, awayMeasure_normalized, mul_one]

theorem UregionS_eq (S : Finset FinitePlace) :
    TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal.UregionS S = VS S ×ˢ VS S := by
  ext z
  simp only [TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal.UregionS, Set.mem_ofPred_eq, Set.mem_prod, VS]
  constructor
  · intro h
    exact ⟨fun w hw => (h w hw).1, fun w hw => (h w hw).2⟩
  · rintro ⟨h1, h2⟩ w hw
    exact ⟨h1 w hw, h2 w hw⟩

/-- **The shape lemma.**  The pushforward of the product Haar measure restricted to `U_S` under the local coordinates at `S` is the
product of the local measures. -/
theorem map_piS_prod_restrict_UregionS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    Measure.map (fun z : FiniteAwayThree × FiniteAwayThree => (piS S z.1, piS S z.2))
        ((finiteAwayThreeMeasure.prod finiteAwayThreeMeasure).restrict
          (TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal.UregionS S)) =
      (localPi S).prod (localPi S) := by
  rw [UregionS_eq, ← Measure.prod_restrict]
  have h := Measure.map_prod_map (finiteAwayThreeMeasure.restrict (VS S)) (finiteAwayThreeMeasure.restrict (VS S))
    (continuous_piS S).measurable (continuous_piS S).measurable
  rw [map_piS_restrict_VS S hS] at h
  exact h.symm

theorem measurable_piPair (S : Finset FinitePlace) :
    Measurable (fun z : FiniteAwayThree × FiniteAwayThree => (piS S z.1, piS S z.2)) :=
  ((continuous_piS S).comp continuous_fst).measurable.prodMk ((continuous_piS S).comp continuous_snd).measurable

/-- **Integrals over `U_S` of functions of the `S`-local coordinates.** -/
theorem setIntegral_UregionS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Finset FinitePlace)
    (hS : ∀ p ∈ S, p ≠ placeThree) (G : WS S × WS S → E)
    (hG : AEStronglyMeasurable G ((localPi S).prod (localPi S))) :
    ∫ z in TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal.UregionS S,
        G (piS S z.1, piS S z.2) ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫ a, G a ∂((localPi S).prod (localPi S)) := by
  have hmap := map_piS_prod_restrict_UregionS S hS
  rw [← hmap] at hG
  rw [← hmap]
  exact (integral_map (measurable_piPair S).aemeasurable hG).symm

/-- The same for `lintegral`. -/
theorem setLIntegral_UregionS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree)
    (G : WS S × WS S → ENNReal) (hG : Measurable G) :
    ∫⁻ z in TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal.UregionS S,
        G (piS S z.1, piS S z.2) ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫⁻ a, G a ∂((localPi S).prod (localPi S)) := by
  rw [← map_piS_prod_restrict_UregionS S hS]
  exact (lintegral_map hG (measurable_piPair S)).symm

theorem UregionS_measurable (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    MeasurableSet (TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal.UregionS S) := by
  rw [UregionS_eq]
  exact (VS_measurable S hS).prod (VS_measurable S hS)

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
