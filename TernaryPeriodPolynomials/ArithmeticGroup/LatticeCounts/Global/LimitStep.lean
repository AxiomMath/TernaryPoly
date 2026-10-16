module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitShape
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AwaySplit

@[expose] public section


/-!
# Global limit: adjoining one place to a finite set (measure-theoretic bookkeeping)

For a finite set `T` of places `≠ 3` and a place `q ∉ T`, `q ≠ 3`, put `U = T ∪ {q}`.  `psiU : WS T × K_q ≃ᵐ WS U` is measure preserving
(`localPi T ⊗ μ_q → localPi U`) and `iotaS U (psiU (a, x)) = iotaS T a + atPlace q x` (`iotaS_psiU`).  `comm4` is the measure preserving
rearrangement `(A × B) × (C × D) ≃ᵐ (A × C) × (B × D)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit

open Classical

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitStep

section Comm4

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]

/-- `B × (C × D) ≃ᵐ C × (B × D)`. -/
def comm3 : B × (C × D) ≃ᵐ C × (B × D) :=
  (MeasurableEquiv.prodAssoc.symm.trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl D))).trans MeasurableEquiv.prodAssoc

/-- `(A × B) × (C × D) ≃ᵐ (A × C) × (B × D)`. -/
def comm4 : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) :=
  (MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) comm3)).trans
    MeasurableEquiv.prodAssoc.symm

theorem comm4_apply (a : A) (b : B) (c : C) (d : D) : comm4 ((a, b), (c, d)) = ((a, c), (b, d)) := rfl

theorem comm3_mp (ν : Measure B) (κ : Measure C) (ρ : Measure D)
    [SigmaFinite ν] [SigmaFinite κ] [SigmaFinite ρ] :
    MeasurePreserving (comm3 : B × (C × D) ≃ᵐ C × (B × D)) (ν.prod (κ.prod ρ)) (κ.prod (ν.prod ρ)) := by
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : B × (C × D) ≃ᵐ (B × C) × D)
      (ν.prod (κ.prod ρ)) ((ν.prod κ).prod ρ) :=
    MeasurePreserving.symm _ (measurePreserving_prodAssoc ν κ ρ)
  have h3 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.prodComm : B × C ≃ᵐ C × B)
      (MeasurableEquiv.refl D)) ((ν.prod κ).prod ρ) ((κ.prod ν).prod ρ) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := κ)).prod (MeasurePreserving.id ρ)
  have h4 : MeasurePreserving (MeasurableEquiv.prodAssoc : (C × B) × D ≃ᵐ C × (B × D))
      ((κ.prod ν).prod ρ) (κ.prod (ν.prod ρ)) := measurePreserving_prodAssoc _ _ _
  exact h4.comp (h3.comp h2)

theorem comm4_mp (μ : Measure A) (ν : Measure B) (κ : Measure C) (ρ : Measure D)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ] [SigmaFinite ρ] :
    MeasurePreserving (comm4 : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D))
      ((μ.prod ν).prod (κ.prod ρ)) ((μ.prod κ).prod (ν.prod ρ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : (A × B) × (C × D) ≃ᵐ A × (B × (C × D)))
      ((μ.prod ν).prod (κ.prod ρ)) (μ.prod (ν.prod (κ.prod ρ))) := measurePreserving_prodAssoc _ _ _
  have h5 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : A × (C × (B × D)) ≃ᵐ (A × C) × (B × D))
      (μ.prod (κ.prod (ν.prod ρ))) ((μ.prod κ).prod (ν.prod ρ)) :=
    MeasurePreserving.symm _ (measurePreserving_prodAssoc μ κ (ν.prod ρ))
  have h6 := (MeasurePreserving.id μ).prod (comm3_mp ν κ ρ)
  exact h5.comp (h6.comp h1)

end Comm4

section Union

variable (T : Finset FinitePlace) (q : FinitePlace)

theorem disjoint_single (hqT : q ∉ T) : Disjoint T ({q} : Finset FinitePlace) :=
  Finset.disjoint_singleton_right.mpr hqT

/-- `WS T × K_q ≃ᵐ WS (T ∪ {q})`. -/
def psiU (hqT : q ∉ T) : WS T × q.adicCompletion ℚ ≃ᵐ WS (T ∪ {q}) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (WS T))
    (MeasurableEquiv.piUnique (fun p : ({q} : Finset FinitePlace) => p.1.adicCompletion ℚ)).symm).trans
    (MeasurableEquiv.piFinsetUnion (fun p : FinitePlace => p.adicCompletion ℚ) (disjoint_single T q hqT))

theorem psiU_mp (hqT : q ∉ T) :
    MeasurePreserving (psiU T q hqT) ((localPi T).prod (finiteCompletionMeasure q)) (localPi (T ∪ {q})) := by
  have hUnit : MeasurePreserving (MeasurableEquiv.piUnique (fun p : ({q} : Finset FinitePlace) => p.1.adicCompletion ℚ))
      (localPi ({q} : Finset FinitePlace)) (finiteCompletionMeasure q) :=
    measurePreserving_piUnique (fun p : ({q} : Finset FinitePlace) => finiteCompletionMeasure p.1)
  have hPi : MeasurePreserving (MeasurableEquiv.piFinsetUnion (fun p : FinitePlace => p.adicCompletion ℚ)
      (disjoint_single T q hqT)) ((localPi T).prod (localPi ({q} : Finset FinitePlace))) (localPi (T ∪ {q})) :=
    measurePreserving_piFinsetUnion (disjoint_single T q hqT) (fun p : FinitePlace => finiteCompletionMeasure p)
  exact hPi.comp ((MeasurePreserving.id _).prod (MeasurePreserving.symm _ hUnit))

theorem psiU_apply_mem (hqT : q ∉ T) (a : WS T) (x : q.adicCompletion ℚ) (w : FinitePlace) (hw : w ∈ T)
    (hw' : w ∈ T ∪ {q}) : psiU T q hqT (a, x) ⟨w, hw'⟩ = a ⟨w, hw⟩ :=
  Equiv.piFinsetUnion_left (fun p : FinitePlace => p.adicCompletion ℚ) (disjoint_single T q hqT) hw hw'

theorem psiU_apply_q (hqT : q ∉ T) (a : WS T) (x : q.adicCompletion ℚ) (hw' : q ∈ T ∪ {q}) :
    psiU T q hqT (a, x) ⟨q, hw'⟩ = x :=
  Equiv.piFinsetUnion_right (fun p : FinitePlace => p.adicCompletion ℚ) (disjoint_single T q hqT)
    (Finset.mem_singleton_self q) hw'

theorem iotaS_psiU (hT : ∀ p ∈ T, p ≠ placeThree) (hU : ∀ p ∈ T ∪ {q}, p ≠ placeThree) (hq : q ≠ placeThree)
    (hqT : q ∉ T) (a : WS T) (x : q.adicCompletion ℚ) :
    iotaS (T ∪ {q}) hU (psiU T q hqT (a, x)) = iotaS T hT a + finiteAwayThreeAtPlace q hq x := by
  apply Subtype.ext
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro w
  have hadd : ∀ (y z : FiniteAwayThree), (y + z).val w = y.val w + z.val w := fun y z => rfl
  rw [hadd]
  by_cases hwT : w ∈ T
  · have hwU : w ∈ T ∪ {q} := Finset.mem_union_left _ hwT
    have hwq : w ≠ q := fun h => hqT (h ▸ hwT)
    have e1 := eval_iotaS_of_mem (T ∪ {q}) hU (psiU T q hqT (a, x)) ⟨w, hwU⟩
    have e2 := eval_iotaS_of_mem T hT a ⟨w, hwT⟩
    rw [psiU_apply_mem T q hqT a x w hwT hwU] at e1
    change finiteEvaluation w _ = _ at e1
    change finiteEvaluation w _ = _ at e2
    have e3 : finiteEvaluation w (finiteAwayThreeAtPlace q hq x).val = 0 := finiteAtPlaceScalar_away q x w hwq
    change finiteEvaluation w (iotaS (T ∪ {q}) hU (psiU T q hqT (a, x))).val =
      finiteEvaluation w (iotaS T hT a).val + finiteEvaluation w (finiteAwayThreeAtPlace q hq x).val
    rw [e1, e2, e3, add_zero]
  · by_cases hwq : w = q
    · subst hwq
      have hwU : w ∈ T ∪ {w} := Finset.mem_union_right _ (Finset.mem_singleton_self w)
      have e1 := eval_iotaS_of_mem (T ∪ {w}) hU (psiU T w hqT (a, x)) ⟨w, hwU⟩
      rw [psiU_apply_q T w hqT a x hwU] at e1
      have e2 := eval_iotaS_of_notMem T hT a w hwT
      have e3 : finiteEvaluation w (finiteAwayThreeAtPlace w hq x).val = x := finiteAtPlaceScalar_same w x
      change finiteEvaluation w (iotaS (T ∪ {w}) hU (psiU T w hqT (a, x))).val =
        finiteEvaluation w (iotaS T hT a).val + finiteEvaluation w (finiteAwayThreeAtPlace w hq x).val
      rw [e1, e2, e3, zero_add]
    · have hwU : w ∉ T ∪ {q} := by
        simp [hwT, hwq]
      have e1 := eval_iotaS_of_notMem (T ∪ {q}) hU (psiU T q hqT (a, x)) w hwU
      have e2 := eval_iotaS_of_notMem T hT a w hwT
      have e3 : finiteEvaluation w (finiteAwayThreeAtPlace q hq x).val = 0 := finiteAtPlaceScalar_away q x w hwq
      change finiteEvaluation w (iotaS (T ∪ {q}) hU (psiU T q hqT (a, x))).val =
        finiteEvaluation w (iotaS T hT a).val + finiteEvaluation w (finiteAwayThreeAtPlace q hq x).val
      rw [e1, e2, e3, add_zero]

end Union

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitStep
