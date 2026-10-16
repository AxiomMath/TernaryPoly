module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AwayMeasure

@[expose] public section


/-!
# The finite-set measure split

Formalized by Claude Haiku 5.5.

For a finite set `S` of places not containing `3`, there is a measurable equivalence
`FiniteAwayThree ≃ᵐ (∀ p : S, K_p) × awayS S`, measure preserving from the Haar measure of
`FiniteAwayThree` to the product of the local completion measures and the Haar measure of
`awayS S` (`localPi S ⊗ awayMeasure S`). Proved by induction on `S`, adjoining one place at a time
with the one-step split `awayStepSplit`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

local instance awaySplitDecidableEq : DecidableEq FinitePlace := Classical.decEq _

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure

/-- The product of the completion measures over the finite set `S`. -/
def localPi (S : Finset FinitePlace) : Measure (∀ p : S, p.1.adicCompletion ℚ) :=
  Measure.pi fun p : S => finiteCompletionMeasure p.1

instance localPi_sigmaFinite (S : Finset FinitePlace) : SigmaFinite (localPi S) :=
  inferInstanceAs (SigmaFinite (Measure.pi fun p : S => finiteCompletionMeasure p.1))

/-- The splitting statement for `S`: under `S ⊆ {places ≠ 3}`, the whole group splits as the
product of the local values over `S` times the points vanishing on `S`, measure preservingly. -/
def SplitFinset (S : Finset FinitePlace) : Prop :=
  (∀ p ∈ S, p ≠ placeThree) →
    ∃ e : FiniteAwayThree ≃ᵐ ((∀ p : S, p.1.adicCompletion ℚ) × awayS S),
      MeasurePreserving e finiteAwayThreeMeasure ((localPi S).prod (awayMeasure S))

instance emptyFinset_isEmpty : IsEmpty (∅ : Finset FinitePlace) :=
  ⟨fun p => Finset.notMem_empty p.1 p.2⟩

/-- The whole group, viewed as `awayS ∅`. -/
def awayEmptyEquiv : FiniteAwayThree ≃ₜ+ awayS (∅ : Finset FinitePlace) where
  toFun x := ⟨x, (mem_awayS).mpr fun p hp => by simp at hp⟩
  invFun y := y.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_id _
  continuous_invFun := continuous_subtype_val

/-- Measurable form of `awayEmptyEquiv`. -/
def awayEmptyMeas : FiniteAwayThree ≃ᵐ awayS (∅ : Finset FinitePlace) :=
  { toEquiv := awayEmptyEquiv.toAddEquiv.toEquiv
    measurable_toFun := awayEmptyEquiv.continuous.measurable
    measurable_invFun := awayEmptyEquiv.symm.continuous.measurable }

theorem awayEmptyMeas_mp :
    MeasurePreserving awayEmptyMeas finiteAwayThreeMeasure (awayMeasure (∅ : Finset FinitePlace)) := by
  have hK : MeasurableSet ((awayUnitCompact (∅ : Finset FinitePlace) : Set (awayS (∅ : Finset FinitePlace)))) :=
    (integralLattice_isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)).measurableSet
  have normalized : finiteAwayThreeMeasure
      (awayEmptyEquiv ⁻¹' ((awayUnitCompact (∅ : Finset FinitePlace) : Set (awayS (∅ : Finset FinitePlace))))) = 1 :=
    finiteAwayThreeMeasure_normalized
  exact ⟨awayEmptyMeas.measurable, map_eq_addHaarMeasure_of_preimage awayEmptyEquiv
    finiteAwayThreeMeasure (awayUnitCompact (∅ : Finset FinitePlace)) hK normalized⟩

/-- Adjoining the trivial product over the empty set. -/
def emptyProdEquiv : awayS (∅ : Finset FinitePlace) ≃ᵐ
    ((∀ p : (∅ : Finset FinitePlace), p.1.adicCompletion ℚ) × awayS (∅ : Finset FinitePlace)) where
  toFun y := (default, y)
  invFun pr := pr.2
  left_inv _ := rfl
  right_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  measurable_toFun := measurable_prodMk_left
  measurable_invFun := measurable_snd

theorem split_empty_base :
    ∃ e : FiniteAwayThree ≃ᵐ ((∀ p : (∅ : Finset FinitePlace), p.1.adicCompletion ℚ) × awayS (∅ : Finset FinitePlace)),
      MeasurePreserving e finiteAwayThreeMeasure ((localPi ∅).prod (awayMeasure ∅)) := by
  refine ⟨awayEmptyMeas.trans emptyProdEquiv, ?_⟩
  have hpi : localPi (∅ : Finset FinitePlace) =
      Measure.dirac (default : ∀ p : (∅ : Finset FinitePlace), p.1.adicCompletion ℚ) := by
    rw [localPi, Measure.pi_of_empty]
    congr 1
  have hmp : MeasurePreserving emptyProdEquiv (awayMeasure (∅ : Finset FinitePlace))
      ((localPi ∅).prod (awayMeasure ∅)) := by
    refine ⟨emptyProdEquiv.measurable, ?_⟩
    rw [hpi, Measure.dirac_prod]
    rfl
  exact hmp.comp awayEmptyMeas_mp

/-- The one-step split as a measurable equivalence. -/
def stepMeas (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) : awayS S ≃ᵐ (q.adicCompletion ℚ × awayS T) :=
  { toEquiv := (awayStepSplit q hq S T hS hT).toAddEquiv.toEquiv
    measurable_toFun := (awayStepSplit q hq S T hS hT).continuous.measurable
    measurable_invFun := (awayStepSplit q hq S T hS hT).symm.continuous.measurable }

theorem stepMeas_mp (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) :
    MeasurePreserving (stepMeas q hq S T hS hT) (awayMeasure S)
      ((finiteCompletionMeasure q).prod (awayMeasure T)) :=
  MeasurePreserving.symm (stepMeas q hq S T hS hT).symm
    (awayStep_symm_measurePreserving q hq S T hS hT)

/-- Splitting the product over `S ∪ {q}` into the product over `S` and the factor at `q`. -/
theorem piFinsetUnion_mp (S : Finset FinitePlace) (q : FinitePlace) (hqS : q ∉ S) :
    ∃ Epi : (∀ p : (S ∪ {q} : Finset FinitePlace), p.1.adicCompletion ℚ) ≃ᵐ
        ((∀ p : S, p.1.adicCompletion ℚ) × q.adicCompletion ℚ),
      MeasurePreserving Epi (localPi (S ∪ {q})) ((localPi S).prod (finiteCompletionMeasure q)) := by
  have hdisj : Disjoint S ({q} : Finset FinitePlace) := Finset.disjoint_singleton_right.mpr hqS
  let unitQ : (∀ p : ({q} : Finset FinitePlace), p.1.adicCompletion ℚ) ≃ᵐ q.adicCompletion ℚ :=
    MeasurableEquiv.piUnique _
  have hUnit : MeasurePreserving unitQ (localPi ({q} : Finset FinitePlace)) (finiteCompletionMeasure q) :=
    measurePreserving_piUnique (fun p : ({q} : Finset FinitePlace) => finiteCompletionMeasure p.1)
  have hPi : MeasurePreserving (MeasurableEquiv.piFinsetUnion (fun p : FinitePlace => p.adicCompletion ℚ) hdisj)
      ((localPi S).prod (localPi ({q} : Finset FinitePlace))) (localPi (S ∪ {q})) :=
    measurePreserving_piFinsetUnion hdisj (fun p : FinitePlace => finiteCompletionMeasure p)
  refine ⟨(MeasurableEquiv.piFinsetUnion (fun p : FinitePlace => p.adicCompletion ℚ) hdisj).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) unitQ), ?_⟩
  have hsymm := MeasurePreserving.symm (MeasurableEquiv.piFinsetUnion (fun p : FinitePlace => p.adicCompletion ℚ) hdisj) hPi
  have hprod : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) unitQ)
      ((localPi S).prod (localPi ({q} : Finset FinitePlace))) ((localPi S).prod (finiteCompletionMeasure q)) :=
    (MeasurePreserving.id _).prod hUnit
  exact hprod.comp hsymm

/-- One-step case: `S` splits, and adjoining `q ∉ S` splits `S ∪ {q}`. -/
theorem split_step (S : Finset FinitePlace) (q : FinitePlace) (hqS : q ∉ S) (ih : SplitFinset S) :
    SplitFinset (S ∪ {q}) := by
  intro hall
  have hq : q ≠ placeThree := hall q (by simp)
  have hS' : ∀ p ∈ S, p ≠ placeThree := fun p hp => hall p (by simp [hp])
  obtain ⟨e, he⟩ := ih hS'
  have hT : ∀ p, p ∈ S ∪ {q} ↔ p ∈ S ∨ p = q := fun p => by
    rw [Finset.mem_union, Finset.mem_singleton]
  obtain ⟨Epi, hEpi⟩ := piFinsetUnion_mp S q hqS
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (∀ p : S, p.1.adicCompletion ℚ))
        (stepMeas q hq S (S ∪ {q}) hqS hT))
      ((localPi S).prod (awayMeasure S))
      ((localPi S).prod ((finiteCompletionMeasure q).prod (awayMeasure (S ∪ {q})))) :=
    (MeasurePreserving.id _).prod (stepMeas_mp q hq S (S ∪ {q}) hqS hT)
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm)
      ((localPi S).prod ((finiteCompletionMeasure q).prod (awayMeasure (S ∪ {q}))))
      (((localPi S).prod (finiteCompletionMeasure q)).prod (awayMeasure (S ∪ {q}))) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc _ _ _)
  have h3 : MeasurePreserving (MeasurableEquiv.prodCongr Epi.symm (MeasurableEquiv.refl _))
      (((localPi S).prod (finiteCompletionMeasure q)).prod (awayMeasure (S ∪ {q})))
      ((localPi (S ∪ {q})).prod (awayMeasure (S ∪ {q}))) :=
    (MeasurePreserving.symm Epi hEpi).prod (MeasurePreserving.id _)
  refine ⟨e.trans ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (stepMeas q hq S (S ∪ {q}) hqS hT)).trans
      (MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodCongr Epi.symm (MeasurableEquiv.refl _)))), ?_⟩
  exact h3.comp (h2.comp (h1.comp he))

theorem splitFinset_all (S : Finset FinitePlace) : SplitFinset S := by
  induction S using Finset.induction_on with
  | empty => intro _; exact split_empty_base
  | @insert q S hqS ih =>
    have h := split_step S q hqS ih
    have hI : S ∪ {q} = insert q S := by
      ext p
      simp
    rwa [hI] at h

end TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
