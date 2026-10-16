module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.AwayThreePlaceSplitting

@[expose] public section


/-!
# Adelic points away from `3` and vanishing on a finite set `S` of places

Formalized by Claude Haiku 5.5.

`awayS S` is the subgroup of `FiniteAwayThree` (finite adeles integral-or-not away from `3`) whose
evaluation at every place of `S` is zero. The one-place split `finiteAwayThreePlaceSplit` restricts
to a continuous additive equivalence `awayS S ≃ₜ+ K_q × awayS (insert q S)` when `q ∉ S`, `q ≠ 3`.
This is the one-step ingredient of the finite-Finset measure split (induction on `S`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep

open TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance awayStepDecidableEq : DecidableEq FinitePlace := Classical.decEq _

/-- Points of `FiniteAwayThree` vanishing at every place of `S`. -/
def awayS (S : Finset FinitePlace) : AddSubgroup FiniteAwayThree where
  carrier := {x | ∀ p ∈ S, finiteEvaluation p x.val = 0}
  add_mem' := by
    intro a b ha hb p hp
    simp only [AddSubgroup.coe_add, map_add, ha p hp, hb p hp, add_zero]
  zero_mem' := by
    intro p _
    exact map_zero _
  neg_mem' := by
    intro a ha p hp
    simp only [AddSubgroup.coe_neg, map_neg, ha p hp, neg_zero]

theorem mem_awayS {S : Finset FinitePlace} {x : FiniteAwayThree} :
    x ∈ awayS S ↔ ∀ p ∈ S, finiteEvaluation p x.val = 0 := Iff.rfl

theorem remainder_mem_awayS (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace)
    (hS : q ∉ S) (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (x : FiniteAwayThree) (hx : x ∈ awayS S) :
    x - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x) ∈ awayS T := by
  intro p hp
  rcases (hT p).mp hp with hpS | hpq
  · have pne : p ≠ q := fun h => hS (h ▸ hpS)
    have hx' : finiteEvaluation p x.val = 0 := (mem_awayS.mp hx) p hpS
    have hι : finiteEvaluation p (finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x)).val = 0 :=
      finiteAtPlaceScalar_away q _ p pne
    rw [AddSubgroup.coe_sub, map_sub, hx', hι, sub_zero]
  · rw [hpq]
    show finiteAwayThreeEvaluation q (x - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x)) = 0
    rw [map_sub, finiteAwayThreeEvaluation_atPlace, sub_self]

theorem add_atPlace_mem_awayS (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace)
    (hS : q ∉ S) (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (a : q.adicCompletion ℚ) (b : FiniteAwayThree)
    (hb : b ∈ awayS T) :
    finiteAwayThreeAtPlace q hq a + b ∈ awayS S := by
  intro p hp
  have pne : p ≠ q := fun h => hS (h ▸ hp)
  have hb' : finiteEvaluation p b.val = 0 := (mem_awayS.mp hb) p ((hT p).mpr (Or.inl hp))
  have hι : finiteEvaluation p (finiteAwayThreeAtPlace q hq a).val = 0 :=
    finiteAtPlaceScalar_away q a p pne
  rw [AddSubgroup.coe_add, map_add, hι, hb', add_zero]

/-- The forward map of the one-step split on `awayS S`. -/
def awayStepFwd (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (x : awayS S) : q.adicCompletion ℚ × awayS T :=
  (finiteAwayThreeEvaluation q x.val,
    ⟨x.val - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x.val),
      remainder_mem_awayS q hq S T hS hT x.val x.property⟩)

/-- The inverse map of the one-step split. -/
def awayStepBwd (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (pr : q.adicCompletion ℚ × awayS T) : awayS S :=
  ⟨finiteAwayThreeAtPlace q hq pr.1 + pr.2.val,
    add_atPlace_mem_awayS q hq S T hS hT pr.1 pr.2.val pr.2.property⟩

theorem awayStep_left_inv (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (x : awayS S) : awayStepBwd q hq S T hS hT (awayStepFwd q hq S T hS hT x) = x := by
  apply Subtype.ext
  show finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x.val) +
    (x.val - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x.val)) = x.val
  abel

theorem awayStep_right_inv (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q)
    (pr : q.adicCompletion ℚ × awayS T) : awayStepFwd q hq S T hS hT (awayStepBwd q hq S T hS hT pr) = pr := by
  obtain ⟨a, b⟩ := pr
  have hbq : finiteAwayThreeEvaluation q b.val = 0 := (mem_awayS.mp b.property) q ((hT q).mpr (Or.inr rfl))
  have hev : finiteAwayThreeEvaluation q (finiteAwayThreeAtPlace q hq a + b.val) = a := by
    rw [map_add, finiteAwayThreeEvaluation_atPlace, hbq, add_zero]
  apply Prod.ext hev
  apply Subtype.ext
  show finiteAwayThreeAtPlace q hq a + b.val - finiteAwayThreeAtPlace q hq
    (finiteAwayThreeEvaluation q (finiteAwayThreeAtPlace q hq a + b.val)) = b.val
  rw [hev]
  abel

theorem awayStep_map_add (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q)
    (x y : awayS S) :
    awayStepFwd q hq S T hS hT (x + y) = awayStepFwd q hq S T hS hT x + awayStepFwd q hq S T hS hT y := by
  apply Prod.ext (map_add _ _ _)
  apply Subtype.ext
  show (x.val + y.val) - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q (x.val + y.val)) =
    (x.val - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q x.val)) +
      (y.val - finiteAwayThreeAtPlace q hq (finiteAwayThreeEvaluation q y.val))
  rw [map_add, map_add]
  abel

/-- **One-step split (restricted).** For `q ≠ 3` with `q ∉ S`, the vanishing-on-`S` points split
as the local value at `q` times the vanishing-on-`T` points (`T = S ∪ {q}`). The same map as
`finiteAwayThreePlaceSplit`, restricted to `awayS S`. -/
def awayStepSplit (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace) (hS : q ∉ S)
    (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) :
    awayS S ≃ₜ+ (q.adicCompletion ℚ × awayS T) where
  toFun := awayStepFwd q hq S T hS hT
  invFun := awayStepBwd q hq S T hS hT
  left_inv := awayStep_left_inv q hq S T hS hT
  right_inv := awayStep_right_inv q hq S T hS hT
  map_add' := awayStep_map_add q hq S T hS hT
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (finiteAwayThreeEvaluation_continuous q).comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.sub
        ((finiteAwayThreeAtPlace_continuous q hq).comp
          ((finiteAwayThreeEvaluation_continuous q).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((finiteAwayThreeAtPlace_continuous q hq).comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)

end TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep
