module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Iterated integration after swapping the middle factors

`((a, b), (c, d)) ↦ ((a, c), (b, d))` is a measure-preserving measurable equivalence of product measures
(`measurePreserving_swapMid`); `integral_swapMid` turns an integral over `(α × β) × (γ × δ)` into the iterated
integral over `α × γ` and then `β × δ`.  Used to split the adelic radical `(ℝ × A_f) × (ℝ × A_f)` into the real
coordinates `ℝ × ℝ` and the finite coordinates `A_f × A_f`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

section Rearrange

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- The measurable equivalence `((a, b), (c, d)) ↦ ((a, c), (b, d))`. -/
def swapMid : ((α × β) × (γ × δ)) ≃ᵐ ((α × γ) × (β × δ)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    show Measurable (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    fun_prop
  measurable_invFun := by
    show Measurable (fun q : (α × γ) × (β × δ) => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
    fun_prop

theorem measurePreserving_swapMid (μα : Measure α) (μβ : Measure β) (μγ : Measure γ) (μδ : Measure δ)
    [SFinite μα] [SFinite μβ] [SFinite μγ] [SFinite μδ] :
    MeasurePreserving (swapMid : ((α × β) × (γ × δ)) ≃ᵐ ((α × γ) × (β × δ)))
      ((μα.prod μβ).prod (μγ.prod μδ)) ((μα.prod μγ).prod (μβ.prod μδ)) := by
  have e1 := measurePreserving_prodAssoc μα μβ (μγ.prod μδ)
  have e2 := (MeasurePreserving.id μα).prod (measurePreserving_prodAssoc μβ μγ μδ).symm
  have e3 := (MeasurePreserving.id μα).prod
    ((Measure.measurePreserving_swap (μ := μβ) (ν := μγ)).prod (MeasurePreserving.id μδ))
  have e4 := (MeasurePreserving.id μα).prod (measurePreserving_prodAssoc μγ μβ μδ)
  have e5 := (measurePreserving_prodAssoc μα μγ (μβ.prod μδ)).symm
  have := e5.comp (e4.comp (e3.comp (e2.comp e1)))
  convert this using 1
  funext p
  rfl

/-- Integration over `(α × β) × (γ × δ)` is iterated integration over `α × γ` and then `β × δ`. -/
theorem integral_swapMid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μα : Measure α) (μβ : Measure β) (μγ : Measure γ) (μδ : Measure δ)
    [SFinite μα] [SFinite μβ] [SFinite μγ] [SFinite μδ]
    (f : (α × β) × (γ × δ) → E) (hf : Integrable f ((μα.prod μβ).prod (μγ.prod μδ))) :
    ∫ p, f p ∂((μα.prod μβ).prod (μγ.prod μδ)) =
      ∫ x : α × γ, ∫ w : β × δ, f ((x.1, w.1), (x.2, w.2)) ∂(μβ.prod μδ) ∂(μα.prod μγ) := by
  have hmp := measurePreserving_swapMid μα μβ μγ μδ
  set g : (α × γ) × (β × δ) → E := fun q => f ((q.1.1, q.2.1), (q.1.2, q.2.2)) with hg
  have hgf : ∀ p, g (swapMid p) = f p := fun p => rfl
  have hint : Integrable g ((μα.prod μγ).prod (μβ.prod μδ)) := by
    have := (hmp.symm.integrable_comp_emb swapMid.symm.measurableEmbedding).mpr hf
    exact this
  have h1 : ∫ p, f p ∂((μα.prod μβ).prod (μγ.prod μδ)) = ∫ q, g q ∂((μα.prod μγ).prod (μβ.prod μδ)) := by
    rw [← hmp.integral_comp' g]
    simp only [hgf]
  rw [h1, integral_prod _ hint]

end Rearrange

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
