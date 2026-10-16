module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
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


/-! Genuine bilinear integration of everywhere-integrable real-valued pairings. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open MeasureTheory
variable {A B X : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [MeasurableSpace X]

/-- A genuine bilinear function-valued pairing whose every value is integrable induces its
literal integral bilinear pairing. -/
def integrableBilinearIntegral (μ : Measure X) (P : A →ₗ[ℝ] B →ₗ[ℝ] (X → ℝ))
    (hP : ∀ a b, Integrable (P a b) μ) : A →ₗ[ℝ] B →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun b := ∫ x, P a b x ∂μ
      map_add' b c := by
        rw [map_add]
        exact integral_add (hP a b) (hP a c)
      map_smul' r b := by
        rw [map_smul]
        exact integral_smul r _ }
  map_add' a c := by
    apply LinearMap.ext
    intro b
    change (∫ x, P (a+c) b x ∂μ) = _
    simp only [map_add, LinearMap.add_apply]
    exact integral_add (hP a b) (hP c b)
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    change (∫ x, P (r • a) b x ∂μ) = _
    simp only [map_smul, LinearMap.smul_apply]
    exact integral_smul r _

end TernaryPoly.PolynomialFormWeakSmooth
