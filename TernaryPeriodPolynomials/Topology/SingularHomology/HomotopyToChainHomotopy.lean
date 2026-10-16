module

/-
SPDX-License-Identifier: Apache-2.0
Adapted from akopjan/HamSandwich.
Original module: HamSandwich.SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy
Ported to the Lean 4.33.0.
-/
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
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
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Homotopy → chain-homotopy bridge (reduction layer)

This file records the *honest* reduction step on the path from homotopies of
continuous maps to homotopy invariance of singular homology.

Pinned Mathlib (`v4.28.0`)
provides:

* the singular chain / homology functors
  (`AlgebraicTopology.singularChainComplexFunctor`,
  `AlgebraicTopology.singularHomologyFunctor`), and
* the abstract chain-level homotopy invariance of homology
  (`Homotopy.homologyMap_eq`: chain-homotopic maps of homological complexes
  induce *equal* maps on homology).

It does **not** provide the keystone *prism operator* turning a
`ContinuousMap.Homotopy` of two continuous maps into a chain `Homotopy` of the
induced singular chain maps.

What we can record today is the *reduction*: **given** a chain
homotopy between the singular chain maps induced by two continuous maps, the
induced maps on singular homology are equal. The chain homotopy is taken as a
hypothesis, so this is **not** a (fake) homotopy-invariance statement — it is the
genuine, reusable consumer of the still-missing prism operator. Once that
operator is constructed, feeding its output into
`singularHomologyMap_eq_of_singularChainHomotopy` yields homotopy invariance of
singular homology immediately.

We fix integer coefficients (`R = ℤ` in `ModuleCat.{0} ℤ`), the case relevant to
the eventual topological degree of sphere maps.
-/

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- The integral singular chain complex functor `TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ`,
i.e. `singularChainComplexFunctor` specialised to coefficients `ℤ`. -/
noncomputable abbrev singularChainℤ :
    TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The `n`-th integral singular homology functor `TopCat ⥤ ModuleCat ℤ`,
i.e. `singularHomologyFunctor` specialised to coefficients `ℤ`. -/
noncomputable abbrev singularHomologyℤ (n : ℕ) :
    TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)

/-- **Reduction lemma (honest consumer of the missing prism operator).**

If the singular chain maps induced by two continuous maps `f, g : X ⟶ Y` are
chain-homotopic, then the induced maps on the `n`-th integral singular homology
are equal.

The chain homotopy `H` is a *hypothesis*: this is the reusable step that turns the
still-missing prism operator (`ContinuousMap.Homotopy → Homotopy (chain maps)`)
into homotopy invariance of singular homology, via `Homotopy.homologyMap_eq`. It
is therefore not a homotopy-invariance theorem on its own. -/
theorem singularHomologyMap_eq_of_singularChainHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  exact H.homologyMap_eq n

end SphereOddDegree
