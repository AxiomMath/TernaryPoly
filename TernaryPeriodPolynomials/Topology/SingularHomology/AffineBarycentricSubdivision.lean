module

/-
SPDX-License-Identifier: Apache-2.0
Adapted from akopjan/HamSandwich.
Original module: HamSandwich.SphereOddDegree.AlgebraicTopology.AffineBarycentricSubdivision
Ported to the Lean 4.33.0.
-/
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Affine barycentric subdivision maps on topological standard simplices

This file supplies the raw affine layer needed before the singular-chain
barycentric subdivision operator.

For a permutation `π : Equiv.Perm (Fin (n+1))`, the `π`-summand of the
barycentric subdivision of the topological standard simplex has vertices

`b_k = barycenter {π 0, ..., π k}`.

The file defines:

* `prefixVertex`      : the ordered prefix map `Fin (k+1) -> Fin (n+1)`;
* `prefixBarycenter`  : the barycenter of the first `k+1` vertices in that
  permuted order, as a point of `StdSimplex ℝ (Fin (n+1))`;
* `affineSubdivMap`   : the affine self-map of `Δ^n` sending vertex `k` to
  `prefixBarycenter n π k`.

This deliberately does **not** claim the chain-level boundary identity or the
subdivision chain homotopy.
-/

open scoped BigOperators
open Finset Convexity

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The ambient topological `n`-simplex, represented by its nonnegative barycentric weights on
`Fin (n+1)` summing to `1`. -/
abbrev Delta (n : ℕ) := StdSimplex ℝ (Fin (n + 1))

/-- The metric on `Δⁿ` induced by its barycentric weight vectors in `Fin (n+1) → ℝ`; it
induces the standard topology of the simplex. -/
noncomputable instance (n : ℕ) : MetricSpace (Delta n) :=
  (MetricSpace.induced (fun t : Delta n => ⇑t.weights)
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective inferInstance).replaceTopology
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).eq_induced

/-- The barycentric weight map is an isometric embedding of `Δⁿ` into `Fin (n+1) → ℝ`. -/
theorem isometry_weights (n : ℕ) : Isometry (fun t : Delta n => ⇑t.weights) :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- The barycentric weights of the image of a point under a vertex map: the weight at `y` is
the total weight of the fibre over `y`. -/
theorem weights_map_apply {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y)
    (s : StdSimplex ℝ X) (y : Y) :
    (StdSimplex.map f s).weights y = ∑ x with f x = y, s.weights x := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => Finsupp.single_apply

/-- The point of the standard simplex with prescribed barycentric coordinates. -/
noncomputable def ofWeights {X : Type*} [Fintype X] (f : X → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∑ i, f i = 1) : StdSimplex ℝ X where
  weights := Finsupp.equivFunOnFinite.symm f
  nonneg := h0
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact h1

@[simp] theorem ofWeights_weights {X : Type*} [Fintype X] (f : X → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∑ i, f i = 1) (i : X) : (ofWeights f h0 h1).weights i = f i := rfl

/-- The `k`-prefix vertex map associated to a permutation of the vertices of
`Δ^n`.  It sends `0,...,k` into `Fin (n+1)` by the permuted order `π`. -/
def prefixVertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    Fin (k.val + 1) → Fin (n + 1) :=
  fun i => π ⟨i.val, by
    have hi : i.val < k.val + 1 := i.isLt
    have hk : k.val < n + 1 := k.isLt
    omega⟩

/-- The barycenter of the first `k+1` vertices in the order given by `π`,
viewed as a point of the ambient simplex `Δ^n`.  This uses Mathlib's existing
`StdSimplex.barycenter` and `StdSimplex.map`, avoiding a hand proof that the
coordinates are nonnegative and have total mass `1`. -/
noncomputable def prefixBarycenter (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Delta n :=
  StdSimplex.map (prefixVertex n π k)
    (StdSimplex.barycenter (M := Fin (k.val + 1)) (K := ℝ))

/-- Coordinate formula for `prefixBarycenter`.  In words, the `j`-coordinate is
`1/(k+1)` if `j` occurs among `π 0, ..., π k`, and `0` otherwise.

-/
theorem prefixBarycenter_def (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    prefixBarycenter n π k =
      StdSimplex.map (prefixVertex n π k)
        (StdSimplex.barycenter (M := Fin (k.val + 1)) (K := ℝ)) := rfl

/-- The coordinate function of the affine map attached to the permutation `π`.
It is the convex combination of the prefix barycenters with weights given by
`x`. -/
noncomputable def affineSubdivMapFun (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) : Fin (n + 1) → ℝ :=
  fun j => ∑ k : Fin (n + 1), (x.weights k) * ((prefixBarycenter n π k).weights j)

/-- Nonnegativity of every coordinate of `affineSubdivMapFun`. -/
theorem affineSubdivMapFun_nonneg (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    0 ≤ affineSubdivMapFun n π x j := by
  unfold affineSubdivMapFun
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (x.weights_nonneg k) ((prefixBarycenter n π k).weights_nonneg j)

/-- The coordinates of `affineSubdivMapFun` sum to `1`. -/
theorem affineSubdivMapFun_sum_eq_one (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) :
    (∑ j : Fin (n + 1), affineSubdivMapFun n π x j) = 1 := by
  unfold affineSubdivMapFun
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin (n + 1),
      (∑ j : Fin (n + 1), x.weights k * (prefixBarycenter n π k).weights j) = x.weights k := by
    intro k
    rw [← Finset.mul_sum, StdSimplex.total_of_fintype, mul_one]
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  exact x.total_of_fintype

/-- The affine self-map of `Δ^n` associated to a permutation `π`; this is the
geometric simplex appearing as one signed summand in barycentric subdivision. -/
noncomputable def affineSubdivMap (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Delta n → Delta n :=
  fun x => ofWeights (affineSubdivMapFun n π x) (affineSubdivMapFun_nonneg n π x)
    (affineSubdivMapFun_sum_eq_one n π x)

@[simp] theorem affineSubdivMap_apply (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    (affineSubdivMap n π x).weights j =
      ∑ k : Fin (n + 1), x.weights k * (prefixBarycenter n π k).weights j := rfl

/-- The affine map sends the `k`-th vertex of the domain simplex to the
`k`-th prefix barycenter. -/
theorem affineSubdivMap_vertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineSubdivMap n π (StdSimplex.single (R := ℝ) k) = prefixBarycenter n π k := by
  ext j
  simp only [affineSubdivMap_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Finsupp.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Naturality of the construction under postcomposition of the vertex
permutation.  This is a lightweight bookkeeping lemma useful when comparing
adjacent permutation summands later. -/
theorem prefixVertex_comp (n : ℕ) (π τ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    prefixVertex n (τ.trans π) k = fun i => π (prefixVertex n τ k i) := by
  funext i
  rfl

/-- The first prefix barycenter is the first permuted vertex. -/
theorem prefixBarycenter_zero (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    prefixBarycenter n π 0 = StdSimplex.single (R := ℝ) (π 0) := by
  change StdSimplex.map (prefixVertex n π 0)
    (StdSimplex.barycenter (M := Fin 1) (K := ℝ)) = _
  rw [StdSimplex.barycenter_fin_one]
  exact StdSimplex.map_single (0 : Fin 1) (prefixVertex n π 0)


end AffineBarycentricSubdivision
end SphereOddDegree
