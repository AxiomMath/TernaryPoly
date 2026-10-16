module

/-
Adapted geometric part of akopjan/HamSandwich, Apache-2.0.
Original: SphereOddDegree/AlgebraicTopology/SphereHomologyMVStep.lean.
-/
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
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
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSphere
open Metric

/-- The literal Euclidean unit sphere of dimension n. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

variable (n : ℕ)

/-- The north pole of `Sⁿ⁺¹` as a unit vector `e₀`. -/
def northVec : EuclideanSpace ℝ (Fin (n + 2)) := EuclideanSpace.single 0 1

theorem norm_northVec : ‖northVec n‖ = 1 := by
  simp [northVec]

/-- The north pole of `Sⁿ⁺¹`. -/
def northPole : Sphere (n + 1) := ⟨northVec n, by simp [norm_northVec]⟩

/-- The south pole of `Sⁿ⁺¹`, the antipode of the north pole. -/
def southPole : Sphere (n + 1) := ⟨-northVec n, by simp [norm_northVec]⟩

theorem northPole_ne_southPole : northPole n ≠ southPole n := by
  intro h
  apply_fun Subtype.val at h
  simp only [northPole, southPole] at h
  have hv : northVec n = 0 := by
    have h2 : (2 : ℝ) • northVec n = 0 := by rw [two_smul]; nth_rewrite 2 [h]; abel
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact h0
  have hnorm := norm_northVec n
  rw [hv, norm_zero] at hnorm
  norm_num at hnorm

/-- The upper punctured sphere `Sⁿ⁺¹ \ {north}`. -/
def upperPunctured : Set (Sphere (n + 1)) := {northPole n}ᶜ

/-- The lower punctured sphere `Sⁿ⁺¹ \ {south}`. -/
def lowerPunctured : Set (Sphere (n + 1)) := {southPole n}ᶜ

theorem isOpen_upperPunctured : IsOpen (upperPunctured n) :=
  isOpen_compl_singleton

theorem isOpen_lowerPunctured : IsOpen (lowerPunctured n) :=
  isOpen_compl_singleton

theorem upper_union_lower : upperPunctured n ∪ lowerPunctured n = Set.univ := by
  rw [upperPunctured, lowerPunctured, ← Set.compl_inter]
  rw [Set.compl_univ_iff, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  rw [Set.mem_singleton_iff] at hx1 hx2
  exact northPole_ne_southPole n (hx1 ▸ hx2)

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}`. -/
def sphereBand : Set (Sphere (n + 1)) := upperPunctured n ∩ lowerPunctured n

/-! ## Contractibility of the punctured spheres -/

instance contractible_upperPunctured : ContractibleSpace (upperPunctured n) := by
  let e := stereographic (norm_northVec n)
  have : ContractibleSpace e.target := by
    change ContractibleSpace (Set.univ : Set (ℝ ∙ northVec n)ᗮ)
    exact (Homeomorph.Set.univ _).contractibleSpace
  exact e.toHomeomorphSourceTarget.contractibleSpace

instance contractible_lowerPunctured : ContractibleSpace (lowerPunctured n) := by
  let e := stereographic (by simp [norm_northVec] : ‖-northVec n‖ = 1)
  have : ContractibleSpace e.target := by
    change ContractibleSpace (Set.univ : Set (ℝ ∙ -northVec n)ᗮ)
    exact (Homeomorph.Set.univ _).contractibleSpace
  exact e.toHomeomorphSourceTarget.contractibleSpace

/-! ## The equatorial band is homotopy equivalent to `Sⁿ` -/

/-
The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`.
-/
/-! ### Construction of the band ≃ Sⁿ homotopy equivalence -/

/-- The squared norm of the equatorial part (coordinates `1 .. n+1`) of a point of
`Sⁿ⁺¹`. -/
def eqNormSq (x : Sphere (n + 1)) : ℝ := ∑ i : Fin (n + 1), (x.val i.succ) ^ 2

theorem eqNormSq_eq (x : Sphere (n + 1)) : eqNormSq n x = 1 - (x.val 0) ^ 2 := by
  have h_norm_sq : ‖x.val‖^2 = ∑ i : Fin (n + 2), (x.val i)^2 := by
    rw [ EuclideanSpace.norm_eq ];
    rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, Finset.sum_congr rfl fun _ _ => by rw [ Real.norm_eq_abs, sq_abs ] ];
  simp_all +decide [ Fin.sum_univ_succ, eqNormSq ]

theorem eqNormSq_pos {x : Sphere (n + 1)} (hx : x ∈ sphereBand n) : 0 < eqNormSq n x := by
  contrapose! hx;
  -- Since `eqNormSq n x ≤ 0`, we have `x.val i.succ = 0` for all `i : Fin (n + 1)`.
  have h_zero : ∀ i : Fin (n + 1), x.val i.succ = 0 := by
    exact fun i => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( x.val ( Fin.succ a ) ) ) ( Finset.mem_univ i ) ) hx ) ( sq_nonneg _ ) );
  -- Since `x.val i.succ = 0` for all `i : Fin (n + 1)`, we have `x.val = northVec n` or `x.val = -northVec n`.
  have h_eq : x.val = northVec n ∨ x.val = -northVec n := by
    have h_eq : x.val 0 = 1 ∨ x.val 0 = -1 := by
      have h_eq : (x.val 0)^2 = 1 := by
        have := eqNormSq_eq n x;
        linarith [ show 0 ≤ eqNormSq n x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
      exact sq_eq_one_iff.mp h_eq;
    exact Or.imp ( fun h => by ext i; induction i using Fin.inductionOn <;> aesop ) ( fun h => by ext i; induction i using Fin.inductionOn <;> aesop ) h_eq;
  intro h
  rcases h_eq with hN | hS
  · exact h.1 (Subtype.ext hN)
  · exact h.2 (Subtype.ext hS)


end TernaryPoly.RationalSphere
