module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.Ring.NamePowerVars
public import Mathlib.Topology.WithTopology

@[expose] public section

open Polynomial

noncomputable section

namespace TernaryPoly

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient of the `k`th Hasse derivative in the Todd operator. -/
def toddCoeff (u : R) (k : ℕ) : R := algebraMap ℚ R (bernoulli k) * (-u)^k

/-- The finite Todd sum with an exclusive upper cutoff. -/
def toddCutoff (u : R) (N : ℕ) : Polynomial R →ₗ[R] Polynomial R :=
  ∑ k ∈ Finset.range N, toddCoeff u k • hasseDeriv k

@[simp] theorem toddCutoff_apply (u : R) (N : ℕ) (p : Polynomial R) :
    toddCutoff u N p = ∑ k ∈ Finset.range N, toddCoeff u k • hasseDeriv k p := by
  simp [toddCutoff]

/-- Increasing a cutoff already beyond the degree adds only zero terms. -/
theorem toddCutoff_eq_of_le (u : R) (p : Polynomial R) {N M : ℕ}
    (hNM : N ≤ M) (hN : p.natDegree < N) :
    toddCutoff u N p = toddCutoff u M p := by
  rw [toddCutoff_apply, toddCutoff_apply]
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro k _ hk
  have hNk : N ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  rw [hasseDeriv_eq_zero_of_lt_natDegree p k (lt_of_lt_of_le hN hNk), smul_zero]

/-- Any two cutoffs strictly above the degree give the same value. -/
theorem toddCutoff_eq (u : R) (p : Polynomial R) {N M : ℕ}
    (hN : p.natDegree < N) (hM : p.natDegree < M) :
    toddCutoff u N p = toddCutoff u M p := by
  exact (toddCutoff_eq_of_le u p (Nat.le_max_left N M) hN).trans
    (toddCutoff_eq_of_le u p (Nat.le_max_right N M) hM).symm

/-- The canonical linear Todd operator, assembled from its monomial values. -/
def todd (u : R) : Polynomial R →ₗ[R] Polynomial R :=
  Polynomial.lsum fun n => (toddCutoff u (n+1)).comp (Polynomial.monomial n)

/-- On a monomial the canonical operator uses the natural finite cutoff. -/
theorem todd_monomial_cutoff (u : R) (n : ℕ) (r : R) :
    todd u (monomial n r) = toddCutoff u (n+1) (monomial n r) := by
  simp [todd, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

/-- The canonical Todd operator agrees with every valid finite cutoff. -/
theorem todd_eq_cutoff (u : R) (p : Polynomial R) (N : ℕ)
    (hN : p.natDegree < N) : todd u p = toddCutoff u N p := by
  classical
  calc
    todd u p = ∑ n ∈ p.support,
        toddCutoff u (n+1) (monomial n (p.coeff n)) := by
      simp [todd, Polynomial.lsum_apply, Polynomial.sum_def]
    _ = ∑ n ∈ p.support, toddCutoff u N (monomial n (p.coeff n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply toddCutoff_eq
      · exact lt_of_le_of_lt (natDegree_monomial_le _) (Nat.lt_succ_self n)
      · exact lt_of_le_of_lt (natDegree_monomial_le _)
          (lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp n hn) hN)
    _ = toddCutoff u N p := by
      rw [← map_sum]
      congr 1
      exact Polynomial.sum_monomial_eq p

/-- A cutoff-free Todd operator can always be expanded into a terminating Hasse sum. -/
theorem todd_eq_sum (u : R) (p : Polynomial R) (N : ℕ)
    (hN : p.natDegree < N) :
    todd u p = ∑ k ∈ Finset.range N,
      (algebraMap ℚ R (bernoulli k) * (-u)^k) • hasseDeriv k p := by
  rw [todd_eq_cutoff u p N hN, toddCutoff_apply]
  rfl

/-- The standard terminating formula includes the top possible Hasse derivative. -/
theorem todd_apply (u : R) (p : Polynomial R) :
    todd u p = ∑ k ∈ Finset.range (p.natDegree+1),
      (algebraMap ℚ R (bernoulli k) * (-u)^k) • hasseDeriv k p :=
  todd_eq_sum u p (p.natDegree+1) (Nat.lt_succ_self _)

/-- The explicit monomial formula for the Todd operator. -/
theorem todd_monomial (u : R) (n : ℕ) (r : R) :
    todd u (monomial n r) = ∑ k ∈ Finset.range (n+1),
      monomial (n-k) ((algebraMap ℚ R (bernoulli k) * (-u)^k) *
        ((n.choose k : R) * r)) := by
  rw [todd_monomial_cutoff, toddCutoff_apply]
  simp only [hasseDeriv_monomial, smul_monomial, smul_eq_mul, toddCoeff]

/-- Todd operators never increase the polynomial degree. -/
theorem natDegree_todd_le (u : R) (p : Polynomial R) :
    (todd u p).natDegree ≤ p.natDegree := by
  rw [todd_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_smul_le _ _).trans
    ((natDegree_hasseDeriv_le p k).trans (Nat.sub_le _ _))

omit [Algebra ℚ R] in
/-- Hasse derivatives commute in the polynomial direction. -/
theorem hasseDeriv_commute (k l : ℕ) (p : Polynomial R) :
    hasseDeriv k (hasseDeriv l p) = hasseDeriv l (hasseDeriv k p) := by
  have h : (hasseDeriv (R := R) k).comp (hasseDeriv l) =
      (hasseDeriv l).comp (hasseDeriv k) := by
    rw [hasseDeriv_comp, hasseDeriv_comp, Nat.choose_symm_add, Nat.add_comm k l]
  exact DFunLike.congr_fun h p

/-- Todd operators commute with every Hasse derivative. -/
theorem hasseDeriv_todd (u : R) (k : ℕ) (p : Polynomial R) :
    hasseDeriv k (todd u p) = todd u (hasseDeriv k p) := by
  have hdegree : (hasseDeriv k p).natDegree < p.natDegree+1 :=
    lt_of_le_of_lt ((natDegree_hasseDeriv_le p k).trans (Nat.sub_le _ _))
      (Nat.lt_succ_self _)
  rw [todd_eq_sum u p (p.natDegree+1) (Nat.lt_succ_self _),
    todd_eq_sum u (hasseDeriv k p) (p.natDegree+1) hdegree, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, hasseDeriv_commute]

/-- In particular, the ordinary derivative commutes with Todd. -/
theorem derivative_todd (u : R) (p : Polynomial R) :
    derivative (todd u p) = todd u (derivative p) := by
  simpa only [hasseDeriv_one'] using hasseDeriv_todd u 1 p

/-- Todd operators in the same polynomial direction commute. -/
theorem todd_commute (u v : R) (p : Polynomial R) :
    todd u (todd v p) = todd v (todd u p) := by
  rw [todd_eq_sum v p (p.natDegree+1) (Nat.lt_succ_self _),
    todd_eq_sum v (todd u p) (p.natDegree+1)
      (lt_of_le_of_lt (natDegree_todd_le u p) (Nat.lt_succ_self _)), map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, hasseDeriv_todd]

end TernaryPoly
