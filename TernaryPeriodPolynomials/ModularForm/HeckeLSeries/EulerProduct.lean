module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Algebra.TransferInstance
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
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.Data.List.Enum
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Factorization.PrimePow
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
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryHeckeEulerProduct

/-- A summable second-order Hecke sequence has a nonvanishing local Euler factor.
No estimate on the roots of its Euler polynomial is required. -/
theorem local_euler_identity (a : ℕ → ℂ) (c : ℂ) (ha0 : a 0=1)
    (hr : ∀ n,a (n+2)=a 1*a (n+1)-c*a n) (hs : Summable a) :
    (1-a 1+c)*(∑' n,a n)=1 := by
  have hs1 : Summable (fun n => a (n+1)) := (summable_nat_add_iff 1).mpr hs
  have h1 := hs.tsum_eq_zero_add
  rw [ha0] at h1
  have h2 := hs1.tsum_eq_zero_add
  change (∑' n,a (n+1))=a 1+∑' n,a (n+2) at h2
  have h3 : (∑' n,a (n+2))=a 1*(∑' n,a (n+1))-c*(∑' n,a n) := by
    simp_rw [hr]
    rw [(hs1.mul_left _).tsum_sub (hs.mul_left _),tsum_mul_left,tsum_mul_left]
  linear_combination (1-a 1)*h1+h2+h3

/-- Positive prime powers are pairwise distinct across both prime and exponent. -/
theorem primePower_injective : Function.Injective
    (fun z : Nat.Primes × ℕ => z.1.val^(z.2+1)) := by
  intro x y h
  obtain ⟨hp,he⟩ := Nat.Prime.pow_inj ((Nat.irreducible_iff_nat_prime _).mp x.1.property)
    ((Nat.irreducible_iff_nat_prime _).mp y.1.property) h
  exact Prod.ext (Subtype.ext hp) he

/-- Absolute convergence controls the sum of all deviations of local Euler factors from one. -/
theorem local_tail_summable (f : ℕ → ℂ) (hs : Summable (fun n => ‖f n‖)) :
    Summable (fun p : Nat.Primes => ‖∑' n,f (p.val^(n+1))‖) := by
  have hp : Summable (fun z : Nat.Primes × ℕ => ‖f (z.1.val^(z.2+1))‖) :=
    hs.comp_injective primePower_injective
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_tsum_le_tsum_norm (hp.prod_factor p)) hp.prod

/-- An absolutely summable multiplicative sequence with the actual second-order prime recurrence
has nonzero total sum. This applies directly to absolutely convergent Hecke Dirichlet coefficients. -/
theorem multiplicative_tsum_ne_zero (f : ℕ → ℂ) (c : Nat.Primes → ℂ)
    (hf0 : f 0=0) (hf1 : f 1=1)
    (hm : ∀ m n, m.Coprime n → f (m*n)=f m*f n)
    (hr : ∀ p : Nat.Primes, ∀ r : ℕ,
      f (p.val^(r+2))=f p.val*f (p.val^(r+1))-c p*f (p.val^r))
    (hs : Summable (fun n => ‖f n‖)) : (∑' n,f n)≠0 := by
  have htail (p : Nat.Primes) : Summable (fun n => f (p.val^(n+1))) :=
    ((hs.comp_injective primePower_injective).prod_factor p).of_norm
  have hlocal (p : Nat.Primes) : Summable (fun n => f (p.val^n)) :=
    (summable_nat_add_iff 1).mp (htail p)
  have hform (p : Nat.Primes) : (∑' n,f (p.val^n))=1+∑' n,f (p.val^(n+1)) := by
    simpa only [pow_zero,hf1] using (hlocal p).tsum_eq_zero_add
  have hn (p : Nat.Primes) : 1+(∑' n,f (p.val^(n+1)))≠0 := by
    have he := local_euler_identity (fun r => f (p.val^r)) (c p)
      (by simpa only [pow_zero] using hf1) (by simpa only [pow_one] using hr p) (hlocal p)
    rw [hform] at he
    intro hz
    rw [hz,mul_zero] at he
    exact zero_ne_one he
  have hp := tprod_one_add_ne_zero_of_summable hn (local_tail_summable f hs)
  have he := EulerProduct.eulerProduct_hasProd hf1 (fun {m n} h => hm m n h) hs hf0
  rw [← he.tprod_eq]
  simpa only [hform] using hp

end TernaryPoly.BinaryHeckeEulerProduct
