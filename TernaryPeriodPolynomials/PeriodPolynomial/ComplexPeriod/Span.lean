module

public import TernaryPeriodPolynomials.PeriodPolynomial.ComplexPeriod.Space
public import TernaryPeriodPolynomials.ModularForm.CommutingEigenvector
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryComplexPeriod

@[simp] theorem extend_zero {K F : Type*} [Field K] [Field F] (φ : K →+* F) (d : ℕ) :
    extend φ d 0=0 := by
  apply Subtype.ext
  exact map_zero (MvPolynomial.map φ)

/-- The actual complex span of a rational period subspace, using coefficient extension. -/
def complexSpan (d : ℕ) (L : Submodule ℚ (space ℚ d)) : Submodule ℂ (space ℂ d) :=
  Submodule.span ℂ ((extend (algebraMap ℚ ℂ) d) '' (L : Set (space ℚ d)))

/-- Complexifying a rational subspace is faithful. -/
theorem complexSpan_eq_bot_iff (d : ℕ) (L : Submodule ℚ (space ℚ d)) :
    complexSpan d L=⊥ ↔ L=⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro q hq
    have he : extend (algebraMap ℚ ℂ) d q ∈ complexSpan d L :=
      Submodule.subset_span ⟨q,hq,rfl⟩
    rw [h] at he
    apply (Submodule.mem_bot ℚ).mpr
    apply extend_injective (algebraMap ℚ ℂ) d
    simpa only [extend_zero] using (Submodule.mem_bot ℂ).mp he
  · intro h
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro q ⟨p,hp,rfl⟩
    change p ∈ L at hp
    rw [h,Submodule.mem_bot] at hp
    simp only [hp,extend_zero,SetLike.mem_coe,Submodule.zero_mem]

/-- Vanishing of the actual extreme functional survives complexification of a rational subspace. -/
theorem complexSpan_extreme (d : ℕ) (L : Submodule ℚ (space ℚ d))
    (hL : ∀ q ∈ L, extreme ℚ d q=0) :
    ∀ q ∈ complexSpan d L, extreme ℂ d q=0 := by
  have hk : complexSpan d L ≤ (extreme ℂ d).ker := by
    apply Submodule.span_le.mpr
    rintro q ⟨p,hp,rfl⟩
    change extreme ℂ d (extend (algebraMap ℚ ℂ) d p)=0
    rw [extreme_extend,hL p hp,map_zero]
  intro q hq
  exact hk hq

/-- A literal intertwining identity transports actual rational stability to its complex span. -/
theorem complexSpan_stable (d : ℕ) (L : Submodule ℚ (space ℚ d))
    (T : Module.End ℚ (space ℚ d)) (U : Module.End ℂ (space ℂ d))
    (hs : ∀ q ∈ L,T q ∈ L)
    (hn : ∀ q, U (extend (algebraMap ℚ ℂ) d q)=extend (algebraMap ℚ ℂ) d (T q)) :
    ∀ q ∈ complexSpan d L,U q ∈ complexSpan d L := by
  have h : complexSpan d L ≤ (complexSpan d L).comap U := by
    apply Submodule.span_le.mpr
    rintro q ⟨p,hp,rfl⟩
    change U (extend (algebraMap ℚ ℂ) d p) ∈ complexSpan d L
    rw [hn]
    exact Submodule.subset_span ⟨T p,hs p hp,rfl⟩
  exact h

/-- The linear-algebra step for the actual binary extreme-coefficient argument.
The operators, compatibility, and common-eigenvector detection remain explicit inputs. -/
theorem rational_eq_bot_of_eigen_detection {I : Type*} (d : ℕ)
    (T : I → Module.End ℚ (space ℚ d)) (U : I → Module.End ℂ (space ℂ d))
    (hc : ∀ i j,Commute (U i) (U j))
    (hn : ∀ i q,U i (extend (algebraMap ℚ ℂ) d q)=extend (algebraMap ℚ ℂ) d (T i q))
    (hd : ∀ q : space ℂ d,q≠0 → (∀ i,∃ a : ℂ,U i q=a • q) → extreme ℂ d q≠0)
    (L : Submodule ℚ (space ℚ d)) (hs : ∀ i q,q ∈ L → T i q ∈ L)
    (hz : ∀ q ∈ L,extreme ℚ d q=0) : L=⊥ := by
  apply (complexSpan_eq_bot_iff d L).mp
  exact CommutingEigenvector.eq_bot_of_functional U hc (extreme ℂ d) hd (complexSpan d L)
    (fun i => complexSpan_stable d L (T i) (U i) (hs i) (hn i))
    (complexSpan_extreme d L hz)

end TernaryPoly.BinaryComplexPeriod
