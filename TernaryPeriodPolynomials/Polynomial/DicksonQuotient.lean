module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.DicksonQuotient

abbrev Poly := MvPolynomial (Fin 3) (ZMod 2)
def a : Poly := X 0
def b : Poly := X 1
def c : Poly := X 2
def d4 : Poly := a^4+b^2+a*c
def d6 : Poly := a^2*b^2+a^3*c+a*b*c+c^2
def d7 : Poly := a*c*(a*b+c)
def invariantEval : Poly →ₐ[ZMod 2] Poly := bind₁ ![d4,d6,d7]

/-- The 28 standard monomials, ordered as in the finite quotient certificate. -/
def standardMonomial : Fin 28 → Poly :=
  ![1,a,b,a^2,c,a*b,a^3,b^2,a*c,a^2*b,b*c,a*b^2,a^2*c,a^3*b,
    c^2,b^3,a*b*c,a^2*b^2,b^2*c,a*c^2,a*b^3,b*c^2,b^4,a*b^2*c,
    c^3,b^3*c,b^5,b*c^3]

def dicksonIdeal : Ideal Poly := Ideal.span {d4,d6,d7}

def invariantRing : Subalgebra (ZMod 2) Poly := invariantEval.range

def standardSpan : Submodule invariantRing Poly :=
  Submodule.span invariantRing (Set.range standardMonomial)

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n

@[simp] theorem invariantEval_a : invariantEval a = d4 := by simp [invariantEval,a]
@[simp] theorem invariantEval_b : invariantEval b = d6 := by simp [invariantEval,b]
@[simp] theorem invariantEval_c : invariantEval c = d7 := by simp [invariantEval,c]

theorem standardMonomial_mem (i : Fin 28) : standardMonomial i ∈ standardSpan :=
  Submodule.subset_span ⟨i,rfl⟩

theorem invariant_mul_standard_mem (p : Poly) (i : Fin 28) :
    invariantEval p * standardMonomial i ∈ standardSpan :=
  standardSpan.smul_mem (⟨invariantEval p,invariantEval.mem_range_self p⟩ : invariantRing)
    (standardMonomial_mem i)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_0 : a * standardMonomial 0 =
    invariantEval (1) * standardMonomial 1 := by
  have h : a * (1) = (1) * (a) := by
    ring
  change a * (1) = invariantEval (1) * (a)
  simpa only [map_one] using h

private theorem mul_standard_0_0_mem : a * standardMonomial 0 ∈ standardSpan := by
  rw [mul_standard_0_0]
  exact (invariant_mul_standard_mem (1) 1)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_1 : a * standardMonomial 1 =
    invariantEval (1) * standardMonomial 3 := by
  have h : a * (a) = (1) * (a^2) := by
    ring
  change a * (a) = invariantEval (1) * (a^2)
  simpa only [map_one] using h

private theorem mul_standard_0_1_mem : a * standardMonomial 1 ∈ standardSpan := by
  rw [mul_standard_0_1]
  exact (invariant_mul_standard_mem (1) 3)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_2 : a * standardMonomial 2 =
    invariantEval (1) * standardMonomial 5 := by
  have h : a * (b) = (1) * (a*b) := by
    ring
  change a * (b) = invariantEval (1) * (a*b)
  simpa only [map_one] using h

private theorem mul_standard_0_2_mem : a * standardMonomial 2 ∈ standardSpan := by
  rw [mul_standard_0_2]
  exact (invariant_mul_standard_mem (1) 5)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_3 : a * standardMonomial 3 =
    invariantEval (1) * standardMonomial 6 := by
  have h : a * (a^2) = (1) * (a^3) := by
    ring
  change a * (a^2) = invariantEval (1) * (a^3)
  simpa only [map_one] using h

private theorem mul_standard_0_3_mem : a * standardMonomial 3 ∈ standardSpan := by
  rw [mul_standard_0_3]
  exact (invariant_mul_standard_mem (1) 6)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_4 : a * standardMonomial 4 =
    invariantEval (1) * standardMonomial 8 := by
  have h : a * (c) = (1) * (a*c) := by
    ring
  change a * (c) = invariantEval (1) * (a*c)
  simpa only [map_one] using h

private theorem mul_standard_0_4_mem : a * standardMonomial 4 ∈ standardSpan := by
  rw [mul_standard_0_4]
  exact (invariant_mul_standard_mem (1) 8)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_5 : a * standardMonomial 5 =
    invariantEval (1) * standardMonomial 9 := by
  have h : a * (a*b) = (1) * (a^2*b) := by
    ring
  change a * (a*b) = invariantEval (1) * (a^2*b)
  simpa only [map_one] using h

private theorem mul_standard_0_5_mem : a * standardMonomial 5 ∈ standardSpan := by
  rw [mul_standard_0_5]
  exact (invariant_mul_standard_mem (1) 9)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_6 : a * standardMonomial 6 =
    invariantEval (a) * standardMonomial 0 + invariantEval (1) * standardMonomial 7 + invariantEval (1) * standardMonomial 8 := by
  have h : a * (a^3) = (d4) * (1) + (1) * (b^2) + (1) * (a*c) := by
    unfold d4
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a^3) = invariantEval (a) * (1) + invariantEval (1) * (b^2) + invariantEval (1) * (a*c)
  simpa only [map_one, invariantEval_a] using h

private theorem mul_standard_0_6_mem : a * standardMonomial 6 ∈ standardSpan := by
  rw [mul_standard_0_6]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (a) 0) (invariant_mul_standard_mem (1) 7)) (invariant_mul_standard_mem (1) 8))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_7 : a * standardMonomial 7 =
    invariantEval (1) * standardMonomial 11 := by
  have h : a * (b^2) = (1) * (a*b^2) := by
    ring
  change a * (b^2) = invariantEval (1) * (a*b^2)
  simpa only [map_one] using h

private theorem mul_standard_0_7_mem : a * standardMonomial 7 ∈ standardSpan := by
  rw [mul_standard_0_7]
  exact (invariant_mul_standard_mem (1) 11)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_8 : a * standardMonomial 8 =
    invariantEval (1) * standardMonomial 12 := by
  have h : a * (a*c) = (1) * (a^2*c) := by
    ring
  change a * (a*c) = invariantEval (1) * (a^2*c)
  simpa only [map_one] using h

private theorem mul_standard_0_8_mem : a * standardMonomial 8 ∈ standardSpan := by
  rw [mul_standard_0_8]
  exact (invariant_mul_standard_mem (1) 12)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_9 : a * standardMonomial 9 =
    invariantEval (1) * standardMonomial 13 := by
  have h : a * (a^2*b) = (1) * (a^3*b) := by
    ring
  change a * (a^2*b) = invariantEval (1) * (a^3*b)
  simpa only [map_one] using h

private theorem mul_standard_0_9_mem : a * standardMonomial 9 ∈ standardSpan := by
  rw [mul_standard_0_9]
  exact (invariant_mul_standard_mem (1) 13)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_10 : a * standardMonomial 10 =
    invariantEval (1) * standardMonomial 16 := by
  have h : a * (b*c) = (1) * (a*b*c) := by
    ring
  change a * (b*c) = invariantEval (1) * (a*b*c)
  simpa only [map_one] using h

private theorem mul_standard_0_10_mem : a * standardMonomial 10 ∈ standardSpan := by
  rw [mul_standard_0_10]
  exact (invariant_mul_standard_mem (1) 16)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_11 : a * standardMonomial 11 =
    invariantEval (1) * standardMonomial 17 := by
  have h : a * (a*b^2) = (1) * (a^2*b^2) := by
    ring
  change a * (a*b^2) = invariantEval (1) * (a^2*b^2)
  simpa only [map_one] using h

private theorem mul_standard_0_11_mem : a * standardMonomial 11 ∈ standardSpan := by
  rw [mul_standard_0_11]
  exact (invariant_mul_standard_mem (1) 17)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_12 : a * standardMonomial 12 =
    invariantEval (b) * standardMonomial 0 + invariantEval (1) * standardMonomial 14 + invariantEval (1) * standardMonomial 16 + invariantEval (1) * standardMonomial 17 := by
  have h : a * (a^2*c) = (d6) * (1) + (1) * (c^2) + (1) * (a*b*c) + (1) * (a^2*b^2) := by
    unfold d6
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a^2*c) = invariantEval (b) * (1) + invariantEval (1) * (c^2) + invariantEval (1) * (a*b*c) + invariantEval (1) * (a^2*b^2)
  simpa only [map_one, invariantEval_b] using h

private theorem mul_standard_0_12_mem : a * standardMonomial 12 ∈ standardSpan := by
  rw [mul_standard_0_12]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b) 0) (invariant_mul_standard_mem (1) 14)) (invariant_mul_standard_mem (1) 16)) (invariant_mul_standard_mem (1) 17))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_13 : a * standardMonomial 13 =
    invariantEval (a) * standardMonomial 2 + invariantEval (1) * standardMonomial 15 + invariantEval (1) * standardMonomial 16 := by
  have h : a * (a^3*b) = (d4) * (b) + (1) * (b^3) + (1) * (a*b*c) := by
    unfold d4
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a^3*b) = invariantEval (a) * (b) + invariantEval (1) * (b^3) + invariantEval (1) * (a*b*c)
  simpa only [map_one, invariantEval_a] using h

private theorem mul_standard_0_13_mem : a * standardMonomial 13 ∈ standardSpan := by
  rw [mul_standard_0_13]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (a) 2) (invariant_mul_standard_mem (1) 15)) (invariant_mul_standard_mem (1) 16))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_14 : a * standardMonomial 14 =
    invariantEval (1) * standardMonomial 19 := by
  have h : a * (c^2) = (1) * (a*c^2) := by
    ring
  change a * (c^2) = invariantEval (1) * (a*c^2)
  simpa only [map_one] using h

private theorem mul_standard_0_14_mem : a * standardMonomial 14 ∈ standardSpan := by
  rw [mul_standard_0_14]
  exact (invariant_mul_standard_mem (1) 19)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_15 : a * standardMonomial 15 =
    invariantEval (1) * standardMonomial 20 := by
  have h : a * (b^3) = (1) * (a*b^3) := by
    ring
  change a * (b^3) = invariantEval (1) * (a*b^3)
  simpa only [map_one] using h

private theorem mul_standard_0_15_mem : a * standardMonomial 15 ∈ standardSpan := by
  rw [mul_standard_0_15]
  exact (invariant_mul_standard_mem (1) 20)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_16 : a * standardMonomial 16 =
    invariantEval (c) * standardMonomial 0 + invariantEval (1) * standardMonomial 19 := by
  have h : a * (a*b*c) = (d7) * (1) + (1) * (a*c^2) := by
    unfold d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a*b*c) = invariantEval (c) * (1) + invariantEval (1) * (a*c^2)
  simpa only [map_one, invariantEval_c] using h

private theorem mul_standard_0_16_mem : a * standardMonomial 16 ∈ standardSpan := by
  rw [mul_standard_0_16]
  exact (standardSpan.add_mem (invariant_mul_standard_mem (c) 0) (invariant_mul_standard_mem (1) 19))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_17 : a * standardMonomial 17 =
    invariantEval (c) * standardMonomial 0 + invariantEval (b) * standardMonomial 1 + invariantEval (a) * standardMonomial 4 + invariantEval (1) * standardMonomial 18 + invariantEval (1) * standardMonomial 19 := by
  have h : a * (a^2*b^2) = (d7) * (1) + (d6) * (a) + (d4) * (c) + (1) * (b^2*c) + (1) * (a*c^2) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a^2*b^2) = invariantEval (c) * (1) + invariantEval (b) * (a) + invariantEval (a) * (c) + invariantEval (1) * (b^2*c) + invariantEval (1) * (a*c^2)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_17_mem : a * standardMonomial 17 ∈ standardSpan := by
  rw [mul_standard_0_17]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 0) (invariant_mul_standard_mem (b) 1)) (invariant_mul_standard_mem (a) 4)) (invariant_mul_standard_mem (1) 18)) (invariant_mul_standard_mem (1) 19))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_18 : a * standardMonomial 18 =
    invariantEval (1) * standardMonomial 23 := by
  have h : a * (b^2*c) = (1) * (a*b^2*c) := by
    ring
  change a * (b^2*c) = invariantEval (1) * (a*b^2*c)
  simpa only [map_one] using h

private theorem mul_standard_0_18_mem : a * standardMonomial 18 ∈ standardSpan := by
  rw [mul_standard_0_18]
  exact (invariant_mul_standard_mem (1) 23)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_19 : a * standardMonomial 19 =
    invariantEval (c) * standardMonomial 1 + invariantEval (b) * standardMonomial 3 + invariantEval (a) * standardMonomial 7 + invariantEval (a) * standardMonomial 8 + invariantEval (1) * standardMonomial 22 := by
  have h : a * (a*c^2) = (d7) * (a) + (d6) * (a^2) + (d4) * (b^2) + (d4) * (a*c) + (1) * (b^4) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a*c^2) = invariantEval (c) * (a) + invariantEval (b) * (a^2) + invariantEval (a) * (b^2) + invariantEval (a) * (a*c) + invariantEval (1) * (b^4)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_19_mem : a * standardMonomial 19 ∈ standardSpan := by
  rw [mul_standard_0_19]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 1) (invariant_mul_standard_mem (b) 3)) (invariant_mul_standard_mem (a) 7)) (invariant_mul_standard_mem (a) 8)) (invariant_mul_standard_mem (1) 22))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_20 : a * standardMonomial 20 =
    invariantEval (b) * standardMonomial 2 + invariantEval (b) * standardMonomial 3 + invariantEval (a) * standardMonomial 7 + invariantEval (a) * standardMonomial 8 + invariantEval (1) * standardMonomial 21 + invariantEval (1) * standardMonomial 22 + invariantEval (1) * standardMonomial 23 := by
  have h : a * (a*b^3) = (d6) * (b) + (d6) * (a^2) + (d4) * (b^2) + (d4) * (a*c) + (1) * (b*c^2) + (1) * (b^4) + (1) * (a*b^2*c) := by
    unfold d4 d6
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a*b^3) = invariantEval (b) * (b) + invariantEval (b) * (a^2) + invariantEval (a) * (b^2) + invariantEval (a) * (a*c) + invariantEval (1) * (b*c^2) + invariantEval (1) * (b^4) + invariantEval (1) * (a*b^2*c)
  simpa only [map_one, invariantEval_a, invariantEval_b] using h

private theorem mul_standard_0_20_mem : a * standardMonomial 20 ∈ standardSpan := by
  rw [mul_standard_0_20]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b) 2) (invariant_mul_standard_mem (b) 3)) (invariant_mul_standard_mem (a) 7)) (invariant_mul_standard_mem (a) 8)) (invariant_mul_standard_mem (1) 21)) (invariant_mul_standard_mem (1) 22)) (invariant_mul_standard_mem (1) 23))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_21 : a * standardMonomial 21 =
    invariantEval (c) * standardMonomial 2 + invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (a) * standardMonomial 10 + invariantEval (1) * standardMonomial 24 + invariantEval (1) * standardMonomial 25 := by
  have h : a * (b*c^2) = (d7) * (b) + (d7) * (a^2) + (d6) * (c) + (d4) * (b*c) + (1) * (c^3) + (1) * (b^3*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (b*c^2) = invariantEval (c) * (b) + invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (a) * (b*c) + invariantEval (1) * (c^3) + invariantEval (1) * (b^3*c)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_21_mem : a * standardMonomial 21 ∈ standardSpan := by
  rw [mul_standard_0_21]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 2) (invariant_mul_standard_mem (c) 3)) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (a) 10)) (invariant_mul_standard_mem (1) 24)) (invariant_mul_standard_mem (1) 25))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_22 : a * standardMonomial 22 =
    invariantEval (c) * standardMonomial 2 + invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (b) * standardMonomial 6 + invariantEval (a) * standardMonomial 11 + invariantEval (a) * standardMonomial 12 + invariantEval (1) * standardMonomial 24 := by
  have h : a * (b^4) = (d7) * (b) + (d7) * (a^2) + (d6) * (c) + (d6) * (a^3) + (d4) * (a*b^2) + (d4) * (a^2*c) + (1) * (c^3) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (b^4) = invariantEval (c) * (b) + invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (b) * (a^3) + invariantEval (a) * (a*b^2) + invariantEval (a) * (a^2*c) + invariantEval (1) * (c^3)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_22_mem : a * standardMonomial 22 ∈ standardSpan := by
  rw [mul_standard_0_22]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 2) (invariant_mul_standard_mem (c) 3)) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (b) 6)) (invariant_mul_standard_mem (a) 11)) (invariant_mul_standard_mem (a) 12)) (invariant_mul_standard_mem (1) 24))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_23 : a * standardMonomial 23 =
    invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (a) * standardMonomial 10 + invariantEval (1) * standardMonomial 24 + invariantEval (1) * standardMonomial 25 := by
  have h : a * (a*b^2*c) = (d7) * (a^2) + (d6) * (c) + (d4) * (b*c) + (1) * (c^3) + (1) * (b^3*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (a*b^2*c) = invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (a) * (b*c) + invariantEval (1) * (c^3) + invariantEval (1) * (b^3*c)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_23_mem : a * standardMonomial 23 ∈ standardSpan := by
  rw [mul_standard_0_23]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 3) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (a) 10)) (invariant_mul_standard_mem (1) 24)) (invariant_mul_standard_mem (1) 25))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_24 : a * standardMonomial 24 =
    invariantEval (c) * standardMonomial 4 + invariantEval (c) * standardMonomial 5 + invariantEval (b) * standardMonomial 9 + invariantEval (a) * standardMonomial 15 + invariantEval (a) * standardMonomial 16 + invariantEval (1) * standardMonomial 26 := by
  have h : a * (c^3) = (d7) * (c) + (d7) * (a*b) + (d6) * (a^2*b) + (d4) * (b^3) + (d4) * (a*b*c) + (1) * (b^5) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (c^3) = invariantEval (c) * (c) + invariantEval (c) * (a*b) + invariantEval (b) * (a^2*b) + invariantEval (a) * (b^3) + invariantEval (a) * (a*b*c) + invariantEval (1) * (b^5)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_24_mem : a * standardMonomial 24 ∈ standardSpan := by
  rw [mul_standard_0_24]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 4) (invariant_mul_standard_mem (c) 5)) (invariant_mul_standard_mem (b) 9)) (invariant_mul_standard_mem (a) 15)) (invariant_mul_standard_mem (a) 16)) (invariant_mul_standard_mem (1) 26))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_25 : a * standardMonomial 25 =
    invariantEval (c) * standardMonomial 4 + invariantEval (c) * standardMonomial 5 + invariantEval (c) * standardMonomial 6 + invariantEval (b) * standardMonomial 8 + invariantEval (a) * standardMonomial 16 := by
  have h : a * (b^3*c) = (d7) * (c) + (d7) * (a*b) + (d7) * (a^3) + (d6) * (a*c) + (d4) * (a*b*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (b^3*c) = invariantEval (c) * (c) + invariantEval (c) * (a*b) + invariantEval (c) * (a^3) + invariantEval (b) * (a*c) + invariantEval (a) * (a*b*c)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_25_mem : a * standardMonomial 25 ∈ standardSpan := by
  rw [mul_standard_0_25]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 4) (invariant_mul_standard_mem (c) 5)) (invariant_mul_standard_mem (c) 6)) (invariant_mul_standard_mem (b) 8)) (invariant_mul_standard_mem (a) 16))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_26 : a * standardMonomial 26 =
    invariantEval (a*c) * standardMonomial 0 + invariantEval (c) * standardMonomial 7 + invariantEval (c) * standardMonomial 9 + invariantEval (b) * standardMonomial 10 + invariantEval (b) * standardMonomial 13 + invariantEval (a) * standardMonomial 19 + invariantEval (a) * standardMonomial 20 + invariantEval (1) * standardMonomial 27 := by
  have h : a * (b^5) = (d4*d7) * (1) + (d7) * (b^2) + (d7) * (a^2*b) + (d6) * (b*c) + (d6) * (a^3*b) + (d4) * (a*c^2) + (d4) * (a*b^3) + (1) * (b*c^3) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (b^5) = invariantEval (a*c) * (1) + invariantEval (c) * (b^2) + invariantEval (c) * (a^2*b) + invariantEval (b) * (b*c) + invariantEval (b) * (a^3*b) + invariantEval (a) * (a*c^2) + invariantEval (a) * (a*b^3) + invariantEval (1) * (b*c^3)
  simpa only [map_mul, map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_26_mem : a * standardMonomial 26 ∈ standardSpan := by
  rw [mul_standard_0_26]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (a*c) 0) (invariant_mul_standard_mem (c) 7)) (invariant_mul_standard_mem (c) 9)) (invariant_mul_standard_mem (b) 10)) (invariant_mul_standard_mem (b) 13)) (invariant_mul_standard_mem (a) 19)) (invariant_mul_standard_mem (a) 20)) (invariant_mul_standard_mem (1) 27))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_0_27 : a * standardMonomial 27 =
    invariantEval (b^2) * standardMonomial 0 + invariantEval (a*c) * standardMonomial 1 + invariantEval (a*b) * standardMonomial 3 + invariantEval (a^2) * standardMonomial 7 + invariantEval (a^2) * standardMonomial 8 + invariantEval (c) * standardMonomial 10 + invariantEval (c) * standardMonomial 13 + invariantEval (b) * standardMonomial 14 + invariantEval (b) * standardMonomial 16 + invariantEval (b) * standardMonomial 17 + invariantEval (a) * standardMonomial 22 := by
  have h : a * (b*c^3) = (d6^2) * (1) + (d4*d7) * (a) + (d4*d6) * (a^2) + (d4^2) * (b^2) + (d4^2) * (a*c) + (d7) * (b*c) + (d7) * (a^3*b) + (d6) * (c^2) + (d6) * (a*b*c) + (d6) * (a^2*b^2) + (d4) * (b^4) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change a * (b*c^3) = invariantEval (b^2) * (1) + invariantEval (a*c) * (a) + invariantEval (a*b) * (a^2) + invariantEval (a^2) * (b^2) + invariantEval (a^2) * (a*c) + invariantEval (c) * (b*c) + invariantEval (c) * (a^3*b) + invariantEval (b) * (c^2) + invariantEval (b) * (a*b*c) + invariantEval (b) * (a^2*b^2) + invariantEval (a) * (b^4)
  simpa only [map_mul, map_pow, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_0_27_mem : a * standardMonomial 27 ∈ standardSpan := by
  rw [mul_standard_0_27]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b^2) 0) (invariant_mul_standard_mem (a*c) 1)) (invariant_mul_standard_mem (a*b) 3)) (invariant_mul_standard_mem (a^2) 7)) (invariant_mul_standard_mem (a^2) 8)) (invariant_mul_standard_mem (c) 10)) (invariant_mul_standard_mem (c) 13)) (invariant_mul_standard_mem (b) 14)) (invariant_mul_standard_mem (b) 16)) (invariant_mul_standard_mem (b) 17)) (invariant_mul_standard_mem (a) 22))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_0 : b * standardMonomial 0 =
    invariantEval (1) * standardMonomial 2 := by
  have h : b * (1) = (1) * (b) := by
    ring
  change b * (1) = invariantEval (1) * (b)
  simpa only [map_one] using h

private theorem mul_standard_1_0_mem : b * standardMonomial 0 ∈ standardSpan := by
  rw [mul_standard_1_0]
  exact (invariant_mul_standard_mem (1) 2)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_1 : b * standardMonomial 1 =
    invariantEval (1) * standardMonomial 5 := by
  have h : b * (a) = (1) * (a*b) := by
    ring
  change b * (a) = invariantEval (1) * (a*b)
  simpa only [map_one] using h

private theorem mul_standard_1_1_mem : b * standardMonomial 1 ∈ standardSpan := by
  rw [mul_standard_1_1]
  exact (invariant_mul_standard_mem (1) 5)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_2 : b * standardMonomial 2 =
    invariantEval (1) * standardMonomial 7 := by
  have h : b * (b) = (1) * (b^2) := by
    ring
  change b * (b) = invariantEval (1) * (b^2)
  simpa only [map_one] using h

private theorem mul_standard_1_2_mem : b * standardMonomial 2 ∈ standardSpan := by
  rw [mul_standard_1_2]
  exact (invariant_mul_standard_mem (1) 7)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_3 : b * standardMonomial 3 =
    invariantEval (1) * standardMonomial 9 := by
  have h : b * (a^2) = (1) * (a^2*b) := by
    ring
  change b * (a^2) = invariantEval (1) * (a^2*b)
  simpa only [map_one] using h

private theorem mul_standard_1_3_mem : b * standardMonomial 3 ∈ standardSpan := by
  rw [mul_standard_1_3]
  exact (invariant_mul_standard_mem (1) 9)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_4 : b * standardMonomial 4 =
    invariantEval (1) * standardMonomial 10 := by
  have h : b * (c) = (1) * (b*c) := by
    ring
  change b * (c) = invariantEval (1) * (b*c)
  simpa only [map_one] using h

private theorem mul_standard_1_4_mem : b * standardMonomial 4 ∈ standardSpan := by
  rw [mul_standard_1_4]
  exact (invariant_mul_standard_mem (1) 10)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_5 : b * standardMonomial 5 =
    invariantEval (1) * standardMonomial 11 := by
  have h : b * (a*b) = (1) * (a*b^2) := by
    ring
  change b * (a*b) = invariantEval (1) * (a*b^2)
  simpa only [map_one] using h

private theorem mul_standard_1_5_mem : b * standardMonomial 5 ∈ standardSpan := by
  rw [mul_standard_1_5]
  exact (invariant_mul_standard_mem (1) 11)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_6 : b * standardMonomial 6 =
    invariantEval (1) * standardMonomial 13 := by
  have h : b * (a^3) = (1) * (a^3*b) := by
    ring
  change b * (a^3) = invariantEval (1) * (a^3*b)
  simpa only [map_one] using h

private theorem mul_standard_1_6_mem : b * standardMonomial 6 ∈ standardSpan := by
  rw [mul_standard_1_6]
  exact (invariant_mul_standard_mem (1) 13)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_7 : b * standardMonomial 7 =
    invariantEval (1) * standardMonomial 15 := by
  have h : b * (b^2) = (1) * (b^3) := by
    ring
  change b * (b^2) = invariantEval (1) * (b^3)
  simpa only [map_one] using h

private theorem mul_standard_1_7_mem : b * standardMonomial 7 ∈ standardSpan := by
  rw [mul_standard_1_7]
  exact (invariant_mul_standard_mem (1) 15)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_8 : b * standardMonomial 8 =
    invariantEval (1) * standardMonomial 16 := by
  have h : b * (a*c) = (1) * (a*b*c) := by
    ring
  change b * (a*c) = invariantEval (1) * (a*b*c)
  simpa only [map_one] using h

private theorem mul_standard_1_8_mem : b * standardMonomial 8 ∈ standardSpan := by
  rw [mul_standard_1_8]
  exact (invariant_mul_standard_mem (1) 16)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_9 : b * standardMonomial 9 =
    invariantEval (1) * standardMonomial 17 := by
  have h : b * (a^2*b) = (1) * (a^2*b^2) := by
    ring
  change b * (a^2*b) = invariantEval (1) * (a^2*b^2)
  simpa only [map_one] using h

private theorem mul_standard_1_9_mem : b * standardMonomial 9 ∈ standardSpan := by
  rw [mul_standard_1_9]
  exact (invariant_mul_standard_mem (1) 17)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_10 : b * standardMonomial 10 =
    invariantEval (1) * standardMonomial 18 := by
  have h : b * (b*c) = (1) * (b^2*c) := by
    ring
  change b * (b*c) = invariantEval (1) * (b^2*c)
  simpa only [map_one] using h

private theorem mul_standard_1_10_mem : b * standardMonomial 10 ∈ standardSpan := by
  rw [mul_standard_1_10]
  exact (invariant_mul_standard_mem (1) 18)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_11 : b * standardMonomial 11 =
    invariantEval (1) * standardMonomial 20 := by
  have h : b * (a*b^2) = (1) * (a*b^3) := by
    ring
  change b * (a*b^2) = invariantEval (1) * (a*b^3)
  simpa only [map_one] using h

private theorem mul_standard_1_11_mem : b * standardMonomial 11 ∈ standardSpan := by
  rw [mul_standard_1_11]
  exact (invariant_mul_standard_mem (1) 20)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_12 : b * standardMonomial 12 =
    invariantEval (c) * standardMonomial 0 + invariantEval (1) * standardMonomial 19 := by
  have h : b * (a^2*c) = (d7) * (1) + (1) * (a*c^2) := by
    unfold d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (a^2*c) = invariantEval (c) * (1) + invariantEval (1) * (a*c^2)
  simpa only [map_one, invariantEval_c] using h

private theorem mul_standard_1_12_mem : b * standardMonomial 12 ∈ standardSpan := by
  rw [mul_standard_1_12]
  exact (standardSpan.add_mem (invariant_mul_standard_mem (c) 0) (invariant_mul_standard_mem (1) 19))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_13 : b * standardMonomial 13 =
    invariantEval (c) * standardMonomial 0 + invariantEval (b) * standardMonomial 1 + invariantEval (a) * standardMonomial 4 + invariantEval (1) * standardMonomial 18 + invariantEval (1) * standardMonomial 19 := by
  have h : b * (a^3*b) = (d7) * (1) + (d6) * (a) + (d4) * (c) + (1) * (b^2*c) + (1) * (a*c^2) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (a^3*b) = invariantEval (c) * (1) + invariantEval (b) * (a) + invariantEval (a) * (c) + invariantEval (1) * (b^2*c) + invariantEval (1) * (a*c^2)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_13_mem : b * standardMonomial 13 ∈ standardSpan := by
  rw [mul_standard_1_13]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 0) (invariant_mul_standard_mem (b) 1)) (invariant_mul_standard_mem (a) 4)) (invariant_mul_standard_mem (1) 18)) (invariant_mul_standard_mem (1) 19))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_14 : b * standardMonomial 14 =
    invariantEval (1) * standardMonomial 21 := by
  have h : b * (c^2) = (1) * (b*c^2) := by
    ring
  change b * (c^2) = invariantEval (1) * (b*c^2)
  simpa only [map_one] using h

private theorem mul_standard_1_14_mem : b * standardMonomial 14 ∈ standardSpan := by
  rw [mul_standard_1_14]
  exact (invariant_mul_standard_mem (1) 21)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_15 : b * standardMonomial 15 =
    invariantEval (1) * standardMonomial 22 := by
  have h : b * (b^3) = (1) * (b^4) := by
    ring
  change b * (b^3) = invariantEval (1) * (b^4)
  simpa only [map_one] using h

private theorem mul_standard_1_15_mem : b * standardMonomial 15 ∈ standardSpan := by
  rw [mul_standard_1_15]
  exact (invariant_mul_standard_mem (1) 22)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_16 : b * standardMonomial 16 =
    invariantEval (1) * standardMonomial 23 := by
  have h : b * (a*b*c) = (1) * (a*b^2*c) := by
    ring
  change b * (a*b*c) = invariantEval (1) * (a*b^2*c)
  simpa only [map_one] using h

private theorem mul_standard_1_16_mem : b * standardMonomial 16 ∈ standardSpan := by
  rw [mul_standard_1_16]
  exact (invariant_mul_standard_mem (1) 23)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_17 : b * standardMonomial 17 =
    invariantEval (b) * standardMonomial 2 + invariantEval (b) * standardMonomial 3 + invariantEval (a) * standardMonomial 7 + invariantEval (a) * standardMonomial 8 + invariantEval (1) * standardMonomial 21 + invariantEval (1) * standardMonomial 22 + invariantEval (1) * standardMonomial 23 := by
  have h : b * (a^2*b^2) = (d6) * (b) + (d6) * (a^2) + (d4) * (b^2) + (d4) * (a*c) + (1) * (b*c^2) + (1) * (b^4) + (1) * (a*b^2*c) := by
    unfold d4 d6
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (a^2*b^2) = invariantEval (b) * (b) + invariantEval (b) * (a^2) + invariantEval (a) * (b^2) + invariantEval (a) * (a*c) + invariantEval (1) * (b*c^2) + invariantEval (1) * (b^4) + invariantEval (1) * (a*b^2*c)
  simpa only [map_one, invariantEval_a, invariantEval_b] using h

private theorem mul_standard_1_17_mem : b * standardMonomial 17 ∈ standardSpan := by
  rw [mul_standard_1_17]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b) 2) (invariant_mul_standard_mem (b) 3)) (invariant_mul_standard_mem (a) 7)) (invariant_mul_standard_mem (a) 8)) (invariant_mul_standard_mem (1) 21)) (invariant_mul_standard_mem (1) 22)) (invariant_mul_standard_mem (1) 23))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_18 : b * standardMonomial 18 =
    invariantEval (1) * standardMonomial 25 := by
  have h : b * (b^2*c) = (1) * (b^3*c) := by
    ring
  change b * (b^2*c) = invariantEval (1) * (b^3*c)
  simpa only [map_one] using h

private theorem mul_standard_1_18_mem : b * standardMonomial 18 ∈ standardSpan := by
  rw [mul_standard_1_18]
  exact (invariant_mul_standard_mem (1) 25)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_19 : b * standardMonomial 19 =
    invariantEval (c) * standardMonomial 2 + invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (a) * standardMonomial 10 + invariantEval (1) * standardMonomial 24 + invariantEval (1) * standardMonomial 25 := by
  have h : b * (a*c^2) = (d7) * (b) + (d7) * (a^2) + (d6) * (c) + (d4) * (b*c) + (1) * (c^3) + (1) * (b^3*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (a*c^2) = invariantEval (c) * (b) + invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (a) * (b*c) + invariantEval (1) * (c^3) + invariantEval (1) * (b^3*c)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_19_mem : b * standardMonomial 19 ∈ standardSpan := by
  rw [mul_standard_1_19]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 2) (invariant_mul_standard_mem (c) 3)) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (a) 10)) (invariant_mul_standard_mem (1) 24)) (invariant_mul_standard_mem (1) 25))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_20 : b * standardMonomial 20 =
    invariantEval (c) * standardMonomial 2 + invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (b) * standardMonomial 6 + invariantEval (a) * standardMonomial 11 + invariantEval (a) * standardMonomial 12 + invariantEval (1) * standardMonomial 24 := by
  have h : b * (a*b^3) = (d7) * (b) + (d7) * (a^2) + (d6) * (c) + (d6) * (a^3) + (d4) * (a*b^2) + (d4) * (a^2*c) + (1) * (c^3) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (a*b^3) = invariantEval (c) * (b) + invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (b) * (a^3) + invariantEval (a) * (a*b^2) + invariantEval (a) * (a^2*c) + invariantEval (1) * (c^3)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_20_mem : b * standardMonomial 20 ∈ standardSpan := by
  rw [mul_standard_1_20]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 2) (invariant_mul_standard_mem (c) 3)) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (b) 6)) (invariant_mul_standard_mem (a) 11)) (invariant_mul_standard_mem (a) 12)) (invariant_mul_standard_mem (1) 24))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_21 : b * standardMonomial 21 =
    invariantEval (c) * standardMonomial 5 + invariantEval (b) * standardMonomial 8 + invariantEval (a) * standardMonomial 14 := by
  have h : b * (b*c^2) = (d7) * (a*b) + (d6) * (a*c) + (d4) * (c^2) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (b*c^2) = invariantEval (c) * (a*b) + invariantEval (b) * (a*c) + invariantEval (a) * (c^2)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_21_mem : b * standardMonomial 21 ∈ standardSpan := by
  rw [mul_standard_1_21]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 5) (invariant_mul_standard_mem (b) 8)) (invariant_mul_standard_mem (a) 14))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_22 : b * standardMonomial 22 =
    invariantEval (1) * standardMonomial 26 := by
  have h : b * (b^4) = (1) * (b^5) := by
    ring
  change b * (b^4) = invariantEval (1) * (b^5)
  simpa only [map_one] using h

private theorem mul_standard_1_22_mem : b * standardMonomial 22 ∈ standardSpan := by
  rw [mul_standard_1_22]
  exact (invariant_mul_standard_mem (1) 26)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_23 : b * standardMonomial 23 =
    invariantEval (c) * standardMonomial 4 + invariantEval (c) * standardMonomial 5 + invariantEval (c) * standardMonomial 6 + invariantEval (b) * standardMonomial 8 + invariantEval (a) * standardMonomial 16 := by
  have h : b * (a*b^2*c) = (d7) * (c) + (d7) * (a*b) + (d7) * (a^3) + (d6) * (a*c) + (d4) * (a*b*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (a*b^2*c) = invariantEval (c) * (c) + invariantEval (c) * (a*b) + invariantEval (c) * (a^3) + invariantEval (b) * (a*c) + invariantEval (a) * (a*b*c)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_23_mem : b * standardMonomial 23 ∈ standardSpan := by
  rw [mul_standard_1_23]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 4) (invariant_mul_standard_mem (c) 5)) (invariant_mul_standard_mem (c) 6)) (invariant_mul_standard_mem (b) 8)) (invariant_mul_standard_mem (a) 16))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_24 : b * standardMonomial 24 =
    invariantEval (1) * standardMonomial 27 := by
  have h : b * (c^3) = (1) * (b*c^3) := by
    ring
  change b * (c^3) = invariantEval (1) * (b*c^3)
  simpa only [map_one] using h

private theorem mul_standard_1_24_mem : b * standardMonomial 24 ∈ standardSpan := by
  rw [mul_standard_1_24]
  exact (invariant_mul_standard_mem (1) 27)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_25 : b * standardMonomial 25 =
    invariantEval (c) * standardMonomial 7 + invariantEval (b) * standardMonomial 10 + invariantEval (b) * standardMonomial 12 + invariantEval (a) * standardMonomial 18 + invariantEval (a) * standardMonomial 19 + invariantEval (1) * standardMonomial 27 := by
  have h : b * (b^3*c) = (d7) * (b^2) + (d6) * (b*c) + (d6) * (a^2*c) + (d4) * (b^2*c) + (d4) * (a*c^2) + (1) * (b*c^3) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (b^3*c) = invariantEval (c) * (b^2) + invariantEval (b) * (b*c) + invariantEval (b) * (a^2*c) + invariantEval (a) * (b^2*c) + invariantEval (a) * (a*c^2) + invariantEval (1) * (b*c^3)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_25_mem : b * standardMonomial 25 ∈ standardSpan := by
  rw [mul_standard_1_25]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 7) (invariant_mul_standard_mem (b) 10)) (invariant_mul_standard_mem (b) 12)) (invariant_mul_standard_mem (a) 18)) (invariant_mul_standard_mem (a) 19)) (invariant_mul_standard_mem (1) 27))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_26 : b * standardMonomial 26 =
    invariantEval (b^2) * standardMonomial 0 + invariantEval (a*c) * standardMonomial 1 + invariantEval (a*b) * standardMonomial 3 + invariantEval (a^2) * standardMonomial 7 + invariantEval (a^2) * standardMonomial 8 + invariantEval (c) * standardMonomial 11 + invariantEval (c) * standardMonomial 13 + invariantEval (b) * standardMonomial 14 + invariantEval (b) * standardMonomial 16 + invariantEval (a) * standardMonomial 23 := by
  have h : b * (b^5) = (d6^2) * (1) + (d4*d7) * (a) + (d4*d6) * (a^2) + (d4^2) * (b^2) + (d4^2) * (a*c) + (d7) * (a*b^2) + (d7) * (a^3*b) + (d6) * (c^2) + (d6) * (a*b*c) + (d4) * (a*b^2*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (b^5) = invariantEval (b^2) * (1) + invariantEval (a*c) * (a) + invariantEval (a*b) * (a^2) + invariantEval (a^2) * (b^2) + invariantEval (a^2) * (a*c) + invariantEval (c) * (a*b^2) + invariantEval (c) * (a^3*b) + invariantEval (b) * (c^2) + invariantEval (b) * (a*b*c) + invariantEval (a) * (a*b^2*c)
  simpa only [map_mul, map_pow, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_26_mem : b * standardMonomial 26 ∈ standardSpan := by
  rw [mul_standard_1_26]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b^2) 0) (invariant_mul_standard_mem (a*c) 1)) (invariant_mul_standard_mem (a*b) 3)) (invariant_mul_standard_mem (a^2) 7)) (invariant_mul_standard_mem (a^2) 8)) (invariant_mul_standard_mem (c) 11)) (invariant_mul_standard_mem (c) 13)) (invariant_mul_standard_mem (b) 14)) (invariant_mul_standard_mem (b) 16)) (invariant_mul_standard_mem (a) 23))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_1_27 : b * standardMonomial 27 =
    invariantEval (c) * standardMonomial 16 + invariantEval (b) * standardMonomial 19 + invariantEval (a) * standardMonomial 24 := by
  have h : b * (b*c^3) = (d7) * (a*b*c) + (d6) * (a*c^2) + (d4) * (c^3) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change b * (b*c^3) = invariantEval (c) * (a*b*c) + invariantEval (b) * (a*c^2) + invariantEval (a) * (c^3)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_1_27_mem : b * standardMonomial 27 ∈ standardSpan := by
  rw [mul_standard_1_27]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 16) (invariant_mul_standard_mem (b) 19)) (invariant_mul_standard_mem (a) 24))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_0 : c * standardMonomial 0 =
    invariantEval (1) * standardMonomial 4 := by
  have h : c * (1) = (1) * (c) := by
    ring
  change c * (1) = invariantEval (1) * (c)
  simpa only [map_one] using h

private theorem mul_standard_2_0_mem : c * standardMonomial 0 ∈ standardSpan := by
  rw [mul_standard_2_0]
  exact (invariant_mul_standard_mem (1) 4)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_1 : c * standardMonomial 1 =
    invariantEval (1) * standardMonomial 8 := by
  have h : c * (a) = (1) * (a*c) := by
    ring
  change c * (a) = invariantEval (1) * (a*c)
  simpa only [map_one] using h

private theorem mul_standard_2_1_mem : c * standardMonomial 1 ∈ standardSpan := by
  rw [mul_standard_2_1]
  exact (invariant_mul_standard_mem (1) 8)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_2 : c * standardMonomial 2 =
    invariantEval (1) * standardMonomial 10 := by
  have h : c * (b) = (1) * (b*c) := by
    ring
  change c * (b) = invariantEval (1) * (b*c)
  simpa only [map_one] using h

private theorem mul_standard_2_2_mem : c * standardMonomial 2 ∈ standardSpan := by
  rw [mul_standard_2_2]
  exact (invariant_mul_standard_mem (1) 10)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_3 : c * standardMonomial 3 =
    invariantEval (1) * standardMonomial 12 := by
  have h : c * (a^2) = (1) * (a^2*c) := by
    ring
  change c * (a^2) = invariantEval (1) * (a^2*c)
  simpa only [map_one] using h

private theorem mul_standard_2_3_mem : c * standardMonomial 3 ∈ standardSpan := by
  rw [mul_standard_2_3]
  exact (invariant_mul_standard_mem (1) 12)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_4 : c * standardMonomial 4 =
    invariantEval (1) * standardMonomial 14 := by
  have h : c * (c) = (1) * (c^2) := by
    ring
  change c * (c) = invariantEval (1) * (c^2)
  simpa only [map_one] using h

private theorem mul_standard_2_4_mem : c * standardMonomial 4 ∈ standardSpan := by
  rw [mul_standard_2_4]
  exact (invariant_mul_standard_mem (1) 14)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_5 : c * standardMonomial 5 =
    invariantEval (1) * standardMonomial 16 := by
  have h : c * (a*b) = (1) * (a*b*c) := by
    ring
  change c * (a*b) = invariantEval (1) * (a*b*c)
  simpa only [map_one] using h

private theorem mul_standard_2_5_mem : c * standardMonomial 5 ∈ standardSpan := by
  rw [mul_standard_2_5]
  exact (invariant_mul_standard_mem (1) 16)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_6 : c * standardMonomial 6 =
    invariantEval (b) * standardMonomial 0 + invariantEval (1) * standardMonomial 14 + invariantEval (1) * standardMonomial 16 + invariantEval (1) * standardMonomial 17 := by
  have h : c * (a^3) = (d6) * (1) + (1) * (c^2) + (1) * (a*b*c) + (1) * (a^2*b^2) := by
    unfold d6
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a^3) = invariantEval (b) * (1) + invariantEval (1) * (c^2) + invariantEval (1) * (a*b*c) + invariantEval (1) * (a^2*b^2)
  simpa only [map_one, invariantEval_b] using h

private theorem mul_standard_2_6_mem : c * standardMonomial 6 ∈ standardSpan := by
  rw [mul_standard_2_6]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b) 0) (invariant_mul_standard_mem (1) 14)) (invariant_mul_standard_mem (1) 16)) (invariant_mul_standard_mem (1) 17))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_7 : c * standardMonomial 7 =
    invariantEval (1) * standardMonomial 18 := by
  have h : c * (b^2) = (1) * (b^2*c) := by
    ring
  change c * (b^2) = invariantEval (1) * (b^2*c)
  simpa only [map_one] using h

private theorem mul_standard_2_7_mem : c * standardMonomial 7 ∈ standardSpan := by
  rw [mul_standard_2_7]
  exact (invariant_mul_standard_mem (1) 18)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_8 : c * standardMonomial 8 =
    invariantEval (1) * standardMonomial 19 := by
  have h : c * (a*c) = (1) * (a*c^2) := by
    ring
  change c * (a*c) = invariantEval (1) * (a*c^2)
  simpa only [map_one] using h

private theorem mul_standard_2_8_mem : c * standardMonomial 8 ∈ standardSpan := by
  rw [mul_standard_2_8]
  exact (invariant_mul_standard_mem (1) 19)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_9 : c * standardMonomial 9 =
    invariantEval (c) * standardMonomial 0 + invariantEval (1) * standardMonomial 19 := by
  have h : c * (a^2*b) = (d7) * (1) + (1) * (a*c^2) := by
    unfold d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a^2*b) = invariantEval (c) * (1) + invariantEval (1) * (a*c^2)
  simpa only [map_one, invariantEval_c] using h

private theorem mul_standard_2_9_mem : c * standardMonomial 9 ∈ standardSpan := by
  rw [mul_standard_2_9]
  exact (standardSpan.add_mem (invariant_mul_standard_mem (c) 0) (invariant_mul_standard_mem (1) 19))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_10 : c * standardMonomial 10 =
    invariantEval (1) * standardMonomial 21 := by
  have h : c * (b*c) = (1) * (b*c^2) := by
    ring
  change c * (b*c) = invariantEval (1) * (b*c^2)
  simpa only [map_one] using h

private theorem mul_standard_2_10_mem : c * standardMonomial 10 ∈ standardSpan := by
  rw [mul_standard_2_10]
  exact (invariant_mul_standard_mem (1) 21)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_11 : c * standardMonomial 11 =
    invariantEval (1) * standardMonomial 23 := by
  have h : c * (a*b^2) = (1) * (a*b^2*c) := by
    ring
  change c * (a*b^2) = invariantEval (1) * (a*b^2*c)
  simpa only [map_one] using h

private theorem mul_standard_2_11_mem : c * standardMonomial 11 ∈ standardSpan := by
  rw [mul_standard_2_11]
  exact (invariant_mul_standard_mem (1) 23)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_12 : c * standardMonomial 12 =
    invariantEval (c) * standardMonomial 1 + invariantEval (b) * standardMonomial 3 + invariantEval (a) * standardMonomial 7 + invariantEval (a) * standardMonomial 8 + invariantEval (1) * standardMonomial 22 := by
  have h : c * (a^2*c) = (d7) * (a) + (d6) * (a^2) + (d4) * (b^2) + (d4) * (a*c) + (1) * (b^4) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a^2*c) = invariantEval (c) * (a) + invariantEval (b) * (a^2) + invariantEval (a) * (b^2) + invariantEval (a) * (a*c) + invariantEval (1) * (b^4)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_12_mem : c * standardMonomial 12 ∈ standardSpan := by
  rw [mul_standard_2_12]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 1) (invariant_mul_standard_mem (b) 3)) (invariant_mul_standard_mem (a) 7)) (invariant_mul_standard_mem (a) 8)) (invariant_mul_standard_mem (1) 22))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_13 : c * standardMonomial 13 =
    invariantEval (b) * standardMonomial 3 + invariantEval (a) * standardMonomial 7 + invariantEval (a) * standardMonomial 8 + invariantEval (1) * standardMonomial 22 := by
  have h : c * (a^3*b) = (d6) * (a^2) + (d4) * (b^2) + (d4) * (a*c) + (1) * (b^4) := by
    unfold d4 d6
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a^3*b) = invariantEval (b) * (a^2) + invariantEval (a) * (b^2) + invariantEval (a) * (a*c) + invariantEval (1) * (b^4)
  simpa only [map_one, invariantEval_a, invariantEval_b] using h

private theorem mul_standard_2_13_mem : c * standardMonomial 13 ∈ standardSpan := by
  rw [mul_standard_2_13]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b) 3) (invariant_mul_standard_mem (a) 7)) (invariant_mul_standard_mem (a) 8)) (invariant_mul_standard_mem (1) 22))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_14 : c * standardMonomial 14 =
    invariantEval (1) * standardMonomial 24 := by
  have h : c * (c^2) = (1) * (c^3) := by
    ring
  change c * (c^2) = invariantEval (1) * (c^3)
  simpa only [map_one] using h

private theorem mul_standard_2_14_mem : c * standardMonomial 14 ∈ standardSpan := by
  rw [mul_standard_2_14]
  exact (invariant_mul_standard_mem (1) 24)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_15 : c * standardMonomial 15 =
    invariantEval (1) * standardMonomial 25 := by
  have h : c * (b^3) = (1) * (b^3*c) := by
    ring
  change c * (b^3) = invariantEval (1) * (b^3*c)
  simpa only [map_one] using h

private theorem mul_standard_2_15_mem : c * standardMonomial 15 ∈ standardSpan := by
  rw [mul_standard_2_15]
  exact (invariant_mul_standard_mem (1) 25)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_16 : c * standardMonomial 16 =
    invariantEval (c) * standardMonomial 2 + invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (a) * standardMonomial 10 + invariantEval (1) * standardMonomial 24 + invariantEval (1) * standardMonomial 25 := by
  have h : c * (a*b*c) = (d7) * (b) + (d7) * (a^2) + (d6) * (c) + (d4) * (b*c) + (1) * (c^3) + (1) * (b^3*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a*b*c) = invariantEval (c) * (b) + invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (a) * (b*c) + invariantEval (1) * (c^3) + invariantEval (1) * (b^3*c)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_16_mem : c * standardMonomial 16 ∈ standardSpan := by
  rw [mul_standard_2_16]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 2) (invariant_mul_standard_mem (c) 3)) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (a) 10)) (invariant_mul_standard_mem (1) 24)) (invariant_mul_standard_mem (1) 25))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_17 : c * standardMonomial 17 =
    invariantEval (c) * standardMonomial 3 + invariantEval (b) * standardMonomial 4 + invariantEval (a) * standardMonomial 10 + invariantEval (1) * standardMonomial 24 + invariantEval (1) * standardMonomial 25 := by
  have h : c * (a^2*b^2) = (d7) * (a^2) + (d6) * (c) + (d4) * (b*c) + (1) * (c^3) + (1) * (b^3*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a^2*b^2) = invariantEval (c) * (a^2) + invariantEval (b) * (c) + invariantEval (a) * (b*c) + invariantEval (1) * (c^3) + invariantEval (1) * (b^3*c)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_17_mem : c * standardMonomial 17 ∈ standardSpan := by
  rw [mul_standard_2_17]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 3) (invariant_mul_standard_mem (b) 4)) (invariant_mul_standard_mem (a) 10)) (invariant_mul_standard_mem (1) 24)) (invariant_mul_standard_mem (1) 25))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_18 : c * standardMonomial 18 =
    invariantEval (c) * standardMonomial 5 + invariantEval (b) * standardMonomial 8 + invariantEval (a) * standardMonomial 14 := by
  have h : c * (b^2*c) = (d7) * (a*b) + (d6) * (a*c) + (d4) * (c^2) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (b^2*c) = invariantEval (c) * (a*b) + invariantEval (b) * (a*c) + invariantEval (a) * (c^2)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_18_mem : c * standardMonomial 18 ∈ standardSpan := by
  rw [mul_standard_2_18]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 5) (invariant_mul_standard_mem (b) 8)) (invariant_mul_standard_mem (a) 14))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_19 : c * standardMonomial 19 =
    invariantEval (c) * standardMonomial 4 + invariantEval (c) * standardMonomial 5 + invariantEval (b) * standardMonomial 9 + invariantEval (a) * standardMonomial 15 + invariantEval (a) * standardMonomial 16 + invariantEval (1) * standardMonomial 26 := by
  have h : c * (a*c^2) = (d7) * (c) + (d7) * (a*b) + (d6) * (a^2*b) + (d4) * (b^3) + (d4) * (a*b*c) + (1) * (b^5) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a*c^2) = invariantEval (c) * (c) + invariantEval (c) * (a*b) + invariantEval (b) * (a^2*b) + invariantEval (a) * (b^3) + invariantEval (a) * (a*b*c) + invariantEval (1) * (b^5)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_19_mem : c * standardMonomial 19 ∈ standardSpan := by
  rw [mul_standard_2_19]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 4) (invariant_mul_standard_mem (c) 5)) (invariant_mul_standard_mem (b) 9)) (invariant_mul_standard_mem (a) 15)) (invariant_mul_standard_mem (a) 16)) (invariant_mul_standard_mem (1) 26))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_20 : c * standardMonomial 20 =
    invariantEval (c) * standardMonomial 4 + invariantEval (c) * standardMonomial 5 + invariantEval (c) * standardMonomial 6 + invariantEval (b) * standardMonomial 8 + invariantEval (a) * standardMonomial 16 := by
  have h : c * (a*b^3) = (d7) * (c) + (d7) * (a*b) + (d7) * (a^3) + (d6) * (a*c) + (d4) * (a*b*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a*b^3) = invariantEval (c) * (c) + invariantEval (c) * (a*b) + invariantEval (c) * (a^3) + invariantEval (b) * (a*c) + invariantEval (a) * (a*b*c)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_20_mem : c * standardMonomial 20 ∈ standardSpan := by
  rw [mul_standard_2_20]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 4) (invariant_mul_standard_mem (c) 5)) (invariant_mul_standard_mem (c) 6)) (invariant_mul_standard_mem (b) 8)) (invariant_mul_standard_mem (a) 16))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_21 : c * standardMonomial 21 =
    invariantEval (1) * standardMonomial 27 := by
  have h : c * (b*c^2) = (1) * (b*c^3) := by
    ring
  change c * (b*c^2) = invariantEval (1) * (b*c^3)
  simpa only [map_one] using h

private theorem mul_standard_2_21_mem : c * standardMonomial 21 ∈ standardSpan := by
  rw [mul_standard_2_21]
  exact (invariant_mul_standard_mem (1) 27)

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_22 : c * standardMonomial 22 =
    invariantEval (c) * standardMonomial 7 + invariantEval (b) * standardMonomial 10 + invariantEval (b) * standardMonomial 12 + invariantEval (a) * standardMonomial 18 + invariantEval (a) * standardMonomial 19 + invariantEval (1) * standardMonomial 27 := by
  have h : c * (b^4) = (d7) * (b^2) + (d6) * (b*c) + (d6) * (a^2*c) + (d4) * (b^2*c) + (d4) * (a*c^2) + (1) * (b*c^3) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (b^4) = invariantEval (c) * (b^2) + invariantEval (b) * (b*c) + invariantEval (b) * (a^2*c) + invariantEval (a) * (b^2*c) + invariantEval (a) * (a*c^2) + invariantEval (1) * (b*c^3)
  simpa only [map_one, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_22_mem : c * standardMonomial 22 ∈ standardSpan := by
  rw [mul_standard_2_22]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 7) (invariant_mul_standard_mem (b) 10)) (invariant_mul_standard_mem (b) 12)) (invariant_mul_standard_mem (a) 18)) (invariant_mul_standard_mem (a) 19)) (invariant_mul_standard_mem (1) 27))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_23 : c * standardMonomial 23 =
    invariantEval (c) * standardMonomial 9 + invariantEval (b) * standardMonomial 12 + invariantEval (a) * standardMonomial 19 := by
  have h : c * (a*b^2*c) = (d7) * (a^2*b) + (d6) * (a^2*c) + (d4) * (a*c^2) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (a*b^2*c) = invariantEval (c) * (a^2*b) + invariantEval (b) * (a^2*c) + invariantEval (a) * (a*c^2)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_23_mem : c * standardMonomial 23 ∈ standardSpan := by
  rw [mul_standard_2_23]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 9) (invariant_mul_standard_mem (b) 12)) (invariant_mul_standard_mem (a) 19))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_24 : c * standardMonomial 24 =
    invariantEval (b^2) * standardMonomial 0 + invariantEval (a*c) * standardMonomial 1 + invariantEval (a*b) * standardMonomial 3 + invariantEval (a^2) * standardMonomial 7 + invariantEval (a^2) * standardMonomial 8 + invariantEval (c) * standardMonomial 11 + invariantEval (c) * standardMonomial 12 + invariantEval (c) * standardMonomial 13 + invariantEval (b) * standardMonomial 17 + invariantEval (a) * standardMonomial 22 := by
  have h : c * (c^3) = (d6^2) * (1) + (d4*d7) * (a) + (d4*d6) * (a^2) + (d4^2) * (b^2) + (d4^2) * (a*c) + (d7) * (a*b^2) + (d7) * (a^2*c) + (d7) * (a^3*b) + (d6) * (a^2*b^2) + (d4) * (b^4) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (c^3) = invariantEval (b^2) * (1) + invariantEval (a*c) * (a) + invariantEval (a*b) * (a^2) + invariantEval (a^2) * (b^2) + invariantEval (a^2) * (a*c) + invariantEval (c) * (a*b^2) + invariantEval (c) * (a^2*c) + invariantEval (c) * (a^3*b) + invariantEval (b) * (a^2*b^2) + invariantEval (a) * (b^4)
  simpa only [map_mul, map_pow, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_24_mem : c * standardMonomial 24 ∈ standardSpan := by
  rw [mul_standard_2_24]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b^2) 0) (invariant_mul_standard_mem (a*c) 1)) (invariant_mul_standard_mem (a*b) 3)) (invariant_mul_standard_mem (a^2) 7)) (invariant_mul_standard_mem (a^2) 8)) (invariant_mul_standard_mem (c) 11)) (invariant_mul_standard_mem (c) 12)) (invariant_mul_standard_mem (c) 13)) (invariant_mul_standard_mem (b) 17)) (invariant_mul_standard_mem (a) 22))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_25 : c * standardMonomial 25 =
    invariantEval (c) * standardMonomial 11 + invariantEval (b) * standardMonomial 16 + invariantEval (a) * standardMonomial 21 := by
  have h : c * (b^3*c) = (d7) * (a*b^2) + (d6) * (a*b*c) + (d4) * (b*c^2) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (b^3*c) = invariantEval (c) * (a*b^2) + invariantEval (b) * (a*b*c) + invariantEval (a) * (b*c^2)
  simpa only [invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_25_mem : c * standardMonomial 25 ∈ standardSpan := by
  rw [mul_standard_2_25]
  exact (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (c) 11) (invariant_mul_standard_mem (b) 16)) (invariant_mul_standard_mem (a) 21))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_26 : c * standardMonomial 26 =
    invariantEval (b*c) * standardMonomial 0 + invariantEval (a*c) * standardMonomial 2 + invariantEval (a*c) * standardMonomial 3 + invariantEval (a*b) * standardMonomial 4 + invariantEval (a^2) * standardMonomial 10 + invariantEval (c) * standardMonomial 15 + invariantEval (c) * standardMonomial 16 + invariantEval (b) * standardMonomial 18 := by
  have h : c * (b^5) = (d6*d7) * (1) + (d4*d7) * (b) + (d4*d7) * (a^2) + (d4*d6) * (c) + (d4^2) * (b*c) + (d7) * (b^3) + (d7) * (a*b*c) + (d6) * (b^2*c) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (b^5) = invariantEval (b*c) * (1) + invariantEval (a*c) * (b) + invariantEval (a*c) * (a^2) + invariantEval (a*b) * (c) + invariantEval (a^2) * (b*c) + invariantEval (c) * (b^3) + invariantEval (c) * (a*b*c) + invariantEval (b) * (b^2*c)
  simpa only [map_mul, map_pow, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_26_mem : c * standardMonomial 26 ∈ standardSpan := by
  rw [mul_standard_2_26]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b*c) 0) (invariant_mul_standard_mem (a*c) 2)) (invariant_mul_standard_mem (a*c) 3)) (invariant_mul_standard_mem (a*b) 4)) (invariant_mul_standard_mem (a^2) 10)) (invariant_mul_standard_mem (c) 15)) (invariant_mul_standard_mem (c) 16)) (invariant_mul_standard_mem (b) 18))

/-- Exact invariant-coefficient multiplication certificate. -/
theorem mul_standard_2_27 : c * standardMonomial 27 =
    invariantEval (b*c) * standardMonomial 1 + invariantEval (b^2) * standardMonomial 3 + invariantEval (a*c) * standardMonomial 4 + invariantEval (a*c) * standardMonomial 5 + invariantEval (a*b) * standardMonomial 7 + invariantEval (a*b) * standardMonomial 8 + invariantEval (a*b) * standardMonomial 9 + invariantEval (a^2) * standardMonomial 15 + invariantEval (a^2) * standardMonomial 16 + invariantEval (c) * standardMonomial 18 + invariantEval (c) * standardMonomial 20 + invariantEval (b) * standardMonomial 21 + invariantEval (b) * standardMonomial 22 + invariantEval (b) * standardMonomial 23 + invariantEval (a) * standardMonomial 26 := by
  have h : c * (b*c^3) = (d6*d7) * (a) + (d6^2) * (a^2) + (d4*d7) * (c) + (d4*d7) * (a*b) + (d4*d6) * (b^2) + (d4*d6) * (a*c) + (d4*d6) * (a^2*b) + (d4^2) * (b^3) + (d4^2) * (a*b*c) + (d7) * (b^2*c) + (d7) * (a*b^3) + (d6) * (b*c^2) + (d6) * (b^4) + (d6) * (a*b^2*c) + (d4) * (b^5) := by
    unfold d4 d6 d7
    ring_nf
    simp only [ofNat_mod]
    norm_num
  change c * (b*c^3) = invariantEval (b*c) * (a) + invariantEval (b^2) * (a^2) + invariantEval (a*c) * (c) + invariantEval (a*c) * (a*b) + invariantEval (a*b) * (b^2) + invariantEval (a*b) * (a*c) + invariantEval (a*b) * (a^2*b) + invariantEval (a^2) * (b^3) + invariantEval (a^2) * (a*b*c) + invariantEval (c) * (b^2*c) + invariantEval (c) * (a*b^3) + invariantEval (b) * (b*c^2) + invariantEval (b) * (b^4) + invariantEval (b) * (a*b^2*c) + invariantEval (a) * (b^5)
  simpa only [map_mul, map_pow, invariantEval_a, invariantEval_b, invariantEval_c] using h

private theorem mul_standard_2_27_mem : c * standardMonomial 27 ∈ standardSpan := by
  rw [mul_standard_2_27]
  exact (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (standardSpan.add_mem (invariant_mul_standard_mem (b*c) 1) (invariant_mul_standard_mem (b^2) 3)) (invariant_mul_standard_mem (a*c) 4)) (invariant_mul_standard_mem (a*c) 5)) (invariant_mul_standard_mem (a*b) 7)) (invariant_mul_standard_mem (a*b) 8)) (invariant_mul_standard_mem (a*b) 9)) (invariant_mul_standard_mem (a^2) 15)) (invariant_mul_standard_mem (a^2) 16)) (invariant_mul_standard_mem (c) 18)) (invariant_mul_standard_mem (c) 20)) (invariant_mul_standard_mem (b) 21)) (invariant_mul_standard_mem (b) 22)) (invariant_mul_standard_mem (b) 23)) (invariant_mul_standard_mem (a) 26))

theorem a_mul_standard_mem (i : Fin 28) : a * standardMonomial i ∈ standardSpan := by
  fin_cases i
  · exact mul_standard_0_0_mem
  · exact mul_standard_0_1_mem
  · exact mul_standard_0_2_mem
  · exact mul_standard_0_3_mem
  · exact mul_standard_0_4_mem
  · exact mul_standard_0_5_mem
  · exact mul_standard_0_6_mem
  · exact mul_standard_0_7_mem
  · exact mul_standard_0_8_mem
  · exact mul_standard_0_9_mem
  · exact mul_standard_0_10_mem
  · exact mul_standard_0_11_mem
  · exact mul_standard_0_12_mem
  · exact mul_standard_0_13_mem
  · exact mul_standard_0_14_mem
  · exact mul_standard_0_15_mem
  · exact mul_standard_0_16_mem
  · exact mul_standard_0_17_mem
  · exact mul_standard_0_18_mem
  · exact mul_standard_0_19_mem
  · exact mul_standard_0_20_mem
  · exact mul_standard_0_21_mem
  · exact mul_standard_0_22_mem
  · exact mul_standard_0_23_mem
  · exact mul_standard_0_24_mem
  · exact mul_standard_0_25_mem
  · exact mul_standard_0_26_mem
  · exact mul_standard_0_27_mem

theorem b_mul_standard_mem (i : Fin 28) : b * standardMonomial i ∈ standardSpan := by
  fin_cases i
  · exact mul_standard_1_0_mem
  · exact mul_standard_1_1_mem
  · exact mul_standard_1_2_mem
  · exact mul_standard_1_3_mem
  · exact mul_standard_1_4_mem
  · exact mul_standard_1_5_mem
  · exact mul_standard_1_6_mem
  · exact mul_standard_1_7_mem
  · exact mul_standard_1_8_mem
  · exact mul_standard_1_9_mem
  · exact mul_standard_1_10_mem
  · exact mul_standard_1_11_mem
  · exact mul_standard_1_12_mem
  · exact mul_standard_1_13_mem
  · exact mul_standard_1_14_mem
  · exact mul_standard_1_15_mem
  · exact mul_standard_1_16_mem
  · exact mul_standard_1_17_mem
  · exact mul_standard_1_18_mem
  · exact mul_standard_1_19_mem
  · exact mul_standard_1_20_mem
  · exact mul_standard_1_21_mem
  · exact mul_standard_1_22_mem
  · exact mul_standard_1_23_mem
  · exact mul_standard_1_24_mem
  · exact mul_standard_1_25_mem
  · exact mul_standard_1_26_mem
  · exact mul_standard_1_27_mem

theorem c_mul_standard_mem (i : Fin 28) : c * standardMonomial i ∈ standardSpan := by
  fin_cases i
  · exact mul_standard_2_0_mem
  · exact mul_standard_2_1_mem
  · exact mul_standard_2_2_mem
  · exact mul_standard_2_3_mem
  · exact mul_standard_2_4_mem
  · exact mul_standard_2_5_mem
  · exact mul_standard_2_6_mem
  · exact mul_standard_2_7_mem
  · exact mul_standard_2_8_mem
  · exact mul_standard_2_9_mem
  · exact mul_standard_2_10_mem
  · exact mul_standard_2_11_mem
  · exact mul_standard_2_12_mem
  · exact mul_standard_2_13_mem
  · exact mul_standard_2_14_mem
  · exact mul_standard_2_15_mem
  · exact mul_standard_2_16_mem
  · exact mul_standard_2_17_mem
  · exact mul_standard_2_18_mem
  · exact mul_standard_2_19_mem
  · exact mul_standard_2_20_mem
  · exact mul_standard_2_21_mem
  · exact mul_standard_2_22_mem
  · exact mul_standard_2_23_mem
  · exact mul_standard_2_24_mem
  · exact mul_standard_2_25_mem
  · exact mul_standard_2_26_mem
  · exact mul_standard_2_27_mem

/-- Multiplication by each ambient coordinate preserves the invariant-module span. -/
theorem X_mul_mem_standardSpan (v : Fin 3) {p : Poly} (hp : p ∈ standardSpan) :
    X v * p ∈ standardSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i,rfl⟩ := hp
      fin_cases v
      · exact a_mul_standard_mem i
      · exact b_mul_standard_mem i
      · exact c_mul_standard_mem i
  | zero => simpa only [mul_zero] using standardSpan.zero_mem
  | add p q hp hq ihp ihq =>
      simpa only [mul_add] using standardSpan.add_mem ihp ihq
  | smul r p hp ih =>
      change X v * ((r : Poly) * p) ∈ standardSpan
      rw [mul_left_comm]
      exact standardSpan.smul_mem r ih

/-- The 28 displayed monomials span the entire polynomial ring over the invariant ring. -/
theorem mem_standardSpan (f : Poly) : f ∈ standardSpan := by
  induction f using MvPolynomial.induction_on with
  | C r =>
      simpa [standardMonomial, invariantEval] using invariant_mul_standard_mem (C r) 0
  | add p q hp hq => exact standardSpan.add_mem hp hq
  | mul_X p i hp =>
      simpa only [mul_comm] using X_mul_mem_standardSpan i hp

/-- Polynomial, rather than fraction-field, spanning by the 28 standard monomials. -/
theorem exists_standard_expansion (f : Poly) :
    ∃ coeff : Fin 28 → Poly,
      f = ∑ i, invariantEval (coeff i) * standardMonomial i := by
  classical
  obtain ⟨coeff,hcoeff⟩ :=
    (Submodule.mem_span_range_iff_exists_fun invariantRing).mp (mem_standardSpan f)
  have hpre (i : Fin 28) : ∃ p : Poly, invariantEval p = (coeff i : Poly) :=
    (coeff i).property
  choose r hr using hpre
  refine ⟨r, hcoeff.symm.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  change (coeff i : Poly) * standardMonomial i = invariantEval (r i) * standardMonomial i
  rw [hr]
end TernaryPoly.DicksonQuotient
