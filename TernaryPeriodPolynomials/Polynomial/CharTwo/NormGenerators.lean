module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
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
namespace TernaryPoly.CharTwoNorm

abbrev Poly := MvPolynomial (Fin 3) (ZMod 2)

def a : Poly := X 0 + X 1 + X 2
def b : Poly := X 0 * X 1 + X 0 * X 2 + X 1 * X 2
def c : Poly := X 0 * X 1 * X 2
def cplus : Poly := a * b + c

def d4 : Poly := a ^ 4 + b ^ 2 + a * c
def d6 : Poly := a ^ 2 * b ^ 2 + a ^ 3 * c + a * b * c + c ^ 2
def d7 : Poly := a * c * cplus

def sub₁ : Poly →ₐ[ZMod 2] Poly := bind₁ ![X 1, X 0 + X 1, X 2]
def sub₂ : Poly →ₐ[ZMod 2] Poly := bind₁ ![X 0 + X 1, X 0, X 2]
def norm (f : Poly) : Poly := f + sub₁ f + sub₂ f

def basis : Fin 8 → Poly :=
  ![1, a, a ^ 2 + b, a * b, a ^ 3 + c, a * cplus,
    a ^ 3 * (a ^ 2 + b), a ^ 6 + a ^ 3 * c + b ^ 3 + c ^ 2]

def generator (i : Fin 8) : Poly := a * cplus * basis i

def invariant : Fin 3 → Poly := ![d4, d6, d7]
def invariantEval : Poly →ₐ[ZMod 2] Poly := bind₁ invariant

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n

/-- The eight stated generators satisfy the literal characteristic-two norm equation. -/
theorem norm_generator (i : Fin 8) : norm (generator i) = 0 := by
  fin_cases i <;>
    simp [norm, generator, basis, sub₁, sub₂, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

/-- Dickson invariants are fixed under the first norm substitution. -/
theorem sub₁_invariant (i : Fin 3) : sub₁ (invariant i) = invariant i := by
  fin_cases i <;>
    simp [invariant, sub₁, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

/-- Dickson invariants are fixed under the second norm substitution. -/
theorem sub₂_invariant (i : Fin 3) : sub₂ (invariant i) = invariant i := by
  fin_cases i <;>
    simp [invariant, sub₂, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

/-- Every coordinate permutation fixes the elementary symmetric coordinates. -/
theorem rename_elementary (σ : Equiv.Perm (Fin 3)) :
    rename σ a = a ∧ rename σ b = b ∧ rename σ c = c := by
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  simp only [a, b, c, map_add, map_mul, rename_X]
  generalize h0 : σ 0 = i0 at *
  generalize h1 : σ 1 = i1 at *
  generalize h2 : σ 2 = i2 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all
  all_goals (repeat' constructor) <;> ring

/-- Each Dickson invariant is fixed by every coordinate permutation. -/
theorem rename_invariant (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    rename σ (invariant i) = invariant i := by
  obtain ⟨ha, hb, hc⟩ := rename_elementary σ
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, ha, hb, hc]

/-- Substitution in the invariant coordinates preserves every common fixed polynomial. -/
theorem map_invariantEval (t : Poly →ₐ[ZMod 2] Poly)
    (ht : ∀ i, t (invariant i) = invariant i) (F : Poly) :
    t (invariantEval F) = invariantEval F := by
  have h : t.comp invariantEval = invariantEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [invariantEval] using ht i
  exact DFunLike.congr_fun h F

theorem sub₁_invariantEval (F : Poly) : sub₁ (invariantEval F) = invariantEval F :=
  map_invariantEval sub₁ sub₁_invariant F

theorem sub₂_invariantEval (F : Poly) : sub₂ (invariantEval F) = invariantEval F :=
  map_invariantEval sub₂ sub₂_invariant F

theorem rename_invariantEval (σ : Equiv.Perm (Fin 3)) (F : Poly) :
    rename σ (invariantEval F) = invariantEval F :=
  map_invariantEval (rename σ) (rename_invariant σ) F

/-- A scalar fixed by the two substitutions factors out of the norm. -/
theorem norm_mul_of_fixed (s f : Poly) (h₁ : sub₁ s = s) (h₂ : sub₂ s = s) :
    norm (s * f) = s * norm f := by
  simp only [norm, map_mul, h₁, h₂, mul_add]

theorem norm_add (f g : Poly) : norm (f + g) = norm f + norm g := by
  simp only [norm, map_add]
  ring

theorem norm_zero : norm 0 = 0 := by simp [norm]

theorem norm_sum {ι : Type*} (s : Finset ι) (g : ι → Poly) :
    norm (∑ i ∈ s, g i) = ∑ i ∈ s, norm (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [norm_zero]
  | @insert i s hi ih => simp [Finset.sum_insert, hi, norm_add, ih]

/-- Each generator is symmetric under arbitrary coordinate permutations. -/
theorem rename_generator (σ : Equiv.Perm (Fin 3)) (i : Fin 8) :
    rename σ (generator i) = generator i := by
  obtain ⟨ha, hb, hc⟩ := rename_elementary σ
  fin_cases i <;> simp [generator, basis, cplus, ha, hb, hc]

/-- Every polynomial-in-Dickson-invariants multiple of a stated generator has zero norm. -/
theorem norm_invariantEval_mul_generator (F : Poly) (i : Fin 8) :
    norm (invariantEval F * generator i) = 0 := by
  rw [norm_mul_of_fixed _ _ (sub₁_invariantEval F) (sub₂_invariantEval F),
    norm_generator, mul_zero]

/-- The module generated by the eight polynomials is contained in the norm kernel.
This is an inclusion statement and makes no spanning or freeness assertion. -/
theorem norm_sum_invariantEval_mul_generator (F : Fin 8 → Poly) :
    norm (∑ i, invariantEval (F i) * generator i) = 0 := by
  rw [norm_sum]
  simp only [norm_invariantEval_mul_generator, Finset.sum_const_zero]

end TernaryPoly.CharTwoNorm
