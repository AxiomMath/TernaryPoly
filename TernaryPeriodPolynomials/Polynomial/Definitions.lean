module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


/-! # Literal polynomial spaces over a commutative coefficient ring

The relations are identities of formal polynomials with explicit coefficient types. No characteristic assumption,
reducedness assumption, or splitting into parity sectors is part of the definitions.
-/


open MvPolynomial

noncomputable section
namespace TernaryPoly.Paper

abbrev Ternary (R : Type*) [CommSemiring R] := MvPolynomial (Fin 3) R
abbrev Binary (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R

variable {R : Type*} [CommRing R]

/-- The two ternary equations in the paper. -/
def Solution (f : Ternary R) : Prop :=
  bind₁ ![X 1, X 2, X 0] f = f ∧
    f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0

theorem Solution.cyclic {f : Ternary R} (hf : Solution f) :
    bind₁ ![X 1, X 2, X 0] f = f := hf.1

theorem Solution.norm {f : Ternary R} (hf : Solution f) :
    f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0 := hf.2

/-- The space of all ternary solutions, without a homogeneity restriction. -/
def solutions (R : Type*) [CommRing R] : Submodule R (Ternary R) where
  carrier := {f | Solution f}
  zero_mem' := by simp [Solution]
  add_mem' := by
    rintro f g ⟨hfc, hfn⟩ ⟨hgc, hgn⟩
    refine ⟨by simp only [map_add, hfc, hgc], ?_⟩
    simp only [map_add]
    linear_combination hfn + hgn
  smul_mem' := by
    rintro a f ⟨hc, hn⟩
    refine ⟨by rw [map_smul, hc], ?_⟩
    rw [map_smul, map_smul, ← smul_add, ← smul_add, hn, smul_zero]

/-- The paper's homogeneous ternary solution space `W_n(R)`. -/
def solutionSpace (R : Type*) [CommRing R] (n : ℕ) : Submodule R (Ternary R) :=
  homogeneousSubmodule (Fin 3) R n ⊓ solutions R

/-- The four full normalized binary period equations, in the paper's order. -/
def PeriodRelations (q : Binary R) : Prop :=
  bind₁ (![0, X 1] : Fin 2 → Binary R) q = 0 ∧ bind₁ (![X 0, 0] : Fin 2 → Binary R) q = 0 ∧
    q + bind₁ ![-X 1, X 0] q = 0 ∧
      q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0

theorem PeriodRelations.axis_first {q : Binary R} (hq : PeriodRelations q) :
    bind₁ (![0, X 1] : Fin 2 → Binary R) q = 0 := hq.1

theorem PeriodRelations.axis_second {q : Binary R} (hq : PeriodRelations q) :
    bind₁ (![X 0, 0] : Fin 2 → Binary R) q = 0 := hq.2.1

theorem PeriodRelations.two_term {q : Binary R} (hq : PeriodRelations q) :
    q + bind₁ ![-X 1, X 0] q = 0 := hq.2.2.1

theorem PeriodRelations.three_term {q : Binary R} (hq : PeriodRelations q) :
    q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0 := hq.2.2.2

/-- The two period identities before imposing the axis normalization. -/
def PeriodIdentities (q : Binary R) : Prop :=
  q + bind₁ ![-X 1, X 0] q = 0 ∧
    q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0

/-- Homogeneous binary periods before quotienting or normalizing the axis term. -/
def periodAmbient (R : Type*) [CommRing R] (n : ℕ) : Submodule R (Binary R) :=
  homogeneousSubmodule (Fin 2) R n ⊓
    (LinearMap.id + (bind₁ ![-X 1, X 0]).toLinearMap : Binary R →ₗ[R] Binary R).ker ⊓
    (LinearMap.id + (bind₁ ![-X 1, X 0 - X 1]).toLinearMap +
      (bind₁ ![X 1 - X 0, -X 0]).toLinearMap : Binary R →ₗ[R] Binary R).ker

/-- All normalized binary periods, with both parity sectors retained. -/
def periods (R : Type*) [CommRing R] : Submodule R (Binary R) where
  carrier := {q | PeriodRelations q}
  zero_mem' := by simp [PeriodRelations]
  add_mem' := by
    rintro p q ⟨hp₀, hp₁, hpS, hpN⟩ ⟨hq₀, hq₁, hqS, hqN⟩
    refine ⟨by simp only [map_add, hp₀, hq₀, add_zero],
      by simp only [map_add, hp₁, hq₁, add_zero], ?_, ?_⟩
    · simp only [map_add]
      linear_combination hpS + hqS
    · simp only [map_add]
      linear_combination hpN + hqN
  smul_mem' := by
    rintro a q ⟨h₀, h₁, hS, hN⟩
    refine ⟨by rw [map_smul, h₀, smul_zero], by rw [map_smul, h₁, smul_zero], ?_, ?_⟩
    · rw [map_smul, ← smul_add, hS, smul_zero]
    · rw [map_smul, map_smul, ← smul_add, ← smul_add, hN, smul_zero]

/-- The full normalized homogeneous binary space `𝒫⁰_n(R)`. -/
def periodSpace (R : Type*) [CommRing R] (n : ℕ) : Submodule R (Binary R) :=
  homogeneousSubmodule (Fin 2) R n ⊓ periods R

/-- The symmetric sector; cyclicity is already imposed in `solutionSpace`. -/
def symmetricSolutionSpace (R : Type*) [CommRing R] (n : ℕ) :
    Submodule R (Ternary R) :=
  solutionSpace R n ⊓ ((bind₁ ![X 1, X 0, X 2]).toLinearMap - LinearMap.id : Ternary R →ₗ[R] Ternary R).ker

/-- The alternating sector; no eigenspace splitting is assumed over `R`. -/
def alternatingSolutionSpace (R : Type*) [CommRing R] (n : ℕ) :
    Submodule R (Ternary R) :=
  solutionSpace R n ⊓ ((bind₁ ![X 1, X 0, X 2]).toLinearMap + LinearMap.id : Ternary R →ₗ[R] Ternary R).ker

/-- The normalized even binary sector (parity in the first variable). -/
def evenPeriodSpace (R : Type*) [CommRing R] (n : ℕ) : Submodule R (Binary R) :=
  periodSpace R n ⊓ ((bind₁ ![-X 0, X 1]).toLinearMap - LinearMap.id : Binary R →ₗ[R] Binary R).ker

/-- The normalized odd binary sector (parity in the first variable). -/
def oddPeriodSpace (R : Type*) [CommRing R] (n : ℕ) : Submodule R (Binary R) :=
  periodSpace R n ⊓ ((bind₁ ![-X 0, X 1]).toLinearMap + LinearMap.id : Binary R →ₗ[R] Binary R).ker

/-- Every monomial with nonzero coefficient omits at least one variable. -/
def Pairwise (f : Ternary R) : Prop :=
  ∀ d : Fin 3 →₀ ℕ, (∀ i, 0 < d i) → f.coeff d = 0

@[simp] theorem mem_solutions (f : Ternary R) : f ∈ solutions R ↔ Solution f := Iff.rfl
@[simp] theorem mem_solutionSpace (n : ℕ) (f : Ternary R) :
    f ∈ solutionSpace R n ↔ f.IsHomogeneous n ∧ Solution f := Iff.rfl
@[simp] theorem mem_periods (q : Binary R) : q ∈ periods R ↔ PeriodRelations q := Iff.rfl
@[simp] theorem mem_periodSpace (n : ℕ) (q : Binary R) :
    q ∈ periodSpace R n ↔ q.IsHomogeneous n ∧ PeriodRelations q := Iff.rfl

end TernaryPoly.Paper
