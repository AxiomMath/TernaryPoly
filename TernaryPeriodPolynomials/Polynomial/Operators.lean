module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
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
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

abbrev TernaryPolynomial := MvPolynomial (Fin 3) ℚ

/-- The order-three substitution in the norm relation. -/
def A : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![-X 1, X 0 - X 1, X 2]

/-- The second substitution in the norm relation. -/
def A2 := (bind₁ ![X 1 - X 0, -X 0, X 2] :
  TernaryPolynomial →ₐ[ℚ] TernaryPolynomial)

/-- The cyclic substitution used literally. -/
def C : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 1, X 2, X 0]

/-- Swap the first two coordinates. -/
def S : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 1, X 0, X 2]

theorem A_comp_A : A.comp A = A2 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A, A2, AlgHom.comp_apply]
  abel

theorem A_comp_A2 : A.comp A2 = AlgHom.id ℚ TernaryPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A, A2, AlgHom.comp_apply]

theorem C_comp_C_comp_C : C.comp (C.comp C) = AlgHom.id ℚ TernaryPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [C, AlgHom.comp_apply]

theorem S_comp_S : S.comp S = AlgHom.id ℚ TernaryPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [S, AlgHom.comp_apply]

theorem A_comp_S : A.comp S = S.comp A2 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A, A2, S, AlgHom.comp_apply]

theorem A2_comp_S : A2.comp S = S.comp A := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A, A2, S, AlgHom.comp_apply]

theorem C_comp_S : C.comp S = S.comp (C.comp C) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [C, S, AlgHom.comp_apply]

@[simp] theorem A_A (f : TernaryPolynomial) : A (A f) = A2 f :=
  DFunLike.congr_fun A_comp_A f

@[simp] theorem A_A2 (f : TernaryPolynomial) : A (A2 f) = f :=
  DFunLike.congr_fun A_comp_A2 f

@[simp] theorem C_C_C (f : TernaryPolynomial) : C (C (C f)) = f :=
  DFunLike.congr_fun C_comp_C_comp_C f

@[simp] theorem S_S (f : TernaryPolynomial) : S (S f) = f :=
  DFunLike.congr_fun S_comp_S f

theorem A_S (f : TernaryPolynomial) : A (S f) = S (A2 f) :=
  DFunLike.congr_fun A_comp_S f

theorem A2_S (f : TernaryPolynomial) : A2 (S f) = S (A f) :=
  DFunLike.congr_fun A2_comp_S f

theorem C_S (f : TernaryPolynomial) : C (S f) = S (C (C f)) :=
  DFunLike.congr_fun C_comp_S f

theorem A_A_A (f : TernaryPolynomial) : A (A (A f)) = f := by
  rw [A_A f, A_A2]

theorem S_A_S (f : TernaryPolynomial) : S (A (S f)) = A2 f := by
  rw [A_S, S_S]

theorem S_C_S (f : TernaryPolynomial) : S (C (S f)) = C (C f) := by
  rw [C_S, S_S]

/-- The linear norm operator `1 + A + A²`. -/
def N : TernaryPolynomial →ₗ[ℚ] TernaryPolynomial :=
  LinearMap.id + A.toLinearMap + A2.toLinearMap

@[simp] theorem N_apply (f : TernaryPolynomial) : N f = f + A f + A2 f := rfl

/-- The two polynomial equations. -/
def PeriodRelations (f : TernaryPolynomial) : Prop := C f = f ∧ N f = 0

theorem periodRelations_iff (f : TernaryPolynomial) : PeriodRelations f ↔
    bind₁ ![X 1, X 2, X 0] f = f ∧
    f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0 := Iff.rfl

theorem N_S (f : TernaryPolynomial) : N (S f) = S (N f) := by
  simp only [N_apply, A_S, A2_S, map_add]
  abel

theorem PeriodRelations.swap {f : TernaryPolynomial} (hf : PeriodRelations f) :
    PeriodRelations (S f) := by
  constructor
  · rw [C_S, hf.1, hf.1]
  · rw [N_S, hf.2, map_zero]

theorem PeriodRelations.add {f g : TernaryPolynomial}
    (hf : PeriodRelations f) (hg : PeriodRelations g) : PeriodRelations (f + g) := by
  constructor
  · rw [map_add, hf.1, hg.1]
  · rw [map_add, hf.2, hg.2, add_zero]

theorem PeriodRelations.sub {f g : TernaryPolynomial}
    (hf : PeriodRelations f) (hg : PeriodRelations g) : PeriodRelations (f - g) := by
  constructor
  · rw [map_sub, hf.1, hg.1]
  · rw [map_sub, hf.2, hg.2, sub_self]

theorem PeriodRelations.smul {f : TernaryPolynomial}
    (hf : PeriodRelations f) (a : ℚ) : PeriodRelations (a • f) := by
  constructor
  · rw [map_smul, hf.1]
  · rw [map_smul, hf.2, smul_zero]

/-- Projection to the swap-fixed part of a polynomial. -/
def symmetricPart (f : TernaryPolynomial) : TernaryPolynomial := (1 / 2 : ℚ) • (f + S f)

/-- Projection to the swap-negated part of a polynomial. -/
def alternatingPart (f : TernaryPolynomial) : TernaryPolynomial := (1 / 2 : ℚ) • (f - S f)

theorem symmetricPart_relations {f : TernaryPolynomial} (hf : PeriodRelations f) :
    PeriodRelations (symmetricPart f) := (hf.add hf.swap).smul _

theorem alternatingPart_relations {f : TernaryPolynomial} (hf : PeriodRelations f) :
    PeriodRelations (alternatingPart f) := (hf.sub hf.swap).smul _

@[simp] theorem S_symmetricPart (f : TernaryPolynomial) :
    S (symmetricPart f) = symmetricPart f := by
  simp [symmetricPart, map_smul, add_comm]

@[simp] theorem S_alternatingPart (f : TernaryPolynomial) :
    S (alternatingPart f) = -alternatingPart f := by
  simp [alternatingPart, map_smul, ← smul_neg, neg_sub]

theorem symmetricPart_add_alternatingPart (f : TernaryPolynomial) :
    symmetricPart f + alternatingPart f = f := by
  rw [symmetricPart, alternatingPart, ← smul_add]
  have h : (f + S f) + (f - S f) = f + f := by abel
  rw [h, ← two_smul ℚ f, smul_smul]
  norm_num

theorem symmetry_reduction {f : TernaryPolynomial} (hf : PeriodRelations f) :
    ∃ g h : TernaryPolynomial, PeriodRelations g ∧ PeriodRelations h ∧
      S g = g ∧ S h = -h ∧ f = g + h := by
  exact ⟨symmetricPart f, alternatingPart f, symmetricPart_relations hf,
    alternatingPart_relations hf, S_symmetricPart f, S_alternatingPart f,
    (symmetricPart_add_alternatingPart f).symm⟩

end TernaryPoly
