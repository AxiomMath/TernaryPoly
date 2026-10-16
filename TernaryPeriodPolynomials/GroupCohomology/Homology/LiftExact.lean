module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Module.End
public import Mathlib.Control.Basic
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
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Lifting into an exact augmented complex

Mathlib's `ProjectiveResolution.lift` lifts a morphism `Y ⟶ Z` to a chain map from a projective
resolution of `Y` to a projective resolution of `Z`; only the exactness of the target is used.  Here the
target is any augmented exact complex `⋯ → Q₁ → Q₀ → Z → 0` (`ExactAugmentation`), for instance the
singular chains of a contractible space with a non-free action.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Projective

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An augmented acyclic complex `⋯ → Q₁ → Q₀ → Z → 0` (exact, no projectivity required). -/
structure ExactAugmentation (Z : C) where
  /-- the complex -/
  complex : ChainComplex C ℕ
  /-- the augmentation -/
  π : complex.X 0 ⟶ Z
  w : complex.d 1 0 ≫ π = 0
  epi_π : Epi π
  exact₀ : (ShortComplex.mk (complex.d 1 0) π w).Exact
  exact_succ : ∀ n : ℕ,
    (ShortComplex.mk (complex.d (n + 2) (n + 1)) (complex.d (n + 1) n)
      (complex.d_comp_d _ _ _)).Exact

namespace ExactAugmentation

variable {Y Z : C} (P : ProjectiveResolution Y) (Q : ExactAugmentation Z)

/-- Auxiliary construction for `lift`. -/
def liftFZero (f : Y ⟶ Z) : P.complex.X 0 ⟶ Q.complex.X 0 :=
  have := Q.epi_π
  Projective.factorThru (P.π.f 0 ≫ f) Q.π

/-- Auxiliary construction for `lift`. -/
def liftFOne (f : Y ⟶ Z) : P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero P Q f) (by
    have := Q.epi_π
    change (P.complex.d 1 0 ≫ liftFZero P Q f) ≫ Q.π = 0
    rw [Category.assoc, liftFZero, Projective.factorThru_comp]
    exact (ProjectiveResolution.complex_d_comp_π_f_zero_assoc P f).trans zero_comp)

theorem liftFOne_zero_comm (f : Y ⟶ Z) :
    liftFOne P Q f ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero P Q f := by
  apply Q.exact₀.liftFromProjective_comp

/-- Auxiliary construction for `lift`. -/
def liftFSucc (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X n)
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- A morphism `Y ⟶ Z` lifts to a chain map from a projective resolution of `Y` to any exact
augmented complex of `Z`. -/
def lift (f : Y ⟶ Z) : P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftFZero P Q f) (liftFOne P Q f) (liftFOne_zero_comm P Q f)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

theorem lift_f_zero_comp (f : Y ⟶ Z) : (lift P Q f).f 0 ≫ Q.π = P.π.f 0 ≫ f := by
  have := Q.epi_π
  simp [lift, liftFZero]

end ExactAugmentation

end TernaryPeriodPolynomials.Argument.GroupHomology
