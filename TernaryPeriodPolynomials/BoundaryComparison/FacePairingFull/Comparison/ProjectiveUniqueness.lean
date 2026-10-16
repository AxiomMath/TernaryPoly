module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.Homotopy
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
# Chain maps from a complex of projectives to a resolution are determined by the augmentation

If `C` is a chain complex of projective objects in an abelian category and `Q` a projective resolution
of `Y`, two chain maps `C ⟶ Q.complex` that agree after composition with the augmentation `Q.π` in degree
zero are homotopic (the proof of `ProjectiveResolution.liftHomotopy`, which asks the source to be a
resolution, only uses that its terms are projective).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits Projective

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {C : ChainComplex 𝒜 ℕ} [∀ n, Projective (C.X n)]
  {Y : 𝒜} {Q : ProjectiveResolution Y}

/-- Auxiliary: the first step of the nullhomotopy. -/
def uniqHomotopyZeroZero (f : C ⟶ Q.complex) (comm : f.f 0 ≫ Q.π.f 0 = 0) :
    C.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0) comm

@[reassoc (attr := simp)]
lemma uniqHomotopyZeroZero_comp (f : C ⟶ Q.complex) (comm : f.f 0 ≫ Q.π.f 0 = 0) :
    uniqHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

/-- Auxiliary: the second step of the nullhomotopy. -/
def uniqHomotopyZeroOne (f : C ⟶ Q.complex) (comm : f.f 0 ≫ Q.π.f 0 = 0) :
    C.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective (f.f 1 - C.d 1 0 ≫ uniqHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
              uniqHomotopyZeroZero_comp, sub_self])

@[reassoc (attr := simp)]
lemma uniqHomotopyZeroOne_comp (f : C ⟶ Q.complex) (comm : f.f 0 ≫ Q.π.f 0 = 0) :
    uniqHomotopyZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - C.d 1 0 ≫ uniqHomotopyZeroZero f comm :=
  (Q.exact_succ 0).liftFromProjective_comp _ _

/-- Auxiliary: the inductive step of the nullhomotopy. -/
def uniqHomotopyZeroSucc (f : C ⟶ Q.complex) (n : ℕ) (g : C.X n ⟶ Q.complex.X (n + 1))
    (g' : C.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = C.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    C.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - C.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]
lemma uniqHomotopyZeroSucc_comp (f : C ⟶ Q.complex) (n : ℕ) (g : C.X n ⟶ Q.complex.X (n + 1))
    (g' : C.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = C.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    uniqHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - C.d _ _ ≫ g' :=
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

/-- A chain map from a complex of projectives to a resolution that vanishes on the augmentation is
null-homotopic. -/
def uniqHomotopyZero (f : C ⟶ Q.complex) (comm : f.f 0 ≫ Q.π.f 0 = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (uniqHomotopyZeroZero f comm) (by simp)
    (uniqHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨uniqHomotopyZeroSucc f n g g' w, by simp⟩

/-- **Uniqueness up to homotopy**: two chain maps from a complex of projectives to a resolution with
the same augmentation are homotopic. -/
def uniqHomotopy (g h : C ⟶ Q.complex) (comm : g.f 0 ≫ Q.π.f 0 = h.f 0 ≫ Q.π.f 0) :
    Homotopy g h :=
  Homotopy.equivSubZero.invFun (uniqHomotopyZero (g - h) (by
    rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, comm, sub_self]))

end

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
