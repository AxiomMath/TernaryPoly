module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
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


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits

/-- The actual first-quadrant module bicomplex used by global descent. -/
abbrev RealBicomplex := HomologicalComplex₂ (ModuleCat.{0} ℝ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)

variable (K : RealBicomplex)

/-- Literal horizontal differential of the actual bicomplex. -/
abbrev horizontal (p q : ℕ) := ((K.d p (p+1)).f q).hom

/-- Literal vertical differential of the actual bicomplex. -/
abbrev vertical (p q : ℕ) := ((K.X p).d q (q+1)).hom

/-- Actual horizontal differentials square to zero. -/
theorem horizontal_squared (p q : ℕ) (x : (K.X p).X q) :
    horizontal K (p+1) q (horizontal K p q x) = 0 :=
  congrArg (fun k => k.hom x) (K.d_f_comp_d_f p (p+1) (p+1+1) q)

/-- Actual vertical differentials square to zero. -/
theorem vertical_squared (p q : ℕ) (x : (K.X p).X q) :
    vertical K p (q+1) (vertical K p q x) = 0 :=
  congrArg (fun k => k.hom x) ((K.X p).d_comp_d q (q+1) (q+1+1))

/-- The two genuine bicomplex differentials commute before totalization signs. -/
theorem horizontal_vertical (p q : ℕ) (x : (K.X p).X q) :
    vertical K (p+1) q (horizontal K p q x) = horizontal K p (q+1) (vertical K p q x) :=
  congrArg (fun k => k.hom x) (K.d_comm p (p+1) q (q+1))

/-- The literal degree-one total module. -/
abbrev TotalOne := ((K.X 1).X 0) × ((K.X 0).X 1)

/-- The literal degree-two total module. -/
abbrev TotalTwo := ((K.X 2).X 0) × ((K.X 1).X 1) × ((K.X 0).X 2)

/-- The literal degree-three total module. -/
abbrev TotalThree := ((K.X 3).X 0) × ((K.X 2).X 1) × ((K.X 1).X 2) × ((K.X 0).X 3)

/-- The actual total differential in degrees one to two, including its horizontal-degree sign. -/
def totalOneD : TotalOne K →ₗ[ℝ] TotalTwo K :=
  ((horizontal K 1 0).comp (LinearMap.fst ℝ _ _)).prod
    (((-(vertical K 1 0).comp (LinearMap.fst ℝ _ _)) +
      (horizontal K 0 1).comp (LinearMap.snd ℝ _ _)).prod
        ((vertical K 0 1).comp (LinearMap.snd ℝ _ _)))

/-- The actual total differential in degrees two to three, including its horizontal-degree signs. -/
def totalTwoD : TotalTwo K →ₗ[ℝ] TotalThree K :=
  ((horizontal K 2 0).comp (LinearMap.fst ℝ _ _)).prod
    (((vertical K 2 0).comp (LinearMap.fst ℝ _ _) +
      ((horizontal K 1 1).comp (LinearMap.fst ℝ _ _)).comp (LinearMap.snd ℝ _ _)).prod
        (((-(vertical K 1 1).comp (LinearMap.fst ℝ _ _)).comp (LinearMap.snd ℝ _ _) +
          ((horizontal K 0 2).comp (LinearMap.snd ℝ _ _)).comp (LinearMap.snd ℝ _ _)).prod
            (((vertical K 0 2).comp (LinearMap.snd ℝ _ _)).comp (LinearMap.snd ℝ _ _))))

/-- The displayed signed total differentials square to zero by the genuine bicomplex identities. -/
theorem totalWindow_squared (x : TotalOne K) : totalTwoD K (totalOneD K x) = 0 := by
  rcases x with ⟨a,b⟩
  apply Prod.ext
  · exact horizontal_squared K 1 0 a
  apply Prod.ext
  · change vertical K 2 0 (horizontal K 1 0 a) +
      horizontal K 1 1 (-vertical K 1 0 a + horizontal K 0 1 b) = 0
    rw [map_add, map_neg, horizontal_squared, horizontal_vertical]
    abel
  apply Prod.ext
  · change -vertical K 1 1 (-vertical K 1 0 a + horizontal K 0 1 b) +
      horizontal K 0 2 (vertical K 0 1 b) = 0
    rw [map_add, map_neg, vertical_squared, horizontal_vertical]
    abel
  · exact vertical_squared K 0 1 b

/-- The genuine degree-two total short complex, with all actual components in degrees one through three. -/
def totalWindow : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.mk (ModuleCat.ofHom (totalOneD K)) (ModuleCat.ofHom (totalTwoD K)) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact totalWindow_squared K x)

end TernaryPoly.SmoothSingularGlobal
