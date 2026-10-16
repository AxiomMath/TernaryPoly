module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
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
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Limits HomologicalComplex

variable {R : Type} [Ring R]

/-- The actual degree-zero augmentation, as a morphism from a complex of constants. -/
def augmentation {K : CochainComplex (ModuleCat R) ℕ} {F : ModuleCat R}
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) :
    (CochainComplex.single₀ (ModuleCat R)).obj F ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K F).symm ⟨a, ha⟩

@[simp] theorem augmentation_f_zero {K : CochainComplex (ModuleCat R) ℕ} {F : ModuleCat R}
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) :
    (augmentation a ha).f 0 = a :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero a ha

/-- Exactness of the augmented sequence and injectivity identify the actual H0 map. -/
theorem augmentation_quasiIso_zero {K : CochainComplex (ModuleCat R) ℕ} {F : ModuleCat R}
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (hex : (ShortComplex.mk a (K.d 0 1) ha).Exact) [Mono a] :
    QuasiIsoAt (augmentation a ha) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
  simpa only [shortComplexFunctor', sc', augmentation_f_zero, CochainComplex.single₀_obj_zero] using
    (show (ShortComplex.mk a (K.d 0 1) ha).Exact ∧ Mono a from ⟨hex, inferInstance⟩)

/-- A literal augmented resolution is a quasi-isomorphism from constants. All exactness
assumptions are explicit and must be established in each geometric application. -/
theorem augmentation_quasiIso {K : CochainComplex (ModuleCat R) ℕ} {F : ModuleCat R}
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (hex : (ShortComplex.mk a (K.d 0 1) ha).Exact) [Mono a]
    (hpos : ∀ n : ℕ, K.ExactAt (n+1)) : QuasiIso (augmentation a ha) := by
  constructor
  intro n
  cases n with
  | zero => exact augmentation_quasiIso_zero a ha hex
  | succ n =>
    apply (quasiIsoAt_iff_exactAt (augmentation a ha) (n+1) ?_).mpr (hpos n)
    apply (exactAt_iff_isZero_homology _ _).mpr
    exact isZero_single_obj_homology _ _ _ _ (Nat.succ_ne_zero n)

/-- Commuting augmentation squares are already commuting chain-level squares. -/
theorem augmentation_natural {K L : CochainComplex (ModuleCat R) ℕ}
    {F G : ModuleCat R} (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (b : G ⟶ L.X 0) (hb : b ≫ L.d 0 1 = 0)
    (f : F ⟶ G) (k : K ⟶ L) (h : a ≫ k.f 0 = f ≫ b) :
    augmentation a ha ≫ k =
      (CochainComplex.single₀ (ModuleCat R)).map f ≫ augmentation b hb := by
  apply (CochainComplex.fromSingle₀Equiv L F).injective
  apply Subtype.ext
  simpa using h

/-- The canonical cohomology comparison furnished by a span of actual quasi-isomorphisms. -/
def comparison {A K L : CochainComplex (ModuleCat R) ℕ}
    (a : A ⟶ K) (b : A ⟶ L) (n : ℕ) [QuasiIsoAt a n] [QuasiIsoAt b n] :
    K.homology n ≅ L.homology n :=
  (isoOfQuasiIsoAt a n).symm ≪≫ isoOfQuasiIsoAt b n

/-- The comparison retains the actual maps induced by both arms of the span. -/
theorem comparison_augmented {A K L : CochainComplex (ModuleCat R) ℕ}
    (a : A ⟶ K) (b : A ⟶ L) (n : ℕ) [QuasiIsoAt a n] [QuasiIsoAt b n] :
    homologyMap a n ≫ (comparison a b n).hom = homologyMap b n := by
  simp [comparison]

/-- A commuting morphism of spans gives a commuting comparison square. This applies to
restriction, coefficient maps, and support-forgetting whenever those actual maps exist. -/
theorem comparison_natural {A K L A' K' L' : CochainComplex (ModuleCat R) ℕ}
    (a : A ⟶ K) (b : A ⟶ L) (a' : A' ⟶ K') (b' : A' ⟶ L')
    (u : A ⟶ A') (v : K ⟶ K') (w : L ⟶ L')
    (ha : a ≫ v = u ≫ a') (hb : b ≫ w = u ≫ b') (n : ℕ)
    [QuasiIsoAt a n] [QuasiIsoAt b n] [QuasiIsoAt a' n] [QuasiIsoAt b' n] :
    (comparison a b n).hom ≫ homologyMap w n =
      homologyMap v n ≫ (comparison a' b' n).hom := by
  apply (cancel_epi (homologyMap a n)).mp
  have haH : homologyMap a n ≫ homologyMap v n =
      homologyMap u n ≫ homologyMap a' n := by
    rw [← homologyMap_comp, ← homologyMap_comp, ha]
  have hbH : homologyMap b n ≫ homologyMap w n =
      homologyMap u n ≫ homologyMap b' n := by
    rw [← homologyMap_comp, ← homologyMap_comp, hb]
  rw [← Category.assoc, comparison_augmented, hbH, ← Category.assoc, haH,
    Category.assoc, comparison_augmented]

end TernaryPoly.SmoothSingularComparison
