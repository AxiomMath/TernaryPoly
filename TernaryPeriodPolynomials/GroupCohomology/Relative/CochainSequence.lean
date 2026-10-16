module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
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
namespace TernaryPoly.RelativeCochainSequence
open CategoryTheory Limits HomologicalComplex

variable {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (r : K ⟶ L)

/-- The actual kernel complex of a cochain restriction map. -/
abbrev relative : CochainComplex (ModuleCat.{0} ℚ) ℕ := kernel r

/-- The literal relative-to-absolute cochain inclusion. -/
abbrev inclusion : relative r ⟶ K := kernel.ι r

/-- The kernel, absolute and restricted cochain complexes form a genuine short complex. -/
def sequence : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ) :=
  ShortComplex.mk (inclusion r) r (kernel.condition r)

/-- Surjective restriction gives the actual short exact relative cochain sequence. -/
theorem shortExact [Epi r] : (sequence r).ShortExact where
  exact := (sequence r).exact_of_f_is_kernel (kernelIsKernel r)
  mono_f := by change Mono (kernel.ι r); infer_instance
  epi_g := by change Epi r; infer_instance

/-- The actual relative-to-absolute homomorphism on cohomology. -/
abbrev relativeMap (n : ℕ) : (relative r).homology n ⟶ K.homology n :=
  homologyMap (inclusion r) n

/-- The actual restriction homomorphism on cohomology. -/
abbrev restrictionMap (n : ℕ) : K.homology n ⟶ L.homology n := homologyMap r n

/-- The connecting homomorphism of the genuine relative cochain sequence. -/
def connecting [Epi r] (n : ℕ) : L.homology n ⟶ (relative r).homology (n+1) :=
  (shortExact r).δ n (n+1) rfl

/-- Exactness at absolute cohomology: the relative image is precisely the kernel of restriction. -/
theorem range_relative_eq_kernel [Epi r] (n : ℕ) :
    LinearMap.range (relativeMap r n).hom = LinearMap.ker (restrictionMap r n).hom :=
  ((shortExact r).homology_exact₂ n).moduleCat_range_eq_ker

/-- An absolute class has zero boundary restriction exactly when it has a relative lift. -/
theorem restriction_zero_iff_lifts [Epi r] (n : ℕ) (x : K.homology n) :
    restrictionMap r n x=0 ↔ ∃ y, relativeMap r n y=x := by
  change x∈LinearMap.ker (restrictionMap r n).hom ↔ x∈LinearMap.range (relativeMap r n).hom
  rw [range_relative_eq_kernel]

/-- Exactness at the boundary cohomology term. -/
theorem range_restriction_eq_kernel_connecting [Epi r] (n : ℕ) :
    LinearMap.range (restrictionMap r n).hom = LinearMap.ker (connecting r n).hom :=
  ((shortExact r).homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker

/-- Exactness at the subsequent relative cohomology term. -/
theorem range_connecting_eq_kernel_relative [Epi r] (n : ℕ) :
    LinearMap.range (connecting r n).hom = LinearMap.ker (relativeMap r (n+1)).hom :=
  ((shortExact r).homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker

/-- This formulation retains the genuine inner-cohomology vanishing gate explicitly. -/
theorem restriction_injective_iff_relativeMap_zero [Epi r] (n : ℕ) :
    Function.Injective (restrictionMap r n) ↔ relativeMap r n=0 := by
  rw [← LinearMap.ker_eq_bot]
  rw [←range_relative_eq_kernel]
  rw [LinearMap.range_eq_bot]
  exact ModuleCat.hom_ext_iff.symm

end TernaryPoly.RelativeCochainSequence
