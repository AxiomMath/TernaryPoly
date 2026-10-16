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
namespace TernaryPoly.RelativeChainSequence
open CategoryTheory Limits HomologicalComplex

variable {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (i : K ⟶ L)

/-- The genuine relative chain complex, defined as the cokernel of a subcomplex inclusion. -/
abbrev relative : ChainComplex (ModuleCat.{0} ℚ) ℕ := cokernel i

/-- The literal absolute-to-relative chain projection. -/
abbrev projection : L ⟶ relative i := cokernel.π i

/-- The actual subcomplex, absolute complex and quotient form a short complex. -/
def sequence : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ) :=
  ShortComplex.mk i (projection i) (cokernel.condition i)

/-- A chain inclusion gives the genuine short exact relative chain sequence. -/
theorem shortExact [Mono i] : (sequence i).ShortExact where
  exact := (sequence i).exact_of_g_is_cokernel (cokernelIsCokernel i)
  mono_f := by change Mono i; infer_instance
  epi_g := by change Epi (cokernel.π i); infer_instance

/-- The actual subspace-to-ambient homology map. -/
abbrev inclusionMap (n : ℕ) := homologyMap i n

/-- The actual absolute-to-relative map on homology. -/
abbrev relativeMap (n : ℕ) := homologyMap (projection i) n

/-- The genuine boundary homomorphism goes from relative degree n+1 to subspace degree n. -/
def connecting [Mono i] (n : ℕ) : (relative i).homology (n+1) ⟶ K.homology n :=
  (shortExact i).δ (n+1) n rfl

/-- Exactness at actual absolute homology. -/
theorem range_inclusion_eq_kernel [Mono i] (n : ℕ) :
    LinearMap.range (inclusionMap i n).hom = LinearMap.ker (relativeMap i n).hom :=
  ((shortExact i).homology_exact₂ n).moduleCat_range_eq_ker

/-- An actual absolute homology class comes from the subspace precisely when its relative
class vanishes. -/
theorem relative_zero_iff_lifts [Mono i] (n : ℕ) (x : L.homology n) :
    relativeMap i n x = 0 ↔ ∃ y, inclusionMap i n y = x := by
  change x ∈ LinearMap.ker (relativeMap i n).hom ↔ x ∈ LinearMap.range (inclusionMap i n).hom
  rw [range_inclusion_eq_kernel]

/-- Exactness at the relative term, with the genuine degree-lowering boundary homomorphism. -/
theorem range_relative_eq_kernel_connecting [Mono i] (n : ℕ) :
    LinearMap.range (relativeMap i (n+1)).hom = LinearMap.ker (connecting i n).hom :=
  ((shortExact i).homology_exact₃ (n+1) n rfl).moduleCat_range_eq_ker

/-- Exactness at the subspace homology term. -/
theorem range_connecting_eq_kernel_inclusion [Mono i] (n : ℕ) :
    LinearMap.range (connecting i n).hom = LinearMap.ker (inclusionMap i n).hom :=
  ((shortExact i).homology_exact₁ (n+1) n rfl).moduleCat_range_eq_ker

/-- Surjectivity of the actual inclusion is precisely zero of the actual absolute-to-relative
map; no relative homology vanishing is presumed. -/
theorem inclusion_surjective_iff_relativeMap_zero [Mono i] (n : ℕ) :
    Function.Surjective (inclusionMap i n).hom ↔ relativeMap i n = 0 := by
  rw [← LinearMap.range_eq_top, range_inclusion_eq_kernel, LinearMap.ker_eq_top]
  exact ModuleCat.hom_ext_iff.symm

end TernaryPoly.RelativeChainSequence
