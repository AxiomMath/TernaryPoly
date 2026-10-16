module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Bases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.WithTopology

@[expose] public section



/-! Actual second countability of countable restricted products with open distinguished sets. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open Set Filter Topology TopologicalSpace
open scoped RestrictedProduct

/-- A countable restricted product of second-countable spaces is second countable when every
distinguished subset is open. This uses its actual restricted-product topology. -/
theorem restrictedProduct_secondCountable {ι : Type} [Countable ι]
    (R : ι → Type) (A : ∀ i, Set (R i)) [∀ i, TopologicalSpace (R i)]
    [∀ i, SecondCountableTopology (R i)] (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  let hs (s : Finset ι) : cofinite ≤ 𝓟 ((s : Set ι)ᶜ) :=
    le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
  let O (s : Finset ι) : Set (Πʳ i, [R i, A i]) :=
    Set.range (RestrictedProduct.inclusion R A (hs s))
  let : ∀ s : Finset ι, SecondCountableTopology (O s) := fun s => by
    let : SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((s : Set ι)ᶜ)]) :=
      (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)).isInducing.secondCountableTopology
    exact (RestrictedProduct.isEmbedding_inclusion_principal (R := R) (A := A) (hs s)).toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover (U := O)
    (fun s => (RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hs s)).isOpen_range)
  apply eq_univ_of_forall
  intro x
  have hbad : {i | x i ∉ A i}.Finite := eventually_cofinite.mp x.property
  let s : Finset ι := hbad.toFinset
  apply mem_iUnion.mpr
  refine ⟨s, ⟨⟨x.val, ?_⟩, rfl⟩⟩
  apply eventually_principal.mpr
  intro i hi
  by_contra hnot
  exact hi (hbad.mem_toFinset.mpr hnot)

end GeneralEisenstein.Adelic

end
