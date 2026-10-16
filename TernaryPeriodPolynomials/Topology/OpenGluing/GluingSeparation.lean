module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Bases
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
open Topology TopologicalSpace CategoryTheory

namespace TernaryPoly.OpenGluingSeparation

universe u
variable (D : TopCat.GlueData.{u})

/-- The actual disjoint union of charts maps openly and surjectively onto the gluing. -/
def chartSigma (x : Σ i, D.U i) : D.toGlueData.glued := D.toGlueData.ι x.1 x.2

theorem chartSigma_continuous : Continuous (chartSigma D) :=
  continuous_sigma fun i => (D.toGlueData.ι i).hom.continuous

theorem chartSigma_isOpenMap : IsOpenMap (chartSigma D) :=
  isOpenMap_sigma.mpr fun i => (D.ι_isOpenEmbedding i).isOpenMap

theorem chartSigma_surjective : Function.Surjective (chartSigma D) := by
  intro x
  obtain ⟨i,y,h⟩ := D.ι_jointly_surjective x
  exact ⟨⟨i,y⟩,h⟩

/-- Closedness can be checked on every pair of open charts. -/
theorem isClosed_iff_chart_pairs (s : Set (D.toGlueData.glued × D.toGlueData.glued)) :
    IsClosed s ↔ ∀ i j, IsClosed (Prod.map (D.toGlueData.ι i) (D.toGlueData.ι j) ⁻¹' s) := by
  constructor
  · intro hs i j
    exact hs.preimage ((D.toGlueData.ι i).hom.continuous.prodMap
      (D.toGlueData.ι j).hom.continuous)
  · intro hs
    rw [← isOpen_compl_iff]
    have he : sᶜ = ⋃ i, ⋃ j,
        Prod.map (D.toGlueData.ι i) (D.toGlueData.ι j) ''
          (Prod.map (D.toGlueData.ι i) (D.toGlueData.ι j) ⁻¹' s)ᶜ := by
      ext p
      constructor
      · intro hp
        obtain ⟨i,x,hx⟩ := D.ι_jointly_surjective p.1
        obtain ⟨j,y,hy⟩ := D.ι_jointly_surjective p.2
        exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,⟨(x,y),by simpa [hx,hy],by simp [hx,hy]⟩⟩⟩
      · intro hp
        obtain ⟨i,hp⟩ := Set.mem_iUnion.mp hp
        obtain ⟨j,q,hq,rfl⟩ := Set.mem_iUnion.mp hp
        exact hq
    rw [he]
    exact isOpen_iUnion fun i => isOpen_iUnion fun j =>
      ((D.ι_isOpenEmbedding i).isOpenMap.prodMap
        (D.ι_isOpenEmbedding j).isOpenMap) _ (hs i j).isOpen_compl

/-- An open gluing is Hausdorff exactly when all its actual chart relations are closed. -/
theorem t2Space_iff_closed_relations :
    T2Space D.toGlueData.glued ↔
      ∀ i j, IsClosed {p : D.U i × D.U j | D.Rel ⟨i,p.1⟩ ⟨j,p.2⟩} := by
  rw [t2_iff_isClosed_diagonal,isClosed_iff_chart_pairs]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  have he : Prod.map (D.toGlueData.ι i) (D.toGlueData.ι j) ⁻¹' Set.diagonal D.toGlueData.glued =
      {p : D.U i × D.U j | D.Rel ⟨i,p.1⟩ ⟨j,p.2⟩} := by
    ext p
    exact D.ι_eq_iff_rel i j p.1 p.2
  rw [he]

/-- Countably many second-countable open charts give a second-countable gluing. -/
theorem secondCountable [Countable D.J] [∀ i, SecondCountableTopology (D.U i)] :
    SecondCountableTopology D.toGlueData.glued :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    ⟨chartSigma_surjective D, chartSigma_continuous D, chartSigma_isOpenMap D⟩

end TernaryPoly.OpenGluingSeparation
