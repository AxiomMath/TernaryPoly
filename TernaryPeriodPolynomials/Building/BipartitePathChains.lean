module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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


noncomputable section
namespace TernaryPoly.BipartitePathChains

variable {L P : Type*}

abbrev Vertex (L P : Type*) := L ⊕ P
abbrev Edge (r : L → P → Prop) := {e : L × P // r e.1 e.2}
abbrev Chain₁ (r : L → P → Prop) := Edge r →₀ ℚ
abbrev Chain₀ (L P : Type*) := Vertex L P →₀ ℚ

/-- An incidence edge is oriented from its line to its plane. -/
def boundary (r : L → P → Prop) : Chain₁ r →ₗ[ℚ] Chain₀ L P :=
  Finsupp.lsum ℚ fun e =>
    Finsupp.lsingle (.inr e.val.2) - Finsupp.lsingle (.inl e.val.1)

@[simp] theorem boundary_single (r : L → P → Prop) (e : Edge r) (c : ℚ) :
    boundary r (Finsupp.single e c) =
      Finsupp.single (.inr e.val.2) c - Finsupp.single (.inl e.val.1) c := by
  simp only [boundary, Finsupp.lsum_single, LinearMap.sub_apply, Finsupp.lsingle_apply]

/-- Adjacency is the incidence relation in either traversal direction. -/
def Adj (r : L → P → Prop) : Vertex L P → Vertex L P → Prop
  | .inl l, .inr p => r l p
  | .inr p, .inl l => r l p
  | _, _ => False

/-- The actual bipartite incidence graph. -/
def graph (r : L → P → Prop) : SimpleGraph (Vertex L P) where
  Adj := Adj r
  symm.symm u v h := by cases u <;> cases v <;> exact h
  loopless.irrefl v h := by cases v <;> exact h

/-- A traversed edge contributes its orientation sign to the incidence chain. -/
def stepChain (r : L → P → Prop) :
    {u v : Vertex L P} → (graph r).Adj u v → Chain₁ r
  | .inl l, .inr p, h => Finsupp.single ⟨(l, p), h⟩ 1
  | .inr p, .inl l, h => -Finsupp.single ⟨(l, p), h⟩ 1
  | .inl _, .inl _, h => False.elim h
  | .inr _, .inr _, h => False.elim h

@[simp] theorem stepChain_symm (r : L → P → Prop) {u v : Vertex L P}
    (h : (graph r).Adj u v) : stepChain r h.symm = -stepChain r h := by
  cases u <;> cases v
  · exact False.elim h
  · rfl
  · simp only [stepChain, neg_neg]
  · exact False.elim h

@[simp] theorem boundary_stepChain (r : L → P → Prop) {u v : Vertex L P}
    (h : (graph r).Adj u v) :
    boundary r (stepChain r h) = Finsupp.single v 1 - Finsupp.single u 1 := by
  cases u <;> cases v
  · exact False.elim h
  · exact boundary_single r _ _
  · simp only [stepChain, map_neg, boundary_single, neg_sub]
  · exact False.elim h

/-- The finite oriented incidence chain traced by a graph walk. -/
def walkChain (r : L → P → Prop) :
    {u v : Vertex L P} → (graph r).Walk u v → Chain₁ r
  | _, _, .nil => 0
  | _, _, .cons h p => stepChain r h + walkChain r p

@[simp] theorem walkChain_nil (r : L → P → Prop) (u : Vertex L P) :
    walkChain r (SimpleGraph.Walk.nil : (graph r).Walk u u) = 0 := rfl

@[simp] theorem walkChain_cons (r : L → P → Prop) {u v w : Vertex L P}
    (h : (graph r).Adj u v) (p : (graph r).Walk v w) :
    walkChain r (.cons h p) = stepChain r h + walkChain r p := rfl

/-- Internal vertices cancel, leaving exactly the endpoints. -/
theorem boundary_walkChain (r : L → P → Prop) {u v : Vertex L P}
    (p : (graph r).Walk u v) :
    boundary r (walkChain r p) = Finsupp.single v 1 - Finsupp.single u 1 := by
  induction p with
  | nil => simp only [walkChain_nil, map_zero, sub_self]
  | cons h p ih =>
    rw [walkChain_cons, map_add, boundary_stepChain, ih]
    abel

/-- Concatenation adds the two oriented chains. -/
theorem walkChain_append (r : L → P → Prop) {u v w : Vertex L P}
    (p : (graph r).Walk u v) (q : (graph r).Walk v w) :
    walkChain r (p.append q) = walkChain r p + walkChain r q := by
  induction p with
  | nil => simp only [SimpleGraph.Walk.nil_append, walkChain_nil, zero_add]
  | cons h p ih => simp only [SimpleGraph.Walk.cons_append, walkChain_cons, ih, add_assoc]

/-- Reversing the walk negates its oriented chain. -/
theorem walkChain_reverse (r : L → P → Prop) {u v : Vertex L P}
    (p : (graph r).Walk u v) : walkChain r p.reverse = -walkChain r p := by
  induction p with
  | nil => simp only [SimpleGraph.Walk.reverse_nil, walkChain_nil, neg_zero]
  | cons h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkChain_append, walkChain_cons,
      walkChain_nil, add_zero, stepChain_symm r h, ih, walkChain_cons]
    abel

/-- A closed walk gives an element of the actual boundary kernel. -/
def closedWalkCycle (r : L → P → Prop) {u : Vertex L P}
    (p : (graph r).Walk u u) : LinearMap.ker (boundary r) :=
  ⟨walkChain r p, by rw [LinearMap.mem_ker, boundary_walkChain, sub_self]⟩

/-- Preconnectedness supplies a chosen finite path chain between any two vertices. -/
def chosenPathChain (r : L → P → Prop) (hc : (graph r).Preconnected)
    (u v : Vertex L P) : Chain₁ r :=
  walkChain r (Classical.choice (hc u v))

@[simp] theorem boundary_chosenPathChain (r : L → P → Prop) (hc : (graph r).Preconnected)
    (u v : Vertex L P) :
    boundary r (chosenPathChain r hc u v) = Finsupp.single v 1 - Finsupp.single u 1 :=
  boundary_walkChain r _

/-- Connectedness supplies a path-chain family from any fixed base vertex. -/
theorem exists_path_family (r : L → P → Prop) (hc : (graph r).Connected)
    (base : Vertex L P) :
    ∃ paths : Vertex L P → Chain₁ r,
      ∀ v, boundary r (paths v) = Finsupp.single v 1 - Finsupp.single base 1 :=
  ⟨chosenPathChain r hc.preconnected base, boundary_chosenPathChain r hc.preconnected base⟩

/-- The opposite path convention has boundary base minus endpoint, as in PathCocycle.Paths. -/
def pathsToBase (r : L → P → Prop) (hc : (graph r).Preconnected)
    (base v : Vertex L P) : Chain₁ r := -chosenPathChain r hc base v

@[simp] theorem boundary_pathsToBase (r : L → P → Prop) (hc : (graph r).Preconnected)
    (base v : Vertex L P) :
    boundary r (pathsToBase r hc base v) = Finsupp.single base 1 - Finsupp.single v 1 := by
  rw [pathsToBase, map_neg, boundary_chosenPathChain, neg_sub]

section Equivalences
variable {L' P' : Type*} {r : L → P → Prop} {s : L' → P' → Prop}

/-- A pair of relation-preserving endpoint bijections induces a bijection on oriented edges. -/
def edgeEquiv (eL : L ≃ L') (eP : P ≃ P')
    (hr : ∀ l p, r l p ↔ s (eL l) (eP p)) : Edge r ≃ Edge s where
  toFun e := ⟨(eL e.val.1, eP e.val.2), (hr _ _).mp e.property⟩
  invFun e := ⟨(eL.symm e.val.1, eP.symm e.val.2), by
    apply (hr _ _).mpr
    simpa only [Equiv.apply_symm_apply] using e.property⟩
  left_inv e := by apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  right_inv e := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

/-- Endpoint-preserving incidence bijections act linearly on edge chains. -/
def chainEquiv (eL : L ≃ L') (eP : P ≃ P')
    (hr : ∀ l p, r l p ↔ s (eL l) (eP p)) : Chain₁ r ≃ₗ[ℚ] Chain₁ s :=
  Finsupp.domLCongr (edgeEquiv eL eP hr)

/-- The corresponding linear bijection on vertex chains. -/
def vertexChainEquiv (eL : L ≃ L') (eP : P ≃ P') : Chain₀ L P ≃ₗ[ℚ] Chain₀ L' P' :=
  Finsupp.domLCongr (Equiv.sumCongr eL eP)

@[simp] theorem chainEquiv_single (eL : L ≃ L') (eP : P ≃ P')
    (hr : ∀ l p, r l p ↔ s (eL l) (eP p)) (e : Edge r) (c : ℚ) :
    chainEquiv eL eP hr (Finsupp.single e c) = Finsupp.single (edgeEquiv eL eP hr e) c :=
  Finsupp.domLCongr_single _ _ _

@[simp] theorem vertexChainEquiv_single (eL : L ≃ L') (eP : P ≃ P')
    (v : Vertex L P) (c : ℚ) :
    vertexChainEquiv eL eP (Finsupp.single v c) = Finsupp.single (Equiv.sumCongr eL eP v) c :=
  Finsupp.domLCongr_single _ _ _

/-- The actual boundary map is equivariant under incidence-preserving endpoint bijections. -/
theorem boundary_chainEquiv (eL : L ≃ L') (eP : P ≃ P')
    (hr : ∀ l p, r l p ↔ s (eL l) (eP p)) (c : Chain₁ r) :
    boundary s (chainEquiv eL eP hr c) = vertexChainEquiv eL eP (boundary r c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e c =>
    simp only [chainEquiv_single, boundary_single, map_sub, vertexChainEquiv_single]
    rfl

/-- Incidence bijections preserve the actual cycle kernel. -/
theorem chainEquiv_mem_ker (eL : L ≃ L') (eP : P ≃ P')
    (hr : ∀ l p, r l p ↔ s (eL l) (eP p)) {c : Chain₁ r}
    (hc : c ∈ LinearMap.ker (boundary r)) :
    chainEquiv eL eP hr c ∈ LinearMap.ker (boundary s) := by
  rw [LinearMap.mem_ker, boundary_chainEquiv, LinearMap.mem_ker.mp hc, map_zero]

end Equivalences

end TernaryPoly.BipartitePathChains
