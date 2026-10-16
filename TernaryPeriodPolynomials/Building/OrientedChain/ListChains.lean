module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Control.Basic
public import Mathlib.Data.Fintype.Option
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
public import Mathlib.Tactic.NormNum.Ineq

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedListChains

variable {V : Type*}

/-- Finite rational combinations of vertex lists, including the empty augmented simplex. -/
abbrev Raw (V : Type*) := List V →₀ ℚ

def rawSimplex (l : List V) : Raw V := Finsupp.single l 1

def rawCons (a : V) : Raw V →ₗ[ℚ] Raw V := Finsupp.lmapDomain ℚ ℚ (List.cons a)

@[simp] theorem rawCons_simplex (a : V) (l : List V) :
    rawCons a (rawSimplex l) = rawSimplex (a :: l) := by
  simp [rawCons,rawSimplex,Finsupp.lmapDomain_apply]

/-- The usual alternating deletion boundary, defined recursively before quotienting. -/
def rawBoundaryList : List V → Raw V
  | [] => 0
  | a :: l => rawSimplex l - rawCons a (rawBoundaryList l)

def rawBoundary : Raw V →ₗ[ℚ] Raw V :=
  Finsupp.lsum ℚ (fun l => LinearMap.toSpanSingleton ℚ _ (rawBoundaryList l))

@[simp] theorem rawBoundary_simplex (l : List V) :
    rawBoundary (rawSimplex l) = rawBoundaryList l := by
  simp [rawBoundary,rawSimplex]

@[simp] theorem rawBoundary_cons (a : V) (l : List V) :
    rawBoundary (rawSimplex (a :: l)) =
      rawSimplex l - rawCons a (rawBoundary (rawSimplex l)) := by
  simp only [rawBoundary_simplex,rawBoundaryList]

private theorem raw_ext {E : Type*} [AddCommGroup E] [Module ℚ E]
    {f g : Raw V →ₗ[ℚ] E} (h : ∀ l, f (rawSimplex l) = g (rawSimplex l)) : f = g := by
  apply Finsupp.lhom_ext
  intro l c
  have hc : Finsupp.single l c = c • rawSimplex l := by simp [rawSimplex]
  rw [hc,map_smul,map_smul,h]

theorem rawBoundary_rawCons (a : V) (c : Raw V) :
    rawBoundary (rawCons a c) = c - rawCons a (rawBoundary c) := by
  have h : rawBoundary.comp (rawCons a) =
      LinearMap.id - (rawCons a).comp rawBoundary := by
    apply raw_ext
    intro l
    simp only [LinearMap.comp_apply,rawCons_simplex,rawBoundary_cons,
      LinearMap.sub_apply,LinearMap.id_apply]
  exact LinearMap.congr_fun h c

theorem rawBoundary_squared (c : Raw V) : rawBoundary (rawBoundary c) = 0 := by
  have h : rawBoundary.comp rawBoundary = (0 : Raw V →ₗ[ℚ] Raw V) := by
    apply raw_ext
    intro l
    change rawBoundary (rawBoundary (rawSimplex l)) = 0
    induction l with
    | nil => simp [rawBoundaryList]
    | cons a l ih =>
      rw [rawBoundary_cons,map_sub,rawBoundary_rawCons,ih,map_zero]
      abel
  exact LinearMap.congr_fun h c

/-- Orientation relations and their finite linear combinations, stable under prefixing.
This is the alternating quotient, not an assumed topological chain module. -/
inductive Relation : Raw V → Prop
  | swap (a b : V) (l : List V) :
      Relation (rawSimplex (a :: b :: l) + rawSimplex (b :: a :: l))
  | cons (a : V) {c : Raw V} : Relation c → Relation (rawCons a c)
  | zero : Relation 0
  | add {c d : Raw V} : Relation c → Relation d → Relation (c+d)
  | smul (q : ℚ) {c : Raw V} : Relation c → Relation (q • c)

def relations (V : Type*) : Submodule ℚ (Raw V) where
  carrier := Relation
  zero_mem' := Relation.zero
  add_mem' := Relation.add
  smul_mem' := Relation.smul

theorem rawCons_relation (a : V) {c : Raw V} (hc : c ∈ relations V) :
    rawCons a c ∈ relations V := Relation.cons a hc

theorem rawCons_swap_relation (a b : V) (c : Raw V) :
    rawCons a (rawCons b c) + rawCons b (rawCons a c) ∈ relations V := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simpa only [map_add,add_add_add_comm] using (relations V).add_mem hc hd
  | single l q =>
    have h : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    rw [h,map_smul,map_smul,map_smul,map_smul,← smul_add]
    simpa only [rawCons_simplex] using (relations V).smul_mem q (Relation.swap a b l)

theorem rawBoundary_relation {c : Raw V} (hc : c ∈ relations V) :
    rawBoundary c ∈ relations V := by
  induction hc with
  | swap a b l =>
    have h := rawCons_swap_relation a b (rawBoundary (rawSimplex l))
    convert h using 1
    simp only [map_add,rawBoundary_cons,map_sub,rawCons_simplex]
    abel
  | cons a hc ih =>
    rw [rawBoundary_rawCons]
    exact (relations V).sub_mem hc (rawCons_relation a ih)
  | zero => simp
  | add hc hd ihc ihd => simpa only [map_add] using (relations V).add_mem ihc ihd
  | smul q hc ih => simpa only [map_smul] using (relations V).smul_mem q ih

/-- Actual rational oriented chains on all finite lists. -/
abbrev Chain (V : Type*) := Raw V ⧸ relations V

def simplex (l : List V) : Chain V := (relations V).mkQ (rawSimplex l)

def cons (a : V) : Chain V →ₗ[ℚ] Chain V :=
  (relations V).mapQ (relations V) (rawCons a) (fun _ hc => rawCons_relation a hc)

def boundary : Chain V →ₗ[ℚ] Chain V :=
  (relations V).mapQ (relations V) rawBoundary (fun _ hc => rawBoundary_relation hc)

@[simp] theorem cons_simplex (a : V) (l : List V) :
    cons a (simplex l) = simplex (a :: l) := by
  simp [cons,simplex,Submodule.mapQ_apply]

@[simp] theorem boundary_nil : boundary (simplex ([] : List V)) = 0 := by
  simp [boundary,simplex,Submodule.mapQ_apply,rawBoundaryList]

theorem boundary_cons (a : V) (l : List V) :
    boundary (simplex (a :: l)) = simplex l - cons a (boundary (simplex l)) := by
  simp [boundary,cons,simplex,Submodule.mapQ_apply,rawBoundaryList,Submodule.Quotient.mk_sub]

theorem boundary_squared (c : Chain V) : boundary (boundary c) = 0 := by
  refine Quotient.inductionOn' c (fun c => ?_)
  change (relations V).mkQ (rawBoundary (rawBoundary c)) = 0
  rw [rawBoundary_squared,map_zero]

theorem simplex_swap (a b : V) (l : List V) :
    simplex (a :: b :: l) + simplex (b :: a :: l) = 0 := by
  rw [simplex,simplex,← map_add]
  exact (Submodule.Quotient.mk_eq_zero (relations V)).mpr (Relation.swap a b l)

theorem simplex_swap_eq_neg (a b : V) (l : List V) :
    simplex (a :: b :: l) = -simplex (b :: a :: l) :=
  eq_neg_of_add_eq_zero_left (simplex_swap a b l)

theorem simplex_repeat_adjacent (a : V) (l : List V) : simplex (a :: a :: l) = 0 := by
  have h : (2 : ℚ) • simplex (a :: a :: l) = 0 := by
    simpa only [two_smul] using simplex_swap a a l
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem simplex_repeat (a : V) (p s : List V) : simplex (a :: (p ++ a :: s)) = 0 := by
  induction p with
  | nil => exact simplex_repeat_adjacent a s
  | cons b p ih =>
    rw [List.cons_append,simplex_swap_eq_neg]
    rw [← cons_simplex]
    rw [ih,map_zero,neg_zero]

theorem simplex_eq_zero_of_not_nodup (l : List V) (h : ¬l.Nodup) : simplex l = 0 := by
  induction l with
  | nil => exact (h List.nodup_nil).elim
  | cons a l ih =>
    by_cases ha : a ∈ l
    · obtain ⟨p,s,rfl⟩ := List.mem_iff_append.mp ha
      exact simplex_repeat a p s
    · have hl : ¬l.Nodup := fun hl => h (List.nodup_cons.mpr ⟨ha,hl⟩)
      rw [← cons_simplex]
      rw [ih hl,map_zero]

/-- Boundary membership can be checked on the codimension-one sublists. -/
theorem boundary_simplex_mem (S : Submodule ℚ (Chain V)) (l : List V)
    (h : ∀ m : List V, m.Sublist l → m.length + 1 = l.length → simplex m ∈ S) :
    boundary (simplex l) ∈ S := by
  induction l generalizing S with
  | nil => simp only [boundary_nil]; exact S.zero_mem
  | cons a l ih =>
    rw [boundary_cons]
    apply S.sub_mem
    · exact h l (List.sublist_cons_self a l) rfl
    · apply ih (S.comap (cons a))
      intro m hm hlen
      change cons a (simplex m) ∈ S
      rw [cons_simplex]
      exact h (a :: m) (hm.cons_cons a) (congrArg Nat.succ hlen)

/-- Empty augmented simplices or genuine nonempty faces of the given precomplex. -/
def Allowed (C : PreAbstractSimplicialComplex V) (l : List V) : Prop :=
  by classical exact l = [] ∨ l.toFinset ∈ C

theorem allowed_sublist (C : PreAbstractSimplicialComplex V) {l m : List V}
    (hl : Allowed C l) (hm : m.Sublist l) : Allowed C m := by
  classical
  by_cases he : m = []
  · exact Or.inl he
  · apply Or.inr
    rcases hl with rfl | hl
    · exact (he (List.sublist_nil.mp hm)).elim
    · exact (C.isRelLowerSet_faces hl).2
        (fun _ hx => List.mem_toFinset.mpr (hm.subset (List.mem_toFinset.mp hx))) ((List.toFinset_nonempty_iff m).mpr he)

/-- The actual finite oriented simplex-chain submodule. The index counts vertices;
index zero is the augmented degree minus one. -/
def chains (C : PreAbstractSimplicialComplex V) (n : ℕ) : Submodule ℚ (Chain V) :=
  Submodule.span ℚ {c | ∃ l : List V, l.length = n ∧ Allowed C l ∧ simplex l = c}

theorem simplex_mem_chains (C : PreAbstractSimplicialComplex V) (l : List V)
    (hl : Allowed C l) : simplex l ∈ chains C l.length :=
  Submodule.subset_span ⟨l,rfl,hl,rfl⟩

theorem boundary_mem_chains (C : PreAbstractSimplicialComplex V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C (n+1)) : boundary c ∈ chains C n := by
  change c ∈ (chains C n).comap boundary
  apply (Submodule.span_le.mpr ?_) hc
  rintro _ ⟨l,hlen,hl,rfl⟩
  change boundary (simplex l) ∈ chains C n
  apply boundary_simplex_mem
  intro m hm hmlen
  have hm_len : m.length = n := Nat.add_right_cancel (hmlen.trans hlen)
  simpa only [hm_len] using simplex_mem_chains C m (allowed_sublist C hl hm)

/-- The boundary restricted to actual finite simplex chains. -/
def differential (C : PreAbstractSimplicialComplex V) (n : ℕ) :
    chains C (n+1) →ₗ[ℚ] chains C n :=
  (boundary.comp (chains C (n+1)).subtype).codRestrict _
    (fun c => boundary_mem_chains C n c.property)

theorem differential_squared (C : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : chains C (n+2)) : differential C n (differential C (n+1) c) = 0 := by
  apply Subtype.ext
  exact boundary_squared c.val

/-- Inclusion of actual face sets induces inclusion of every chain submodule. -/
theorem chains_mono {C D : PreAbstractSimplicialComplex V} (h : C ≤ D) (n : ℕ) :
    chains C n ≤ chains D n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,hl,rfl⟩
  apply Submodule.subset_span
  exact ⟨l,hlen,hl.imp_right (fun hl => h hl),rfl⟩

end TernaryPoly.OrientedListChains
