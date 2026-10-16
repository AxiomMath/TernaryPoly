module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.ModThreeGoodAction

abbrev IntegralVector := Fin 3 → ℤ
abbrev Space := Fin 3 → ℚ
abbrev RationalSubspace := Submodule ℚ Space
abbrev IntegralGL := Matrix.GeneralLinearGroup (Fin 3) ℤ

def fixedRow : Fin 3 → ZMod 3 := fun _ => 1

def reduction : IntegralGL →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3))

/-- The actual congruence subgroup fixing the row `(1,1,1)` modulo three. -/
def K : Subgroup IntegralGL where
  carrier := {g | Matrix.vecMul fixedRow (reduction g).val = fixedRow}
  one_mem' := by simp
  mul_mem' hg hh := by
    change Matrix.vecMul fixedRow (reduction (_*_)).val = fixedRow
    rw [map_mul,Units.val_mul,← Matrix.vecMul_vecMul,hg,hh]
  inv_mem' := by
    intro g hg
    have h := congrArg (fun row => Matrix.vecMul row (reduction g⁻¹).val) hg
    rw [Matrix.vecMul_vecMul] at h
    have he : (reduction g).val * (reduction g⁻¹).val = 1 := by
      rw [← Units.val_mul,← map_mul, mul_inv_cancel,map_one,Units.val_one]
    rw [he,Matrix.vecMul_one] at h
    exact h.symm

@[simp] theorem mem_K (g : IntegralGL) :
    g ∈ K ↔ Matrix.vecMul fixedRow (reduction g).val = fixedRow := Iff.rfl

/-- Integer vectors embedded in rational three-space. -/
def rationalVector (v : IntegralVector) : Space := fun i => (v i : ℚ)

def residueVector (v : IntegralVector) : Fin 3 → ZMod 3 := fun i => (v i : ZMod 3)

/-- Goodness is existence in the full integral lattice of a vector with nonzero row residue. -/
def Good (L : RationalSubspace) : Prop :=
  ∃ v : IntegralVector, rationalVector v ∈ L ∧ ∑ i, (v i : ZMod 3) ≠ 0

/-- The rational representation induced by coefficient extension of the genuine integer matrix. -/
def rationalRepresentation : IntegralGL →* (Space ≃ₗ[ℚ] Space) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Space).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ))

theorem rationalRepresentation_apply (g : IntegralGL) (v : Space) :
    rationalRepresentation g v =
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g).val.mulVec v := by
  change (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)).toLinearEquiv v = _
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,Matrix.GeneralLinearGroup.toLin_apply]
  rfl

/-- The actual integral matrix produces the witness after applying the rational action. -/
theorem rationalVector_mulVec (g : IntegralGL) (v : IntegralVector) :
    rationalVector (g.val.mulVec v) = rationalRepresentation g (rationalVector v) := by
  rw [rationalRepresentation_apply]
  funext i
  simp [rationalVector,Matrix.mulVec,dotProduct,Matrix.GeneralLinearGroup.map_apply]

theorem residueVector_mulVec (g : IntegralGL) (v : IntegralVector) :
    residueVector (g.val.mulVec v) = (reduction g).val.mulVec (residueVector v) := by
  funext i
  simp [residueVector,reduction,Matrix.mulVec,dotProduct,Matrix.GeneralLinearGroup.map_apply]

/-- The fixed row makes the residue of the coordinate sum invariant. -/
theorem coordinate_sum_invariant (g : K) (v : IntegralVector) :
    (∑ i, (g.1.val.mulVec v i : ZMod 3)) =
      ∑ i, (v i : ZMod 3) := by
  have h := Matrix.dotProduct_mulVec fixedRow (reduction g.1).val (residueVector v)
  rw [g.2] at h
  rw [← residueVector_mulVec] at h
  simpa [dotProduct,fixedRow,residueVector] using h

/-- Image of a rational subspace under the actual linear equivalence. -/
def act (g : K) (L : RationalSubspace) : RationalSubspace :=
  L.map (rationalRepresentation g.1).toLinearMap

theorem act_one (L : RationalSubspace) : act 1 L = L := by
  simp [act]

theorem act_mul (g h : K) (L : RationalSubspace) : act (g*h) L = act g (act h L) := by
  simpa only [act,Subgroup.coe_mul,map_mul,LinearEquiv.coe_toLinearMap_mul,Module.End.mul_eq_comp] using
    (Submodule.map_comp (rationalRepresentation h.1).toLinearMap
      (rationalRepresentation g.1).toLinearMap L)

theorem act_inv_act (g : K) (L : RationalSubspace) : act g⁻¹ (act g L) = L := by
  rw [← act_mul,inv_mul_cancel,act_one]

instance subspaceMulAction : MulAction K RationalSubspace where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

instance vectorMulAction : MulAction K Space where
  smul g v := rationalRepresentation g.1 v
  one_smul v := by
    change rationalRepresentation (1 : IntegralGL) v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change rationalRepresentation (g.1*h.1) v = rationalRepresentation g.1 (rationalRepresentation h.1 v)
    rw [map_mul,LinearEquiv.mul_apply]

/-- Goodness is preserved by acting on its integral witness. -/
theorem Good.act {L : RationalSubspace} (hL : Good L) (g : K) : Good (act g L) := by
  obtain ⟨v,hv,hs⟩ := hL
  refine ⟨g.1.val.mulVec v, ?_, ?_⟩
  · rw [rationalVector_mulVec]
    exact Submodule.mem_map_of_mem hv
  · rwa [coordinate_sum_invariant]

/-- The inverse matrix gives the converse, so the action preserves goodness exactly. -/
theorem good_act_iff (g : K) (L : RationalSubspace) : Good (act g L) ↔ Good L := by
  constructor
  · intro h
    have hi := h.act g⁻¹
    rwa [act_inv_act] at hi
  · exact fun h => h.act g

theorem Good.mono {L M : RationalSubspace} (h : L ≤ M) : Good L → Good M := by
  rintro ⟨v,hv,hs⟩
  exact ⟨v,h hv,hs⟩

/-- A good integral witness is nonzero in rational three-space. -/
theorem rationalVector_ne_zero {v : IntegralVector} (hv : ∑ i, (v i : ZMod 3) ≠ 0) :
    rationalVector v ≠ 0 := by
  intro h
  have he (i : Fin 3) : v i = 0 := by
    have hi : (v i : ℚ) = 0 := congrFun h i
    exact_mod_cast hi
  simp [he] at hv

/-- In particular for planes, goodness is equivalent to containing a one-dimensional good subspace. -/
theorem good_iff_contains_good_line (L : RationalSubspace) :
    Good L ↔ ∃ ell : RationalSubspace, Module.finrank ℚ ell = 1 ∧ Good ell ∧ ell ≤ L := by
  constructor
  · rintro ⟨v,hv,hs⟩
    refine ⟨Submodule.span ℚ {rationalVector v},finrank_span_singleton (rationalVector_ne_zero hs),?_,?_⟩
    · exact ⟨v,Submodule.subset_span (Set.mem_singleton _),hs⟩
    · exact Submodule.span_le.mpr (by intro w hw; rcases hw with rfl; exact hv)
  · rintro ⟨ell,_,hg,hle⟩
    exact hg.mono hle

/-- The first standard coordinate vector is a concrete good integral vector. -/
def firstIntegralVector : IntegralVector := ![1,0,0]

def firstLine : RationalSubspace := Submodule.span ℚ {rationalVector firstIntegralVector}

theorem firstLine_good : Good firstLine := by
  refine ⟨firstIntegralVector,Submodule.subset_span (Set.mem_singleton _),?_⟩
  norm_num only [firstIntegralVector,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Int.cast_one,Int.cast_zero,add_zero]
  exact one_ne_zero

theorem firstLine_finrank : Module.finrank ℚ firstLine = 1 := by
  apply finrank_span_singleton
  apply rationalVector_ne_zero
  norm_num only [firstIntegralVector,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Int.cast_one,Int.cast_zero,add_zero]
  exact one_ne_zero

theorem exists_good_line : ∃ L : RationalSubspace, Module.finrank ℚ L = 1 ∧ Good L :=
  ⟨firstLine,firstLine_finrank,firstLine_good⟩

/-- The genuine equivalence preserves dimensions as well as the lattice condition. -/
theorem act_finrank (g : K) (L : RationalSubspace) : Module.finrank ℚ (act g L) = Module.finrank ℚ L :=
  (rationalRepresentation g.1).submoduleMap L |>.finrank_eq.symm

theorem act_mono (g : K) {L M : RationalSubspace} (h : L ≤ M) : act g L ≤ act g M :=
  Submodule.map_mono h

theorem act_le_act_iff (g : K) (L M : RationalSubspace) : act g L ≤ act g M ↔ L ≤ M := by
  constructor
  · intro h
    have hi := act_mono g⁻¹ h
    simpa only [act_inv_act] using hi
  · exact act_mono g

theorem act_lt_act_iff (g : K) (L M : RationalSubspace) : act g L < act g M ↔ L < M := by
  simp only [lt_iff_le_not_ge,act_le_act_iff]

end TernaryPoly.ModThreeGoodAction
