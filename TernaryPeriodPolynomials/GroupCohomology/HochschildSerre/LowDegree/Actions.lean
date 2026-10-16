module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)

abbrev G := N ⋊[φ] Q
abbrev nIn : N →* G φ := SemidirectProduct.inl
abbrev qIn : Q →* G φ := SemidirectProduct.inr

variable (A : Rep ℚ (G φ))
abbrev radicalRep : Rep ℚ N := Rep.res (nIn φ) A

/-- The coefficient map for actual inverse conjugation by a quotient-group element. -/
def coefficientHom (q : Q) :
    Rep.res (φ q⁻¹).toMonoidHom (radicalRep φ A) ⟶ radicalRep φ A :=
  Rep.ofHom ⟨A.ρ (qIn φ q), fun n => by
    change A.ρ (qIn φ q) * A.ρ (nIn φ (φ q⁻¹ n)) =
      A.ρ (nIn φ n) * A.ρ (qIn φ q)
    rw [← map_mul, ← map_mul]
    congr 1
    rw [SemidirectProduct.inl_aut]
    simp [mul_assoc]⟩

/-- Actual inverse-conjugation pullback and coefficient action on inhomogeneous N-cochains. -/
def cochainsAction (q : Q) :
    groupCohomology.inhomogeneousCochains (radicalRep φ A) ⟶
      groupCohomology.inhomogeneousCochains (radicalRep φ A) :=
  groupCohomology.cochainsMap (φ q⁻¹).toMonoidHom (coefficientHom φ A q)

@[simp] theorem cochainsAction_apply (q : Q) (k : ℕ) (c : (Fin k → N) → A) (g : Fin k → N) :
    (cochainsAction φ A q).f k c g = A.ρ (qIn φ q) (c (fun i => φ q⁻¹ (g i))) := rfl

theorem cochainsAction_one : cochainsAction φ A 1 = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext g
  change A.ρ (qIn φ 1) (c (fun i => φ (1 : Q)⁻¹ (g i))) = c g
  simp

/-- Composition order matches the genuine left action on cochains. -/
theorem cochainsAction_mul (q r : Q) :
    cochainsAction φ A (q*r) = cochainsAction φ A r ≫ cochainsAction φ A q := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext g
  change A.ρ (qIn φ (q*r)) (c (fun i => φ (q*r)⁻¹ (g i))) =
    A.ρ (qIn φ q) (A.ρ (qIn φ r) (c (fun i => φ r⁻¹ (φ q⁻¹ (g i)))))
  simp [mul_inv_rev]

/-- The actual quotient-group action on every N-cohomology group. -/
def cohomologyAction (k : ℕ) : Q →* Module.End ℚ (groupCohomology (radicalRep φ A) k) where
  toFun q := (groupCohomology.map (φ q⁻¹).toMonoidHom (coefficientHom φ A q) k).hom
  map_one' := by
    change (HomologicalComplex.homologyMap (cochainsAction φ A 1) k).hom = LinearMap.id
    rw [cochainsAction_one, HomologicalComplex.homologyMap_id]
    rfl
  map_mul' q r := by
    change (HomologicalComplex.homologyMap (cochainsAction φ A (q*r)) k).hom = _
    rw [cochainsAction_mul, HomologicalComplex.homologyMap_comp]
    rfl

/-- Genuine Hᵏ(N,A) as a Q-representation. -/
abbrev cohomologyRep (k : ℕ) : Rep ℚ Q := Rep.of (cohomologyAction φ A k)

@[simp] theorem cohomologyRep_apply (k : ℕ) (q : Q)
    (v : groupCohomology (radicalRep φ A) k) :
    (cohomologyRep φ A k).ρ q v =
      groupCohomology.map (φ q⁻¹).toMonoidHom (coefficientHom φ A q) k v := rfl

/-- A genuine N-invariant vector remains invariant after the quotient coefficient action. -/
theorem invariants_stable (q : Q) (v : (radicalRep φ A).ρ.invariants) :
    A.ρ (qIn φ q) v ∈ (radicalRep φ A).ρ.invariants := by
  rw [Representation.mem_invariants]
  intro n
  have h := Rep.hom_comm_apply (coefficientHom φ A q) n (v : A)
  change A.ρ (qIn φ q) (A.ρ (nIn φ (φ q⁻¹ n)) v) =
    A.ρ (nIn φ n) (A.ρ (qIn φ q) v) at h
  have hv := (Representation.mem_invariants _ _).mp v.property (φ q⁻¹ n)
  change A.ρ (nIn φ (φ q⁻¹ n)) v = v at hv
  rw [hv] at h
  exact h.symm

def invariantsLinearAction (q : Q) :
    (radicalRep φ A).ρ.invariants →ₗ[ℚ] (radicalRep φ A).ρ.invariants where
  toFun v := ⟨A.ρ (qIn φ q) v, invariants_stable φ A q v⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The actual Q representation A^N, with no transported or postulated action. -/
abbrev invariantsRep : Rep ℚ Q := Rep.of {
  toFun := invariantsLinearAction φ A
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change A.ρ (qIn φ 1) v = v
    simp
  map_mul' := fun q r => by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change A.ρ (qIn φ (q*r)) v = A.ρ (qIn φ q) (A.ρ (qIn φ r) v)
    simp }

@[simp] theorem invariantsRep_apply (q : Q) (v : (radicalRep φ A).ρ.invariants) :
    ((invariantsRep φ A).ρ q v : (radicalRep φ A).ρ.invariants).val =
      A.ρ (qIn φ q) (v : A) := rfl

/-- Literal induced action on N one-cocycles. -/
def cocyclesOneAction (q : Q) (c : groupCohomology.cocycles₁ (radicalRep φ A)) :
    groupCohomology.cocycles₁ (radicalRep φ A) :=
  groupCohomology.mapCocycles₁ (φ q⁻¹).toMonoidHom (coefficientHom φ A q) c

@[simp] theorem cocyclesOneAction_apply (q : Q) (c : groupCohomology.cocycles₁ (radicalRep φ A))
    (n : N) : cocyclesOneAction φ A q c n = A.ρ (qIn φ q) (c (φ q⁻¹ n)) := rfl

@[simp] theorem H1π_action (q : Q) (c : groupCohomology.cocycles₁ (radicalRep φ A)) :
    (cohomologyRep φ A 1).ρ q (groupCohomology.H1π (radicalRep φ A) c) =
      groupCohomology.H1π (radicalRep φ A) (cocyclesOneAction φ A q c) :=
  groupCohomology.H1π_comp_map_apply _ _ _

end TernaryPoly.LowDegreeHochschildSerre
