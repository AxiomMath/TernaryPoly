module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCohomologyDescent
open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G]

/-- Genuine rational group cohomology of a finite group vanishes in every positive degree. -/
theorem finite_isZero [Finite G] (A : Rep ℚ G) (n : ℕ) :
    IsZero (groupCohomology A (n+1)) :=
  (isZero_Ext_succ_of_projective (Rep.trivial ℚ G ℚ) A n).of_iso
    (groupCohomologyIsoExt A (n+1))

variable (H : Subgroup G) [H.FiniteIndex] (A : Rep ℚ G)

abbrev RightCosets := Quotient (QuotientGroup.rightRel H)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

instance : Nonempty (RightCosets H) := ⟨Quotient.mk _ 1⟩

/-- The actual coinduction unit. -/
def coindUnit : A ⟶ Rep.coind H.subtype (Rep.res H.subtype A) :=
  Rep.resCoindToHom H.subtype A (Rep.res H.subtype A) (𝟙 _)

/-- The actual induction counit. -/
def indCounit : Rep.ind H.subtype (Rep.res H.subtype A) ⟶ A :=
  (Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)

omit [H.FiniteIndex] in
@[simp] theorem coindUnit_apply (v : A) (g : G) :
    ((coindUnit H A).hom v).val g = A.ρ g v := rfl

omit [H.FiniteIndex] in
theorem indCounit_mk (g : G) (v : A) :
    (indCounit H A).hom (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ g v)=
      A.ρ g⁻¹ v := by
  simp [indCounit,Rep.indResHomEquiv]

/-- Finite-index induction/coinduction identifies a genuine equivariant trace. -/
def coindTrace : Rep.coind H.subtype (Rep.res H.subtype A) ⟶ A := by
  classical
  exact (Rep.indCoindIso (Rep.res H.subtype A)).inv ≫ indCounit H A

/-- The trace of the coinduction unit is the exact number of right cosets. -/
theorem coindUnit_trace_apply (v : A) :
    (coindTrace H A).hom ((coindUnit H A).hom v)=
      (Nat.card (RightCosets H) : ℚ) • v := by
  classical
  change (indCounit H A).hom ((Rep.res H.subtype A).coindToInd ((coindUnit H A).hom v)) = _
  rw [Rep.coindToInd_apply,map_sum]
  trans ∑ _ : RightCosets H,v
  · apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with | h g =>
    rw [Quotient.liftOn_mk,indCounit_mk,coindUnit_apply]
    rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  · simp only [Finset.sum_const,Finset.card_univ,Nat.card_eq_fintype_card]
    exact (Nat.cast_smul_eq_nsmul ℚ (Fintype.card (RightCosets H)) v).symm

/-- The normalized trace splits the actual coinduction unit. -/
def coindRetraction : Rep.coind H.subtype (Rep.res H.subtype A) ⟶ A :=
  (Nat.card (RightCosets H) : ℚ)⁻¹ • coindTrace H A

theorem coindUnit_retraction : coindUnit H A ≫ coindRetraction H A = 𝟙 A := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change (Nat.card (RightCosets H) : ℚ)⁻¹ • (coindTrace H A).hom ((coindUnit H A).hom v)=v
  rw [coindUnit_trace_apply,smul_smul,inv_mul_cancel₀,one_smul]
  exact_mod_cast (Nat.card_pos (α := RightCosets H)).ne'

/-- Vanishing on an actual finite-index subgroup implies vanishing for the full rational group. -/
theorem finiteIndex_isZero (n : ℕ)
    (h : IsZero (groupCohomology (Rep.res H.subtype A) n)) :
    IsZero (groupCohomology A n) := by
  have hc : IsZero (groupCohomology (Rep.coind H.subtype (Rep.res H.subtype A)) n) :=
    h.of_iso (groupCohomology.coindIso (Rep.res H.subtype A) n)
  have hm : groupCohomology.map (MonoidHom.id G) (coindUnit H A) n=0 := hc.eq_of_tgt _ _
  have he := congrArg (fun f => groupCohomology.map (MonoidHom.id G) f n)
    (coindUnit_retraction H A)
  rw [groupCohomology.map_id_comp,groupCohomology.map_id,hm,zero_comp] at he
  exact (IsZero.iff_id_eq_zero _).mpr he.symm

end TernaryPoly.RationalCohomologyDescent
