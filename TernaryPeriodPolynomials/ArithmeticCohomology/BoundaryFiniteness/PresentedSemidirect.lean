module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Abelianization.Defs
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
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.PresentedSemidirect

noncomputable section

variable {N H K : Type} [Group N] [Group H] [Group K]

theorem compatibility_of_generators (action : H →* MulAut N) (normalMap : N →* K) (groupMap : H →* K)
    (normalGenerators : Set N) (groupGenerators : Set H)
    (normal_generated : Subgroup.closure normalGenerators = ⊤)
    (group_generated : Subgroup.closure groupGenerators = ⊤)
    (compatible : ∀ group ∈ groupGenerators, ∀ normal ∈ normalGenerators,
      normalMap (action group normal) = groupMap group * normalMap normal * (groupMap group)⁻¹) :
    ∀ group, normalMap.comp (action group).toMonoidHom =
      (MulAut.conj (groupMap group)).toMonoidHom.comp normalMap := by
  have generators_compatible (group : H) (membership : group ∈ groupGenerators) :
      normalMap.comp (action group).toMonoidHom =
        (MulAut.conj (groupMap group)).toMonoidHom.comp normalMap :=
    MonoidHom.eq_of_eqOn_dense normal_generated (compatible group membership)
  intro group
  have membership : group ∈ Subgroup.closure groupGenerators := group_generated ▸ Subgroup.mem_top group
  induction membership using Subgroup.closure_induction with
  | mem group membership => exact generators_compatible group membership
  | one => ext normal; simp
  | mul left right _ _ left_compatible right_compatible =>
    ext normal
    have left_equation := congrArg (fun hom : N →* K => hom (action right normal)) left_compatible
    have right_equation := congrArg (fun hom : N →* K => hom normal) right_compatible
    change normalMap (action left (action right normal)) =
      groupMap left * normalMap (action right normal) * (groupMap left)⁻¹ at left_equation
    change normalMap (action right normal) = groupMap right * normalMap normal * (groupMap right)⁻¹ at right_equation
    change normalMap (action (left * right) normal) =
      groupMap (left * right) * normalMap normal * (groupMap (left * right))⁻¹
    simp only [map_mul, MulAut.mul_apply, mul_inv_rev]
    rw [left_equation, right_equation]
    simp only [mul_assoc]
  | inv group _ group_compatible =>
    ext normal
    have equation := congrArg (fun hom : N →* K => hom ((action group)⁻¹ normal)) group_compatible
    change normalMap (action group ((action group)⁻¹ normal)) =
      groupMap group * normalMap ((action group)⁻¹ normal) * (groupMap group)⁻¹ at equation
    simp only [MulAut.apply_inv_self] at equation
    have transformed := congrArg (fun value => (groupMap group)⁻¹ * value * groupMap group) equation
    change normalMap (action group⁻¹ normal) =
      groupMap group⁻¹ * normalMap normal * (groupMap group⁻¹)⁻¹
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using transformed.symm

def canonical (action : H →* MulAut N) : Monoid.Coprod N H →* N ⋊[action] H :=
  Monoid.Coprod.lift SemidirectProduct.inl SemidirectProduct.inr

theorem canonical_surjective (action : H →* MulAut N) : Function.Surjective (canonical action) := by
  intro element
  refine ⟨Monoid.Coprod.inl element.left * Monoid.Coprod.inr element.right, ?_⟩
  simp [canonical, SemidirectProduct.inl_left_mul_inr_right]

def relation (action : H →* MulAut N) (group : H) (normal : N) : Monoid.Coprod N H :=
  Monoid.Coprod.inr group * Monoid.Coprod.inl normal * (Monoid.Coprod.inr group)⁻¹ *
    (Monoid.Coprod.inl (action group normal))⁻¹

theorem relation_in_kernel (action : H →* MulAut N) (group : H) (normal : N) :
    relation action group normal ∈ (canonical action).ker := by
  change canonical action (relation action group normal) = 1
  simp only [canonical, relation, map_mul, map_inv]
  change SemidirectProduct.inr group * SemidirectProduct.inl normal * (SemidirectProduct.inr group)⁻¹ *
    (SemidirectProduct.inl (action group normal))⁻¹ = (1 : N ⋊[action] H)
  rw [← map_inv, ← SemidirectProduct.inl_aut, mul_inv_cancel]

def relations (action : H →* MulAut N) (normalGenerators : Set N) (groupGenerators : Set H) :
    Set (Monoid.Coprod N H) :=
  (fun pair : H × N => relation action pair.1 pair.2) '' (groupGenerators ×ˢ normalGenerators)

theorem relations_generate_kernel (action : H →* MulAut N) (normalGenerators : Set N) (groupGenerators : Set H)
    (normal_generated : Subgroup.closure normalGenerators = ⊤)
    (group_generated : Subgroup.closure groupGenerators = ⊤) :
    Subgroup.normalClosure (relations action normalGenerators groupGenerators) = (canonical action).ker := by
  let kernel := Subgroup.normalClosure (relations action normalGenerators groupGenerators)
  let quotient := QuotientGroup.mk' kernel
  let normalMap := quotient.comp (Monoid.Coprod.inl : N →* Monoid.Coprod N H)
  let groupMap := quotient.comp (Monoid.Coprod.inr : H →* Monoid.Coprod N H)
  have compatible : ∀ group, normalMap.comp (action group).toMonoidHom =
      (MulAut.conj (groupMap group)).toMonoidHom.comp normalMap := by
    apply compatibility_of_generators action normalMap groupMap normalGenerators groupGenerators normal_generated group_generated
    intro group group_mem normal normal_mem
    have membership : relation action group normal ∈ kernel :=
      Subgroup.subset_normalClosure ⟨(group, normal), ⟨group_mem, normal_mem⟩, rfl⟩
    have equation : quotient (relation action group normal) = 1 := (QuotientGroup.eq_one_iff _).mpr membership
    change quotient (Monoid.Coprod.inl (action group normal)) =
      quotient (Monoid.Coprod.inr group) * quotient (Monoid.Coprod.inl normal) *
        (quotient (Monoid.Coprod.inr group))⁻¹
    apply Eq.symm
    apply mul_inv_eq_one.mp
    simpa only [relation, map_mul, map_inv] using equation
  let inverse := SemidirectProduct.lift normalMap groupMap compatible
  have factorization : inverse.comp (canonical action) = quotient := by
    apply Monoid.Coprod.hom_ext
    · ext normal
      simp [canonical, inverse, normalMap]
    · ext group
      simp [canonical, inverse, groupMap]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨⟨group, normal⟩, _, rfl⟩
    exact relation_in_kernel action group normal
  · intro word membership
    have image : canonical action word = 1 := membership
    have equation := congrArg (fun hom : Monoid.Coprod N H →* (Monoid.Coprod N H ⧸ kernel) => hom word) factorization
    change inverse (canonical action word) = quotient word at equation
    rw [image, map_one] at equation
    exact (QuotientGroup.eq_one_iff _).mp equation.symm

theorem finitelyGenerated_of_presented (G : Type) [Group G] [Group.IsFinitelyPresented G] : Group.FG G := by
  obtain ⟨_, quotient, surjective, _⟩ := Group.IsFinitelyPresented.out (G := G)
  exact Group.fg_of_surjective surjective

theorem finitelyPresented (action : H →* MulAut N)
    [Group.IsFinitelyPresented N] [Group.IsFinitelyPresented H] : Group.IsFinitelyPresented (N ⋊[action] H) := by
  have normal_fg := finitelyGenerated_of_presented N
  have group_fg := finitelyGenerated_of_presented H
  obtain ⟨normalGenerators, normal_generated, normal_finite⟩ := Group.fg_iff.mp normal_fg
  obtain ⟨groupGenerators, group_generated, group_finite⟩ := Group.fg_iff.mp group_fg
  apply Group.IsFinitelyPresented.of_surjective (canonical action) (canonical_surjective action)
  refine ⟨relations action normalGenerators groupGenerators, ?_,
    relations_generate_kernel action normalGenerators groupGenerators normal_generated group_generated⟩
  exact (group_finite.prod normal_finite).image _

theorem product_finitelyPresented [Group.IsFinitelyPresented N] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (N × H) := by
  let := finitelyPresented (1 : H →* MulAut N)
  exact Group.IsFinitelyPresented.equiv SemidirectProduct.mulEquivProd

end

end TernaryPeriodPolynomials.BoundaryFiniteness.PresentedSemidirect
