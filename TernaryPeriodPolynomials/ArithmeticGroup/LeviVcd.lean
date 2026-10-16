module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.LeviCohomology
public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.Descent
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section


/-!
# Virtually free groups have rational cohomology vanishing above degree one

"The arithmetic Levi groups occurring here have free subgroups of finite index, so their rational cohomology vanishes above degree one."

* `isZero_of_H2_isZero`: if `H²(G, A) = 0` for every rational representation `A` of `G`, then `H^m(G, A) = 0` for every `m ≥ 2` and every `A`
  (dimension shifting along the coinduced module from the trivial subgroup, whose cohomology vanishes in positive degrees over `ℚ`).
* `VirtuallyFree G`: `G` has a free subgroup of finite index.  `VirtuallyFree.isZero`: for such `G`, `H^{n+2}(G, A) = 0` for all `n` and all `A : Rep ℚ G`
  (the degree-two case is the library's `VirtuallyFreeSecondCohomology.isZero_H2_of_isFreeGroup`: finite-index descent and the splitting of cocycle extensions of a free group).
* Closure properties: `VirtuallyFree.subgroup` (every subgroup of a virtually free group), `VirtuallyFree.prod_finite` (product with a finite group), finite groups.
* `levi_groups_virtuallyFree`: the Levi groups that occur -- `GL₂(ℤ)` (Levi of the bad plane), every subgroup of it, in particular `Γ₂`, `{±1} × Γ₂` (Levi of the bad line) and the diagonal sign
  groups -- are virtually free, hence `levi_cohomology_vanishes_above_one`: rational cohomology above degree one vanishes uniformly.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.LeviVcd

open CategoryTheory CategoryTheory.Limits TernaryPoly

section Abstract

variable {G : Type} [Group G]

/-- The unit of coinduction from the trivial subgroup is injective. -/
theorem coindUnit_bot_mono (A : Rep ℚ G) :
    Mono (RationalCohomologyDescent.coindUnit (⊥ : Subgroup G) A) := by
  rw [Rep.mono_iff_injective]
  intro v w h
  have e1 := RationalCohomologyDescent.coindUnit_apply (⊥ : Subgroup G) A v 1
  have e2 := RationalCohomologyDescent.coindUnit_apply (⊥ : Subgroup G) A w 1
  have : A.ρ 1 v = A.ρ 1 w := by
    rw [← e1, ← e2]
    exact congrArg (fun z => z.val 1) h
  simpa using this

/-- **Dimension shifting.**  If `H²(G, A) = 0` for all rational representations `A`, then `H^m(G, A) = 0` for all `m ≥ 2`. -/
theorem isZero_of_H2_isZero (h2 : ∀ A : Rep ℚ G, IsZero (groupCohomology A 2)) :
    ∀ (n : ℕ) (A : Rep ℚ G), IsZero (groupCohomology A (n + 2)) := by
  intro n
  induction n with
  | zero => exact h2
  | succ n ih =>
    intro A
    have := coindUnit_bot_mono A
    let f := RationalCohomologyDescent.coindUnit (⊥ : Subgroup G) A
    let S : ShortComplex (Rep ℚ G) := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance
    have hmid : IsZero (groupCohomology S.X₂ (n + 3)) := by
      have hb : IsZero (groupCohomology (Rep.res (⊥ : Subgroup G).subtype A) (n + 2 + 1)) :=
        RationalCohomologyDescent.finite_isZero _ (n + 2)
      exact hb.of_iso (groupCohomology.coindIso (Rep.res (⊥ : Subgroup G).subtype A) (n + 3))
    have := groupCohomology.epi_δ_of_isZero hS (n + 2) hmid
    exact (ih S.X₃).of_epi (groupCohomology.δ hS (n + 2) (n + 3) rfl)

end Abstract

/-- A group is *virtually free* if it has a free subgroup of finite index. -/
def VirtuallyFree (G : Type) [Group G] : Prop := ∃ H : Subgroup G, H.FiniteIndex ∧ IsFreeGroup H

namespace VirtuallyFree

/-- **Rational cohomology of a virtually free group vanishes above degree one**, for every rational representation. -/
theorem isZero {G : Type} [Group G] (h : VirtuallyFree G) (n : ℕ) (A : Rep ℚ G) :
    IsZero (groupCohomology A (n + 2)) := by
  obtain ⟨H, hfin, hfree⟩ := h
  exact isZero_of_H2_isZero (fun B => VirtuallyFreeSecondCohomology.isZero_H2_of_isFreeGroup H B) n A

theorem isZero_of_ge {G : Type} [Group G] (h : VirtuallyFree G) {m : ℕ} (hm : 2 ≤ m) (A : Rep ℚ G) :
    IsZero (groupCohomology A m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm]
  exact h.isZero n A

/-- A finite group is virtually free (its trivial subgroup is free of finite index). -/
theorem of_finite {G : Type} [Group G] [Finite G] : VirtuallyFree G := by
  have : IsFreeGroup (⊥ : Subgroup G) :=
    IsFreeGroup.ofMulEquiv (MulEquiv.ofUnique : FreeGroup Empty ≃* (⊥ : Subgroup G))
  exact ⟨⊥, inferInstance, inferInstance⟩

/-- **Every subgroup of a virtually free group is virtually free** (Nielsen-Schreier on the intersection with the free subgroup). -/
theorem subgroup {G : Type} [Group G] (h : VirtuallyFree G) (K : Subgroup G) : VirtuallyFree K := by
  obtain ⟨F, hfin, hfree⟩ := h
  have : IsFreeGroup (K.subgroupOf F) := inferInstance
  refine ⟨F.subgroupOf K, inferInstance, ?_⟩
  exact ((IsFreeGroup.basis (K.subgroupOf F)).map
    (RelativeLeviCohomology.intersectionEquiv K F)).isFreeGroup

/-- **Product with a finite group** (the sign factors of the Levi groups). -/
theorem prod_finite {A B : Type} [Group A] [Group B] [Finite B] (h : VirtuallyFree A) : VirtuallyFree (B × A) := by
  obtain ⟨F, hfin, hfree⟩ := h
  let P : Subgroup (B × A) := (⊥ : Subgroup B).prod F
  have : P.FiniteIndex := by
    constructor
    change ((⊥ : Subgroup B).prod F).index ≠ 0
    rw [Subgroup.index_prod]
    exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := (⊥ : Subgroup B)))
      (Subgroup.FiniteIndex.index_ne_zero (H := F))
  let e : F ≃* P :=
    { toFun := fun x => ⟨(1, x.val), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, x.property⟩⟩
      invFun := fun x => ⟨x.val.2, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Subtype.ext
        have hx : x.val.1 = 1 := x.property.1
        exact Prod.ext hx.symm rfl
      map_mul' := fun _ _ => by
        apply Subtype.ext
        exact Prod.ext (one_mul 1).symm rfl }
  exact ⟨P, inferInstance, ((IsFreeGroup.basis F).map e).isFreeGroup⟩

end VirtuallyFree

section Levi

open TernaryPoly.RelativeStabilizerParameters TernaryPoly.IntegralGL2Free

/-- `GL₂(ℤ)`, the Levi group of the bad plane, is virtually free. -/
theorem gl2_virtuallyFree : VirtuallyFree GL2 := ⟨generated, inferInstance, inferInstance⟩

/-- Every subgroup of `GL₂(ℤ)` is virtually free; in particular `Γ₂ = {D : (0,1) D ≡ (0,1) mod 3}`. -/
theorem subgroup_gl2_virtuallyFree (H : Subgroup GL2) : VirtuallyFree H := gl2_virtuallyFree.subgroup H

theorem gamma_virtuallyFree : VirtuallyFree Gamma := gl2_virtuallyFree.subgroup Gamma

/-- The Levi group `{±1} × Γ₂` of the bad line is virtually free. -/
theorem lineLevi_virtuallyFree : VirtuallyFree (ℤˣ × Gamma) := gamma_virtuallyFree.prod_finite

/-- **The arithmetic Levi groups that occur have rational cohomology vanishing above degree one**, uniformly:
`GL₂(ℤ)` (bad plane), every subgroup of it (e.g. `Γ₂`), `{±1} × Γ₂` (bad line), and the finite sign groups. -/
theorem levi_cohomology_vanishes_above_one :
    (∀ (n : ℕ) (A : Rep ℚ GL2), IsZero (groupCohomology A (n + 2))) ∧
    (∀ (H : Subgroup GL2) (n : ℕ) (A : Rep ℚ H), IsZero (groupCohomology A (n + 2))) ∧
    (∀ (n : ℕ) (A : Rep ℚ Gamma), IsZero (groupCohomology A (n + 2))) ∧
    (∀ (n : ℕ) (A : Rep ℚ (ℤˣ × Gamma)), IsZero (groupCohomology A (n + 2))) ∧
    (∀ (n : ℕ) (A : Rep ℚ (ℤˣ × ℤˣ)), IsZero (groupCohomology A (n + 2))) :=
  ⟨fun n A => gl2_virtuallyFree.isZero n A, fun H n A => (subgroup_gl2_virtuallyFree H).isZero n A,
    fun n A => gamma_virtuallyFree.isZero n A, fun n A => lineLevi_virtuallyFree.isZero n A,
    fun n A => VirtuallyFree.of_finite.isZero n A⟩

end Levi

end TernaryPeriodPolynomials.Argument.Identities.LeviVcd
