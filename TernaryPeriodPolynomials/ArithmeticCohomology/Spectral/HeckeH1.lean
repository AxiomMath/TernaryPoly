module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Basic.Complex.Basic
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


/-!
# Hecke operators on first group cohomology

Let `G ⊆ 𝔾` (an injective homomorphism `embed`) and let `α_j` (`j` in a finite index type) be
representatives of finitely many right cosets `G α_j` which are permuted by right multiplication by
`G`: for `g ∈ G` and every `j` there is `next g j` with `α_j g α_{next g j}⁻¹ ∈ G`, and the cosets
are distinct. For a representation `ρ` of `𝔾` restricting to the `G`-representation `A`, the
formula
`(T c)(g) = ∑_j ρ(α_j)⁻¹ c(α_j g α_{next g j}⁻¹)`
sends one-cocycles to one-cocycles and coboundaries to coboundaries (`heckeCocycle`), hence acts on
`H¹(G, A)` (`heckeH1`). If a function `F : X → A` on a `𝔾`-set is a primitive of the cocycle `c`
(`c(g) = F(g x) - ρ(g) F(x)` for all `x`), then the trace `∑_j ρ(α_j)⁻¹ F(α_j x)` is a primitive of
`T c` (`heckeCocycle_primitive`); this is how the classical Hecke operator on cusp forms is compared
with `T` through period integrals.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open CategoryTheory

namespace TernaryPeriodPolynomials.Spectral.HeckeH1

variable {G 𝔾 : Type} [Group G] [Group 𝔾]

/-- Finitely many distinct right cosets `G α_j` of `G` in `𝔾`, permuted by right multiplication
by `G`. -/
structure RightCosets (embed : G →* 𝔾) where
  /-- The index type of the cosets. -/
  index : Type
  [fintype : Fintype index]
  /-- The coset representatives. -/
  rep : index → 𝔾
  /-- The coset of `α_j g` is `G α_{next g j}`. -/
  next : G → index → index
  /-- The element `α_j g α_{next g j}⁻¹` of `G`. -/
  delta : G → index → G
  delta_spec : ∀ g j, embed (delta g j) = rep j * embed g * (rep (next g j))⁻¹
  disjoint : ∀ i j (g : G), embed g = rep i * (rep j)⁻¹ → i = j

attribute [instance] RightCosets.fintype

namespace RightCosets

variable {embed : G →* 𝔾} (S : RightCosets embed)

theorem next_unique {g h : G} {j k : S.index}
    (spec : embed h = S.rep j * embed g * (S.rep k)⁻¹) : k = S.next g j := by
  apply S.disjoint k (S.next g j) (h⁻¹ * S.delta g j)
  rw [map_mul, map_inv, spec, S.delta_spec]
  group

theorem delta_unique (embedded : Function.Injective embed) {g h : G} {j : S.index}
    (spec : embed h = S.rep j * embed g * (S.rep (S.next g j))⁻¹) : h = S.delta g j := by
  apply embedded
  rw [spec, S.delta_spec]

theorem next_mul (g h : G) (j : S.index) :
    S.next (g * h) j = S.next h (S.next g j) := by
  symm
  apply S.next_unique (h := S.delta g j * S.delta h (S.next g j))
  rw [map_mul, S.delta_spec, S.delta_spec, map_mul]
  group

theorem delta_mul (embedded : Function.Injective embed) (g h : G) (j : S.index) :
    S.delta (g * h) j = S.delta g j * S.delta h (S.next g j) := by
  symm
  apply S.delta_unique embedded
  rw [map_mul, S.delta_spec, S.delta_spec, map_mul, S.next_mul]
  group

theorem next_injective (g : G) : Function.Injective (S.next g) := by
  intro i j heq
  apply S.disjoint i j (S.delta g i * (S.delta g j)⁻¹)
  rw [map_mul, map_inv, S.delta_spec, S.delta_spec, heq]
  group

theorem next_bijective (g : G) : Function.Bijective (S.next g) :=
  Finite.injective_iff_bijective.mp (S.next_injective g)

/-- Right multiplication by `g` as a permutation of the cosets. -/
def nextEquiv (g : G) : S.index ≃ S.index := Equiv.ofBijective _ (S.next_bijective g)

theorem rep_inv_delta (g : G) (j : S.index) :
    (S.rep j)⁻¹ * embed (S.delta g j) = embed g * (S.rep (S.next g j))⁻¹ := by
  rw [S.delta_spec]
  group

end RightCosets

variable {embed : G →* 𝔾} (S : RightCosets embed) (A : Rep.{0, 0, 0} ℂ G)
  (ρ : Representation ℂ 𝔾 A) (compat : ∀ g, A.ρ g = ρ (embed g))

/-- The Hecke formula on functions `G → A`. -/
def heckeFun (c : G → A) (g : G) : A :=
  ∑ j, ρ (S.rep j)⁻¹ (c (S.delta g j))

theorem heckeFun_apply (c : G → A) (g : G) :
    heckeFun S A ρ c g = ∑ j, ρ (S.rep j)⁻¹ (c (S.delta g j)) := rfl

theorem cocycle_add_apply (c d : groupCohomology.cocycles₁ A) (g : G) : (c + d) g = c g + d g := rfl

theorem cocycle_smul_apply (a : ℂ) (c : groupCohomology.cocycles₁ A) (g : G) :
    (a • c) g = a • c g := rfl

include compat in
theorem heckeFun_mem (embedded : Function.Injective embed) (c : groupCohomology.cocycles₁ A) :
    heckeFun S A ρ c ∈ groupCohomology.cocycles₁ A := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro g h
  have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.property
  simp only [groupCohomology.cocycles₁.val_eq_coe] at hc
  have key : ∀ j, ρ (S.rep j)⁻¹ (c (S.delta (g * h) j)) =
      ρ (embed g) (ρ (S.rep (S.next g j))⁻¹ (c (S.delta h (S.next g j)))) +
        ρ (S.rep j)⁻¹ (c (S.delta g j)) := by
    intro j
    rw [S.delta_mul embedded, hc, map_add, compat, ← Module.End.mul_apply, ← map_mul,
      S.rep_inv_delta, map_mul, Module.End.mul_apply]
  rw [heckeFun_apply, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    heckeFun_apply, heckeFun_apply, compat, map_sum]
  congr 1
  exact Equiv.sum_comp (S.nextEquiv g) (fun k => ρ (embed g) (ρ (S.rep k)⁻¹ (c (S.delta h k))))

/-- The Hecke operator on one-cocycles. -/
def heckeCocycle (embedded : Function.Injective embed) :
    groupCohomology.cocycles₁ A →ₗ[ℂ] groupCohomology.cocycles₁ A where
  toFun c := ⟨heckeFun S A ρ c, heckeFun_mem S A ρ compat embedded c⟩
  map_add' c d := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change heckeFun S A ρ (c + d) g = heckeFun S A ρ c g + heckeFun S A ρ d g
    simp only [heckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a c := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change heckeFun S A ρ (a • c) g = a • heckeFun S A ρ c g
    simp only [heckeFun_apply, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem heckeCocycle_apply (embedded : Function.Injective embed) (c : groupCohomology.cocycles₁ A)
    (g : G) : heckeCocycle S A ρ compat embedded c g = ∑ j, ρ (S.rep j)⁻¹ (c (S.delta g j)) := rfl

/-- The trace `∑_j ρ(α_j)⁻¹ w` of a vector. -/
def traceVector (w : A) : A := ∑ j, ρ (S.rep j)⁻¹ w

include compat in
theorem heckeFun_coboundary (w : A) (g : G) :
    heckeFun S A ρ (fun g => A.ρ g w - w) g =
      A.ρ g (traceVector S A ρ w) - traceVector S A ρ w := by
  have key : ∀ j, ρ (S.rep j)⁻¹ (A.ρ (S.delta g j) w - w) =
      ρ (embed g) (ρ (S.rep (S.next g j))⁻¹ w) - ρ (S.rep j)⁻¹ w := by
    intro j
    rw [map_sub, compat, ← Module.End.mul_apply, ← map_mul, S.rep_inv_delta, map_mul,
      Module.End.mul_apply]
  rw [heckeFun_apply, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib,
    traceVector, compat, map_sum]
  congr 1
  exact Equiv.sum_comp (S.nextEquiv g) (fun k => ρ (embed g) (ρ (S.rep k)⁻¹ w))

include compat in
theorem heckeCocycle_coboundary (embedded : Function.Injective embed)
    (c : groupCohomology.cocycles₁ A) (hc : ⇑c ∈ groupCohomology.coboundaries₁ A) :
    ⇑(heckeCocycle S A ρ compat embedded c) ∈ groupCohomology.coboundaries₁ A := by
  obtain ⟨w, hw⟩ := hc
  refine ⟨traceVector S A ρ w, ?_⟩
  funext g
  have hcg : c = fun g => A.ρ g w - w := by
    rw [← hw]
    rfl
  change A.ρ g (traceVector S A ρ w) - traceVector S A ρ w = heckeFun S A ρ c g
  rw [hcg, heckeFun_coboundary S A ρ compat]

theorem H1π_surjective : Function.Surjective (groupCohomology.H1π A) := by
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h z => exact ⟨z, rfl⟩

theorem heckeCocycle_ker (embedded : Function.Injective embed) :
    LinearMap.ker (groupCohomology.H1π A).hom ≤
      (LinearMap.ker (groupCohomology.H1π A).hom).comap (heckeCocycle S A ρ compat embedded) := by
  intro c hc
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  rw [LinearMap.mem_ker] at hc
  exact (groupCohomology.H1π_eq_zero_iff _).mpr
    (heckeCocycle_coboundary S A ρ compat embedded c ((groupCohomology.H1π_eq_zero_iff c).mp hc))

/-- The quotient presentation of `H¹`. -/
def H1Equiv :
    (groupCohomology.cocycles₁ A ⧸ LinearMap.ker (groupCohomology.H1π A).hom) ≃ₗ[ℂ]
      groupCohomology.H1 A :=
  LinearMap.quotKerEquivOfSurjective _ (H1π_surjective A)

/-- **The Hecke operator on `H¹(G, A)`.** -/
def heckeH1 (embedded : Function.Injective embed) : Module.End ℂ (groupCohomology.H1 A) :=
  (H1Equiv A).toLinearMap ∘ₗ
    ((LinearMap.ker (groupCohomology.H1π A).hom).mapQ _ (heckeCocycle S A ρ compat embedded)
      (heckeCocycle_ker S A ρ compat embedded)) ∘ₗ (H1Equiv A).symm.toLinearMap

theorem heckeH1_H1π (embedded : Function.Injective embed) (c : groupCohomology.cocycles₁ A) :
    heckeH1 S A ρ compat embedded (groupCohomology.H1π A c) =
      groupCohomology.H1π A (heckeCocycle S A ρ compat embedded c) := by
  have hsymm : (H1Equiv A).symm (groupCohomology.H1π A c) =
      Submodule.Quotient.mk (p := LinearMap.ker (groupCohomology.H1π A).hom) c := by
    apply (H1Equiv A).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [heckeH1, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hsymm,
    Submodule.mapQ_apply]
  rfl

section Primitive

variable {H X : Type} [Group H] [MulAction H X] (φ : 𝔾 →* H)

/-- The Hecke trace `∑_j ρ(α_j)⁻¹ F(α_j x)` of a function on a `𝔾`-set. -/
def traceFunction (F : X → A) (x : X) : A :=
  ∑ j, ρ (S.rep j)⁻¹ (F (φ (S.rep j) • x))

include compat in
/-- **Primitives.** If `F` is a primitive of `c`, the trace of `F` is a primitive of `T c`. -/
theorem heckeFun_primitive (c : G → A) (F : X → A)
    (primitive : ∀ g x, c g = F (φ (embed g) • x) - A.ρ g (F x)) (g : G) (x : X) :
    heckeFun S A ρ c g = traceFunction S A ρ φ F (φ (embed g) • x) -
      A.ρ g (traceFunction S A ρ φ F x) := by
  have key : ∀ j, ρ (S.rep j)⁻¹ (c (S.delta g j)) =
      ρ (S.rep j)⁻¹ (F (φ (S.rep j) • φ (embed g) • x)) -
        ρ (embed g) (ρ (S.rep (S.next g j))⁻¹ (F (φ (S.rep (S.next g j)) • x))) := by
    intro j
    have hpoint : φ (S.rep j) • φ (embed g) • x =
        φ (embed (S.delta g j)) • φ (S.rep (S.next g j)) • x := by
      rw [smul_smul, smul_smul, ← map_mul, ← map_mul, S.delta_spec, inv_mul_cancel_right]
    rw [primitive _ (φ (S.rep (S.next g j)) • x), hpoint, map_sub, compat,
      ← Module.End.mul_apply (ρ (S.rep j)⁻¹), ← map_mul, S.rep_inv_delta, map_mul,
      Module.End.mul_apply]
  rw [heckeFun_apply, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib,
    traceFunction, traceFunction, compat, map_sum]
  congr 1
  exact Equiv.sum_comp (S.nextEquiv g) (fun k => ρ (embed g) (ρ (S.rep k)⁻¹ (F (φ (S.rep k) • x))))

end Primitive

end TernaryPeriodPolynomials.Spectral.HeckeH1
