module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Irreducibility of cyclic spans in unitary representations

For a unitary representation `π` of a group `G` on a complex Hilbert space `H`, a subgroup `C`
and a function `χ : C → ℂ`, the `χ`-type subspace is the closed subspace of vectors on which
every `c ∈ C` acts by the scalar `χ c`.  Compressing `π g` to this subspace by the orthogonal
projection `P` gives operators `P ∘ π g ∘ P`; a subspace of the type subspace stable under all of
them is *compression-stable*, and a minimal nonzero one is *compression-simple*.

The main result, `cyclicSpan_irreducible`, says that the closed cyclic span of a nonzero vector
of a finite-dimensional compression-simple subspace is an irreducible closed subrepresentation.
We also show that every finite-dimensional compression-stable subspace of the type subspace is
spanned by its compression-simple subspaces (`eq_sSup_compressionSimple`).
-/

namespace TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility

open Submodule

open scoped InnerProductSpace

variable {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A representation on a complex inner product space is unitary when every group element acts
by a norm-preserving map. -/
class IsUnitary (π : Representation ℂ G H) : Prop where
  norm_map : ∀ g v, ‖π g v‖ = ‖v‖

section General

variable (π : Representation ℂ G H) [IsUnitary π]

/-- The action of a group element of a unitary representation, as a linear isometry. -/
def isometry (g : G) : H →ₗᵢ[ℂ] H where
  toLinearMap := π g
  norm_map' := IsUnitary.norm_map g

@[simp]
theorem isometry_apply (g : G) (v : H) : isometry π g v = π g v := rfl

/-- A unitary representation preserves inner products. -/
theorem inner_map_map (g : G) (u w : H) : ⟪π g u, π g w⟫_ℂ = ⟪u, w⟫_ℂ :=
  (isometry π g).inner_map_map u w

/-- The adjoint of `π g` is `π g⁻¹`. -/
theorem inner_map (g : G) (u w : H) : ⟪π g u, w⟫_ℂ = ⟪u, π g⁻¹ w⟫_ℂ := by
  rw [← inner_map_map π g⁻¹, Representation.inv_self_apply]

theorem continuous_apply (g : G) : Continuous (π g) :=
  (isometry π g).continuous

/-- A subspace is invariant when every group element maps it into itself. -/
def IsInvariant (W : Submodule ℂ H) : Prop :=
  ∀ g, ∀ v ∈ W, π g v ∈ W

variable {π} in
/-- The orthogonal complement of an invariant subspace is invariant. -/
theorem IsInvariant.orthogonal {W : Submodule ℂ H} (hW : IsInvariant π W) :
    IsInvariant π Wᗮ := by
  intro g v hv
  rw [mem_orthogonal]
  intro w hw
  rw [← inner_map_map π g⁻¹, Representation.inv_self_apply]
  exact inner_right_of_mem_orthogonal (hW g⁻¹ w hw) hv

/-- An orthogonal projection commutes with a linear map preserving both the subspace and its
orthogonal complement. -/
theorem starProjection_comm_of_mapsTo (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →ₗ[ℂ] H) (hK : ∀ v ∈ K, T v ∈ K) (hKo : ∀ v ∈ Kᗮ, T v ∈ Kᗮ) (x : H) :
    K.starProjection (T x) = T (K.starProjection x) := by
  apply eq_starProjection_of_mem_of_inner_eq_zero (hK _ (starProjection_apply_mem K x))
  intro w hw
  rw [← map_sub]
  exact inner_left_of_mem_orthogonal hw (hKo _ (sub_starProjection_mem_orthogonal x))

variable {π} in
/-- The orthogonal projection onto a closed invariant subspace commutes with the action. -/
theorem IsInvariant.starProjection_comm {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : IsInvariant π W) (g : G) (x : H) :
    W.starProjection (π g x) = π g (W.starProjection x) :=
  starProjection_comm_of_mapsTo W (π g) (hW g) (hW.orthogonal g) x

/-- Two orthogonal projections commute as soon as one of them maps the range of the other into
itself. -/
theorem starProjection_comm_of_le (K W : Submodule ℂ H) [K.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (hWK : ∀ v ∈ K, W.starProjection v ∈ K) (x : H) :
    K.starProjection (W.starProjection x) = W.starProjection (K.starProjection x) := by
  apply eq_starProjection_of_mem_of_inner_eq_zero (hWK _ (starProjection_apply_mem K x))
  intro w hw
  rw [← map_sub, inner_starProjection_left_eq_right]
  exact inner_left_of_mem_orthogonal (hWK w hw) (sub_starProjection_mem_orthogonal x)

/-- The closed cyclic span of a vector: the closure of the span of its orbit. -/
def cyclicSpan (v : H) : Submodule ℂ H :=
  (span ℂ (Set.range fun g => π g v)).topologicalClosure

omit [IsUnitary π] in
theorem isClosed_cyclicSpan (v : H) : IsClosed (cyclicSpan π v : Set H) :=
  isClosed_topologicalClosure _

omit [IsUnitary π] in
theorem mem_cyclicSpan_self (v : H) : v ∈ cyclicSpan π v := by
  refine le_topologicalClosure _ (subset_span ⟨1, ?_⟩)
  simp

omit [IsUnitary π] in
/-- The closed cyclic span of `v` is contained in every closed subspace containing the orbit
of `v`. -/
theorem cyclicSpan_le_of_forall {v : H} {W : Submodule ℂ H} (hW : IsClosed (W : Set H))
    (h : ∀ g, π g v ∈ W) : cyclicSpan π v ≤ W :=
  topologicalClosure_minimal _ (span_le.2 (Set.range_subset_iff.2 h)) hW

variable {π} in
omit [IsUnitary π] in
/-- The closed cyclic span of `v` is contained in every closed invariant subspace
containing `v`. -/
theorem IsInvariant.cyclicSpan_le {v : H} {W : Submodule ℂ H} (hinv : IsInvariant π W)
    (hW : IsClosed (W : Set H)) (hv : v ∈ W) : cyclicSpan π v ≤ W :=
  cyclicSpan_le_of_forall π hW fun g => hinv g v hv

/-- The closed cyclic span of a vector is invariant. -/
theorem isInvariant_cyclicSpan (v : H) : IsInvariant π (cyclicSpan π v) := by
  intro g
  have : cyclicSpan π v ≤ (cyclicSpan π v).comap (π g) := by
    refine topologicalClosure_minimal _ ?_
      ((isClosed_cyclicSpan π v).preimage (continuous_apply π g))
    refine span_le.2 (Set.range_subset_iff.2 fun h => ?_)
    refine le_topologicalClosure _ (subset_span ⟨g * h, ?_⟩)
    simp
  exact fun x hx => this hx

end General

section TypeSubspace

variable (π : Representation ℂ G H) (C : Subgroup G) (χ : C → ℂ)

/-- The `χ`-type subspace: vectors on which each `c ∈ C` acts by the scalar `χ c`. -/
def typeSubspace : Submodule ℂ H where
  carrier := {u | ∀ c : C, π c u = χ c • u}
  add_mem' {u w} hu hw c := by simp [hu c, hw c, smul_add]
  zero_mem' c := by simp
  smul_mem' a u hu c := by simp [hu c, smul_comm a]

theorem mem_typeSubspace {u : H} : u ∈ typeSubspace π C χ ↔ ∀ c : C, π c u = χ c • u :=
  Iff.rfl

variable [IsUnitary π]

theorem isClosed_typeSubspace : IsClosed (typeSubspace π C χ : Set H) := by
  have : (typeSubspace π C χ : Set H) = ⋂ c : C, {u | π c u = χ c • u} := by
    ext u
    simp [mem_typeSubspace]
  rw [this]
  exact isClosed_iInter fun c =>
    isClosed_eq (continuous_apply π c) (continuous_const_smul (χ c))

instance [CompleteSpace H] : (typeSubspace π C χ).HasOrthogonalProjection :=
  have := (isClosed_typeSubspace π C χ).completeSpace_coe
  HasOrthogonalProjection.ofCompleteSpace _

variable {π} in
/-- The orthogonal projection onto a closed invariant subspace preserves the type subspace. -/
theorem IsInvariant.starProjection_mem_typeSubspace {W : Submodule ℂ H}
    [W.HasOrthogonalProjection] (hW : IsInvariant π W) {u : H}
    (hu : u ∈ typeSubspace π C χ) : W.starProjection u ∈ typeSubspace π C χ := by
  intro c
  rw [← hW.starProjection_comm, hu c, map_smul]

variable [CompleteSpace H]

/-- The orthogonal projection onto the type subspace. -/
noncomputable abbrev typeProj : H →L[ℂ] H :=
  (typeSubspace π C χ).starProjection

variable {π} in
/-- The orthogonal projection onto a closed invariant subspace commutes with the projection
onto the type subspace. -/
theorem IsInvariant.typeProj_comm {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : IsInvariant π W) (x : H) :
    typeProj π C χ (W.starProjection x) = W.starProjection (typeProj π C χ x) :=
  starProjection_comm_of_le _ W (fun _ hu => hW.starProjection_mem_typeSubspace C χ hu) x

/-- A subspace `N` is compression-stable when `P (π g u) ∈ N` for all `g` and `u ∈ N`, where `P`
is the orthogonal projection onto the type subspace. -/
def CompressionStable (N : Submodule ℂ H) : Prop :=
  ∀ g, ∀ u ∈ N, typeProj π C χ (π g u) ∈ N

/-- A compression-simple subspace: a nonzero compression-stable subspace of the type subspace
whose only compression-stable subspaces are `⊥` and itself. -/
structure CompressionSimple (N : Submodule ℂ H) : Prop where
  ne_bot : N ≠ ⊥
  le_typeSubspace : N ≤ typeSubspace π C χ
  stable : CompressionStable π C χ N
  eq_bot_or_eq : ∀ N' ≤ N, CompressionStable π C χ N' → N' = ⊥ ∨ N' = N

/-- If `N ≤ S` are compression-stable subspaces of the type subspace, then the relative
orthogonal complement `Nᗮ ⊓ S` of `N` in `S` is compression-stable. -/
theorem compressionStable_orthogonal_inf {S N : Submodule ℂ H} (hS : S ≤ typeSubspace π C χ)
    (hSs : CompressionStable π C χ S) (hNS : N ≤ S) (hN : CompressionStable π C χ N) :
    CompressionStable π C χ (Nᗮ ⊓ S) := by
  intro g u hu
  refine mem_inf.2 ⟨?_, hSs g u hu.2⟩
  rw [mem_orthogonal]
  intro n hn
  have hPn : typeProj π C χ n = n := starProjection_eq_self_iff.2 (hS (hNS hn))
  have hPu : typeProj π C χ u = u := starProjection_eq_self_iff.2 (hS hu.2)
  rw [← inner_starProjection_left_eq_right, hPn, ← inv_inv g, ← inner_map, ← hPu,
    ← inner_starProjection_left_eq_right]
  exact inner_right_of_mem_orthogonal (hN g⁻¹ n hn) hu.1

/-- Main theorem: the closed cyclic span of a nonzero vector `v` of a finite-dimensional
compression-simple subspace is irreducible: every closed invariant subspace of it is `⊥` or the
whole cyclic span. -/
theorem cyclicSpan_irreducible {N : Submodule ℂ H} [FiniteDimensional ℂ N]
    (hN : CompressionSimple π C χ N) {v : H} (hvN : v ∈ N) (hv : v ≠ 0)
    {W : Submodule ℂ H} (hWc : IsClosed (W : Set H)) (hWv : W ≤ cyclicSpan π v)
    (hW : IsInvariant π W) : W = ⊥ ∨ W = cyclicSpan π v := by
  have := hWc.completeSpace_coe
  set Q := W.starProjection with hQ
  -- `P` maps the cyclic span into `N`.
  have hPcyc : ∀ x ∈ cyclicSpan π v, typeProj π C χ x ∈ N := by
    have : cyclicSpan π v ≤ N.comap (typeProj π C χ : H →ₗ[ℂ] H) :=
      cyclicSpan_le_of_forall π
        ((closed_of_finiteDimensional N).preimage (typeProj π C χ).continuous)
        fun g => hN.stable g v hvN
    exact fun x hx => this hx
  -- `Q` maps `N` into `N`.
  have hQN : ∀ u ∈ N, Q u ∈ N := by
    intro u hu
    have hT : Q u ∈ typeSubspace π C χ :=
      hW.starProjection_mem_typeSubspace C χ (hN.le_typeSubspace hu)
    rw [← starProjection_eq_self_iff.2 hT]
    exact hPcyc _ (hWv (starProjection_apply_mem W u))
  -- An eigenvalue of `Q` restricted to `N`.
  have : Nontrivial N := nontrivial_iff_ne_bot.2 hN.ne_bot
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((Q : H →ₗ[ℂ] H).restrict hQN)
  obtain ⟨x, hx, hx0⟩ := hc.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  let N' : Submodule ℂ H := N ⊓ LinearMap.ker ((Q : H →ₗ[ℂ] H) - c • LinearMap.id)
  have hmemN' : ∀ u, u ∈ N' ↔ u ∈ N ∧ Q u = c • u := by
    intro u
    simp [N', sub_eq_zero]
  have hN'stable : CompressionStable π C χ N' := by
    intro g u hu
    rw [hmemN'] at hu ⊢
    refine ⟨hN.stable g u hu.1, ?_⟩
    rw [← hW.typeProj_comm, hW.starProjection_comm, hu.2, map_smul, map_smul]
  have hN'eq : N' = N := by
    refine (hN.eq_bot_or_eq N' inf_le_left hN'stable).resolve_left fun h => hx0 ?_
    have : (x : H) ∈ N' := (hmemN' x).2 ⟨x.2, congrArg Subtype.val hx⟩
    rw [h, mem_bot] at this
    exact Subtype.ext this
  have hQv : Q v = c • v := ((hmemN' v).1 (hN'eq ▸ hvN)).2
  -- `Q` is idempotent, so `c = 0` or `c = 1`.
  have hcc : c * c = c := by
    have h1 : Q (Q v) = Q v := starProjection_eq_self_iff.2 (starProjection_apply_mem W v)
    rw [hQv, map_smul, hQv, smul_smul] at h1
    by_contra hne
    exact hv (smul_eq_zero.1 (by rw [sub_smul, h1, sub_self] : (c * c - c) • v = 0)
      |>.resolve_left (sub_ne_zero.2 hne))
  obtain rfl | rfl : c = 0 ∨ c = 1 := by
    have h : c * (c - 1) = 0 := by rw [mul_sub, hcc, mul_one, sub_self]
    exact (mul_eq_zero.1 h).imp id sub_eq_zero.1
  · left
    have hvW : v ∈ Wᗮ := by
      have := sub_starProjection_mem_orthogonal (K := W) v
      rwa [← hQ, hQv, zero_smul, sub_zero] at this
    have hle : W ≤ Wᗮ := hWv.trans (hW.orthogonal.cyclicSpan_le (isClosed_orthogonal W) hvW)
    rw [← inf_orthogonal_eq_bot W, inf_eq_left.2 hle]
  · right
    have hvW : v ∈ W := by
      rw [← starProjection_eq_self_iff, ← hQ, hQv, one_smul]
    exact le_antisymm hWv (hW.cyclicSpan_le hWc hvW)

/-- The irreducibility theorem stated for a compression-simple subspace of a
finite-dimensional compression-stable subspace of the type subspace. -/
theorem cyclicSpan_irreducible_of_le {S N : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hNS : N ≤ S) (hN : CompressionSimple π C χ N) {v : H} (hvN : v ∈ N) (hv : v ≠ 0)
    {W : Submodule ℂ H} (hWc : IsClosed (W : Set H)) (hWv : W ≤ cyclicSpan π v)
    (hW : IsInvariant π W) : W = ⊥ ∨ W = cyclicSpan π v :=
  have := Submodule.finiteDimensional_of_le hNS
  cyclicSpan_irreducible π C χ hN hvN hv hWc hWv hW

/-- The closed cyclic span `H_v` of a nonzero vector `v` of a finite-dimensional
compression-simple subspace is a nonzero closed invariant subspace with no closed invariant
subspaces other than `⊥` and itself. -/
theorem cyclicSpan_isIrreducible {N : Submodule ℂ H} [FiniteDimensional ℂ N]
    (hN : CompressionSimple π C χ N) {v : H} (hvN : v ∈ N) (hv : v ≠ 0) :
    cyclicSpan π v ≠ ⊥ ∧ IsClosed (cyclicSpan π v : Set H) ∧
      IsInvariant π (cyclicSpan π v) ∧
      ∀ W : Submodule ℂ H, IsClosed (W : Set H) → W ≤ cyclicSpan π v → IsInvariant π W →
        W = ⊥ ∨ W = cyclicSpan π v :=
  ⟨fun h => hv ((mem_bot ℂ).1 (h ▸ mem_cyclicSpan_self π v)), isClosed_cyclicSpan π v,
    isInvariant_cyclicSpan π v,
    fun _ hWc hWv hW => cyclicSpan_irreducible π C χ hN hvN hv hWc hWv hW⟩

/-- A nonzero finite-dimensional compression-stable subspace of the type subspace contains a
compression-simple subspace. -/
theorem exists_compressionSimple_le {S : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hS : S ≤ typeSubspace π C χ) (hSs : CompressionStable π C χ S) (hS0 : S ≠ ⊥) :
    ∃ N ≤ S, CompressionSimple π C χ N := by
  classical
  have hex : ∃ n, ∃ N ≤ S, CompressionStable π C χ N ∧ N ≠ ⊥ ∧ Module.finrank ℂ N = n :=
    ⟨_, S, le_rfl, hSs, hS0, rfl⟩
  obtain ⟨N, hNS, hNs, hN0, hNr⟩ := Nat.find_spec hex
  have := Submodule.finiteDimensional_of_le hNS
  refine ⟨N, hNS, hN0, hNS.trans hS, hNs, fun N' hN'N hN's => ?_⟩
  by_cases h : N' = ⊥
  · exact Or.inl h
  refine Or.inr (eq_of_le_of_finrank_le hN'N ?_)
  rw [hNr]
  exact Nat.find_min' hex ⟨N', hN'N.trans hNS, hN's, h, rfl⟩

/-- A finite-dimensional compression-stable subspace of the type subspace is the span of its
compression-simple subspaces. -/
theorem eq_sSup_compressionSimple {S : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hS : S ≤ typeSubspace π C χ) (hSs : CompressionStable π C χ S) :
    S = sSup {N | N ≤ S ∧ CompressionSimple π C χ N} := by
  refine le_antisymm ?_ (sSup_le fun N hN => hN.1)
  induction hn : Module.finrank ℂ S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hS0 : S = ⊥
    · rw [hS0]
      exact bot_le
    obtain ⟨N, hNS, hN⟩ := exists_compressionSimple_le π C χ hS hSs hS0
    have := Submodule.finiteDimensional_of_le hNS
    have hlt : Nᗮ ⊓ S < S := by
      refine lt_of_le_of_ne inf_le_right fun h => hN.ne_bot ?_
      have : N ≤ Nᗮ := hNS.trans (h ▸ inf_le_left)
      rw [← inf_orthogonal_eq_bot N, inf_eq_left.2 this]
    have := Submodule.finiteDimensional_of_le (inf_le_right : Nᗮ ⊓ S ≤ S)
    have hrest := ih _ (hn ▸ finrank_lt_finrank_of_lt hlt) (inf_le_right.trans hS)
      (compressionStable_orthogonal_inf π C χ hS hSs hNS hN.stable) rfl
    calc S = N ⊔ Nᗮ ⊓ S := (sup_orthogonal_inf_of_hasOrthogonalProjection hNS).symm
      _ ≤ _ := sup_le (le_sSup (show N ∈ {N | N ≤ S ∧ _} from ⟨hNS, hN⟩))
          (hrest.trans (sSup_le_sSup fun _ hN' => And.intro (hN'.1.trans inf_le_right) hN'.2))

/-- Every vector of a finite-dimensional compression-stable subspace of the type subspace is a
finite sum of vectors from compression-simple subspaces. -/
theorem exists_finset_compressionSimple {S : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hS : S ≤ typeSubspace π C χ) (hSs : CompressionStable π C χ S) {u : H} (hu : u ∈ S) :
    ∃ s : Finset (Submodule ℂ H), (∀ N ∈ s, N ≤ S ∧ CompressionSimple π C χ N) ∧
      u ∈ ⨆ N ∈ s, N := by
  rw [eq_sSup_compressionSimple π C χ hS hSs, mem_sSup_iff_exists_finset] at hu
  obtain ⟨s, hs, hus⟩ := hu
  exact ⟨s, fun N hN => hs hN, hus⟩

end TypeSubspace

end TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility
