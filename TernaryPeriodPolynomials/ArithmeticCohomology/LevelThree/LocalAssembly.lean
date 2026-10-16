module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
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
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Peel

@[expose] public section


/-!
# Linear algebra of the local Hecke operators at a cusp

At each cusp the local Hecke operator `T` of an away-from-three correspondence is upper
triangular with respect to the subspace `K` of classes with vanishing radical restriction: it acts
on the quotient by a scalar `λ` (`T y - λ y ∈ K` for every `y`), and on `K` it is intertwined by an
injective edge map `E : K → H` with `α + β S` for a Hecke operator `S` of the Levi quotient. This
file records the two consequences used for the local joint generalized eigenspaces:

* `maxGenEigenspace_le_of_sub_mem` : a generalized eigenvector for an eigenvalue `c ≠ λ` lies in
  `K`;
* `edge_mem_maxGenEigenspace` : the edge map sends a generalized `c`-eigenvector in `K` to a
  generalized `(c - α)/β`-eigenvector of `S`;
* `finrank_maxGenEigenspace_le` : hence the generalized `c`-eigenspace of `T` has dimension at most
  that of the generalized `(c - α)/β`-eigenspace of `S`, and the joint version
  `finrank_iInf_le`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.LevelThree.LocalAssembly

open Module

variable {M H : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H]

/-- If `T` acts on `M ⧸ K` by the scalar `λ`, then `K` is `T`-stable. -/
theorem map_mem_of_sub_mem (T : Module.End ℂ M) (K : Submodule ℂ M) (lam : ℂ)
    (sub_mem : ∀ y, T y - lam • y ∈ K) {y : M} (hy : y ∈ K) : T y ∈ K := by
  have h := K.add_mem (sub_mem y) (K.smul_mem lam hy)
  rwa [sub_add_cancel] at h

theorem pow_map_mem (T : Module.End ℂ M) (K : Submodule ℂ M) (lam c : ℂ)
    (sub_mem : ∀ y, T y - lam • y ∈ K) (k : ℕ) {z : M} (hz : z ∈ K) :
    ((T - c • 1) ^ k) z ∈ K := by
  induction k generalizing z with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact K.sub_mem (map_mem_of_sub_mem T K lam sub_mem hz) (K.smul_mem c hz)

theorem sub_smul_pow_sub_mem (T : Module.End ℂ M) (K : Submodule ℂ M) (lam c : ℂ)
    (sub_mem : ∀ y, T y - lam • y ∈ K) (k : ℕ) (y : M) :
    ((T - c • 1) ^ k) y - (lam - c) ^ k • y ∈ K := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have hstep : (T - c • 1) y - (lam - c) • y ∈ K := by
      have : (T - c • 1) y - (lam - c) • y = T y - lam • y := by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
        abel
      rw [this]
      exact sub_mem y
    have h1 := pow_map_mem T K lam c sub_mem k hstep
    have h2 := K.smul_mem (lam - c) (ih y)
    have e : ((T - c • 1) ^ (k + 1)) y - (lam - c) ^ (k + 1) • y =
        ((T - c • 1) ^ k) ((T - c • 1) y - (lam - c) • y) +
          (lam - c) • (((T - c • 1) ^ k) y - (lam - c) ^ k • y) := by
      rw [pow_succ, Module.End.mul_apply, map_sub, map_smul, smul_sub, smul_smul, pow_succ,
        mul_comm (lam - c) ((lam - c) ^ k)]
      abel
    rw [e]
    exact K.add_mem h1 h2

/-- **Complement.** If `T` acts on `M ⧸ K` by `λ` and `c ≠ λ`, every generalized `c`-eigenvector
of `T` lies in `K`. -/
theorem maxGenEigenspace_le_of_sub_mem (T : Module.End ℂ M) (K : Submodule ℂ M) (lam c : ℂ)
    (sub_mem : ∀ y, T y - lam • y ∈ K) (hne : c ≠ lam) :
    T.maxGenEigenspace c ≤ K := by
  intro y hy
  rw [Module.End.mem_maxGenEigenspace] at hy
  obtain ⟨k, hk⟩ := hy
  have h := sub_smul_pow_sub_mem T K lam c sub_mem k y
  rw [hk, zero_sub, neg_mem_iff] at h
  have hne' : (lam - c) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hne))
  have := K.smul_mem ((lam - c) ^ k)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this

section Polynomial

open Polynomial

/-- **Complement, polynomial form.** If `K` is `T`-stable and a polynomial `P` with `P(c) ≠ 0`
maps every vector into `K` (`T` acts on `M ⧸ K` with eigenvalues among the roots of `P`), then
every generalized `c`-eigenvector of `T` lies in `K`. -/
theorem maxGenEigenspace_le_of_aeval_mem (T : Module.End ℂ M) (K : Submodule ℂ M)
    (stable : ∀ y ∈ K, T y ∈ K) (P : ℂ[X]) (aeval_mem : ∀ y, aeval T P y ∈ K) (c : ℂ)
    (hc : P.eval c ≠ 0) : T.maxGenEigenspace c ≤ K := by
  intro y hy
  rw [Module.End.mem_maxGenEigenspace] at hy
  obtain ⟨k, hk⟩ := hy
  have hcop : IsCoprime ((X - C c) ^ k) P := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C c).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hc
  obtain ⟨A, B, hAB⟩ := hcop
  have hstable : ∀ (Q : ℂ[X]) z, z ∈ K → aeval T Q z ∈ K := by
    intro Q z hz
    induction Q using Polynomial.induction_on' with
    | add Q R hQ hR => rw [map_add, LinearMap.add_apply]; exact K.add_mem hQ hR
    | monomial j a =>
      rw [aeval_monomial, Module.End.mul_apply, algebraMap_end_apply]
      apply K.smul_mem
      induction j with
      | zero => simpa using hz
      | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact stable _ ih
  have hy : y = aeval T A (aeval T ((X - C c) ^ k) y) + aeval T B (aeval T P y) := by
    have := congrArg (fun Q => aeval T Q y) hAB
    simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply] at this
    exact this.symm
  have hzero : aeval T ((X - C c) ^ k) y = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C, algebraMap_end_eq_smul_id]
    exact hk
  rw [hy, hzero, map_zero, zero_add]
  exact hstable B _ (aeval_mem y)

end Polynomial

section Edge

variable (T : Module.End ℂ M) (K : Submodule ℂ M) (S : Module.End ℂ H) (E : K →ₗ[ℂ] H)
  (α β : ℂ)

/-- `E ((T - c)^k y) = β^k (S - (c - α)/β)^k (E y)` along an intertwining
`E (T y) = α E y + β S (E y)` on a `T`-stable subspace. -/
theorem edge_pow (stable : ∀ y ∈ K, T y ∈ K)
    (intertwine : ∀ y : K, E ⟨T y, stable y y.property⟩ = α • E y + β • S (E y))
    (hβ : β ≠ 0) (c : ℂ) (k : ℕ) (y : K) (hk : ∀ j ≤ k, ((T - c • 1) ^ j) y.val ∈ K) :
    E ⟨((T - c • 1) ^ k) y, hk k le_rfl⟩ = β ^ k • ((S - ((c - α) / β) • 1) ^ k) (E y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun j hj => hk j (Nat.le_succ_of_le hj))
    have hmem : ((T - c • 1) ^ k) y.val ∈ K := hk k (Nat.le_succ k)
    have hsplit : (⟨((T - c • 1) ^ (k + 1)) y, hk (k + 1) le_rfl⟩ : K) =
        ⟨T (((T - c • 1) ^ k) y), stable _ hmem⟩ - c • ⟨((T - c • 1) ^ k) y, hmem⟩ := by
      apply Subtype.ext
      simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul]
    have hpow : ((S - ((c - α) / β) • 1) ^ (k + 1)) (E y) =
        (S - ((c - α) / β) • 1) (((S - ((c - α) / β) • 1) ^ k) (E y)) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hsplit, map_sub, map_smul, intertwine ⟨_, hmem⟩, hprev, hpow]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      smul_sub, smul_smul]
    have hβ' : β ^ (k + 1) * ((c - α) / β) = (c - α) * β ^ k := by
      rw [pow_succ]
      field_simp
    rw [hβ', pow_succ, mul_comm (β ^ k) β, sub_mul, sub_smul]
    module

/-- **Edge.** The edge map sends generalized `c`-eigenvectors of `T` lying in `K` to generalized
`(c - α)/β`-eigenvectors of `S`. -/
theorem edge_mem_maxGenEigenspace (stable : ∀ y ∈ K, T y ∈ K)
    (intertwine : ∀ y : K, E ⟨T y, stable y y.property⟩ = α • E y + β • S (E y))
    (hβ : β ≠ 0) (c : ℂ) (y : K) (hy : y.val ∈ T.maxGenEigenspace c) :
    E y ∈ S.maxGenEigenspace ((c - α) / β) := by
  rw [Module.End.mem_maxGenEigenspace] at hy ⊢
  obtain ⟨k, hk⟩ := hy
  have hmem : ∀ j ≤ k, ((T - c • 1) ^ j) y.val ∈ K := by
    intro j _
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      have h := ih (by omega)
      exact K.sub_mem (stable _ h) (K.smul_mem c h)
  refine ⟨k, ?_⟩
  have h := edge_pow T K S E α β stable intertwine hβ c k y hmem
  have hzero : (⟨((T - c • 1) ^ k) y, hmem k le_rfl⟩ : K) = 0 := Subtype.ext hk
  rw [hzero, map_zero] at h
  have hβk : β ^ k ≠ 0 := pow_ne_zero _ hβ
  exact (smul_eq_zero.mp h.symm).resolve_left hβk

end Edge

section Joint

variable {ι : Type*}

/-- **The edge map on joint generalized eigenspaces.** Let the operators `T i` preserve `K`, be
intertwined on `K` by the edge map `E` with `α i + β i • S i` (`β i ≠ 0`), and let some `T i₀`
act on `M ⧸ K` by a scalar `λ ≠ c i₀`. Then `E` maps the joint generalized eigenspace of the
`T i` for the character `c` into the joint generalized eigenspace of the `S i` for
`(c i - α i) / β i`. -/
def jointEdge (T : ι → Module.End ℂ M) (K : Submodule ℂ M) (S : ι → Module.End ℂ H)
    (E : K →ₗ[ℂ] H) (α β lam c : ι → ℂ) (stable : ∀ i, ∀ y ∈ K, T i y ∈ K)
    (intertwine : ∀ i (y : K),
      E ⟨T i y, stable i y y.property⟩ = α i • E y + β i • S i (E y))
    (hβ : ∀ i, β i ≠ 0) (i₀ : ι) (sub_mem : ∀ y, T i₀ y - lam i₀ • y ∈ K) (hne : c i₀ ≠ lam i₀) :
    (⨅ i, (T i).maxGenEigenspace (c i) : Submodule ℂ M) →ₗ[ℂ]
      (⨅ i, (S i).maxGenEigenspace ((c i - α i) / β i) : Submodule ℂ H) :=
  have hK : ∀ y ∈ (⨅ i, (T i).maxGenEigenspace (c i) : Submodule ℂ M), y ∈ K := by
    intro y hy
    apply maxGenEigenspace_le_of_sub_mem (T i₀) K (lam i₀) (c i₀) sub_mem hne
    exact (Submodule.mem_iInf _).mp hy i₀
  { toFun := fun y => ⟨E ⟨y.val, hK y.val y.property⟩, by
      apply (Submodule.mem_iInf _).mpr
      intro i
      exact edge_mem_maxGenEigenspace (T i) K (S i) E (α i) (β i) (stable i) (intertwine i)
        (hβ i) (c i) ⟨y.val, hK y.val y.property⟩ ((Submodule.mem_iInf _).mp y.property i)⟩
    map_add' := fun y z => by
      apply Subtype.ext
      exact map_add E ⟨y.val, hK _ y.property⟩ ⟨z.val, hK _ z.property⟩
    map_smul' := fun a y => by
      apply Subtype.ext
      exact map_smul E a ⟨y.val, hK _ y.property⟩ }

theorem jointEdge_injective (T : ι → Module.End ℂ M) (K : Submodule ℂ M)
    (S : ι → Module.End ℂ H) (E : K →ₗ[ℂ] H) (α β lam c : ι → ℂ)
    (stable : ∀ i, ∀ y ∈ K, T i y ∈ K)
    (intertwine : ∀ i (y : K),
      E ⟨T i y, stable i y y.property⟩ = α i • E y + β i • S i (E y))
    (hβ : ∀ i, β i ≠ 0) (injective : Function.Injective E) (i₀ : ι)
    (sub_mem : ∀ y, T i₀ y - lam i₀ • y ∈ K) (hne : c i₀ ≠ lam i₀) :
    Function.Injective (jointEdge T K S E α β lam c stable intertwine hβ i₀ sub_mem hne) := by
  intro y z h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (congrArg Subtype.val (injective h') :)

/-- **Finite-dimensionality of the joint generalized eigenspace.** -/
theorem finite_iInf [FiniteDimensional ℂ H] (T : ι → Module.End ℂ M) (K : Submodule ℂ M)
    (S : ι → Module.End ℂ H) (E : K →ₗ[ℂ] H) (α β lam c : ι → ℂ)
    (stable : ∀ i, ∀ y ∈ K, T i y ∈ K)
    (intertwine : ∀ i (y : K),
      E ⟨T i y, stable i y y.property⟩ = α i • E y + β i • S i (E y))
    (hβ : ∀ i, β i ≠ 0) (injective : Function.Injective E) (i₀ : ι)
    (sub_mem : ∀ y, T i₀ y - lam i₀ • y ∈ K) (hne : c i₀ ≠ lam i₀) :
    Module.Finite ℂ (⨅ i, (T i).maxGenEigenspace (c i) : Submodule ℂ M) :=
  Module.Finite.of_injective _
    (jointEdge_injective T K S E α β lam c stable intertwine hβ injective i₀ sub_mem hne)

/-- **Joint bound.** Under the hypotheses of `jointEdge`, with `E` injective, the joint
generalized eigenspace of the `T i` for the character `c` embeds into the joint generalized
eigenspace of the `S i` for `(c i - α i) / β i`. -/
theorem finrank_iInf_le [FiniteDimensional ℂ H] (T : ι → Module.End ℂ M) (K : Submodule ℂ M)
    (S : ι → Module.End ℂ H) (E : K →ₗ[ℂ] H) (α β lam c : ι → ℂ)
    (stable : ∀ i, ∀ y ∈ K, T i y ∈ K)
    (intertwine : ∀ i (y : K),
      E ⟨T i y, stable i y y.property⟩ = α i • E y + β i • S i (E y))
    (hβ : ∀ i, β i ≠ 0) (injective : Function.Injective E) (i₀ : ι)
    (sub_mem : ∀ y, T i₀ y - lam i₀ • y ∈ K) (hne : c i₀ ≠ lam i₀) :
    finrank ℂ (⨅ i, (T i).maxGenEigenspace (c i) : Submodule ℂ M) ≤
      finrank ℂ (⨅ i, (S i).maxGenEigenspace ((c i - α i) / β i) : Submodule ℂ H) :=
  LinearMap.finrank_le_finrank_of_injective
    (jointEdge_injective T K S E α β lam c stable intertwine hβ injective i₀ sub_mem hne)

end Joint

end TernaryPeriodPolynomials.LevelThree.LocalAssembly
