module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.CentralTwist
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Unipotence of a central twist on filtered coefficients

Let `ρ` be a representation of `G` on `V` and `(φ, A)` a compatible pair:
`φ : G →* G` with central `φ`-fixed defects `a⁻¹ * φ a`, and `A : V → V` linear with
`A ∘ ρ (φ g) = ρ g ∘ A`. Suppose that `V` has a finite filtration on whose graded pieces
both `ρ` and `A` act trivially. Then `(α - 1)^(3m)` sends every inhomogeneous 2-cocycle
to a coboundary, where `α ω (a, b) = A (ω (φ a) (φ b))`.

The induction on the filtration uses the explicit trivial-coefficient computation of
`CentralTwist`: modulo the previous step, `(α - 1)^3 ω` is the coboundary of an explicit
cochain built from `ω`, so it differs from a coboundary by a cocycle of lower filtration.

We also prove the elementary characteristic-zero fact used afterwards: if `f` preserves a
submodule `B`, `(f - 1)^N x ∈ B` and `f^K x - x ∈ B` with `K > 0`, then `f x - x ∈ B`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness.FilteredUnipotence

open CentralTwist

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- The inhomogeneous 2-cocycle condition. -/
def IsCocycle2 (ρ : Representation ℂ G V) (ω : G → G → V) : Prop :=
  ∀ a b c, ρ a (ω b c) - ω (a * b) c + ω a (b * c) - ω a b = 0

/-- The inhomogeneous coboundary. -/
def dρ (ρ : Representation ℂ G V) : (G → V) →ₗ[ℂ] (G → G → V) where
  toFun τ a b := ρ a (τ b) - τ (a * b) + τ a
  map_add' τ σ := by
    funext a b
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c τ := by
    funext a b
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add]

theorem dρ_apply (ρ : Representation ℂ G V) (τ : G → V) (a b : G) :
    dρ ρ τ a b = ρ a (τ b) - τ (a * b) + τ a := rfl

theorem dρ_isCocycle (ρ : Representation ℂ G V) (τ : G → V) : IsCocycle2 ρ (dρ ρ τ) := by
  intro a b c
  simp only [dρ_apply, map_sub, map_add, ← Module.End.mul_apply, ← map_mul, mul_assoc]
  abel

variable (ρ : Representation ℂ G V) (φ : G →* G) (A : V →ₗ[ℂ] V)

/-- Twisted pull-back on 2-cochains. -/
def pull2 : (G → G → V) →ₗ[ℂ] (G → G → V) where
  toFun ω a b := A (ω (φ a) (φ b))
  map_add' ω η := by funext a b; simp
  map_smul' c ω := by funext a b; simp

/-- Twisted pull-back on 1-cochains. -/
def pull1 : (G → V) →ₗ[ℂ] (G → V) where
  toFun τ a := A (τ (φ a))
  map_add' ω η := by funext a; simp
  map_smul' c ω := by funext a; simp

theorem pull2_apply (ω : G → G → V) (a b : G) : pull2 φ A ω a b = A (ω (φ a) (φ b)) := rfl

theorem pull1_apply (τ : G → V) (a : G) : pull1 φ A τ a = A (τ (φ a)) := rfl

variable {ρ φ A}
variable (hA : ∀ g v, A (ρ (φ g) v) = ρ g (A v))
include hA

theorem pull2_isCocycle {ω : G → G → V} (hω : IsCocycle2 ρ ω) : IsCocycle2 ρ (pull2 φ A ω) := by
  intro a b c
  simp only [pull2_apply, map_mul, ← hA]
  rw [← map_sub, ← map_add, ← map_sub, hω, map_zero]

theorem pull2_dρ (τ : G → V) : pull2 φ A (dρ ρ τ) = dρ ρ (pull1 φ A τ) := by
  funext a b
  simp only [pull2_apply, dρ_apply, pull1_apply, map_add, map_sub, hA, map_mul]

theorem sub_one_pow_dρ (k : ℕ) (τ : G → V) :
    ((pull2 φ A - 1) ^ k) (dρ ρ τ) = dρ ρ (((pull1 φ A - 1) ^ k) τ) := by
  induction k generalizing τ with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
    have : (pull2 φ A - 1) (dρ ρ τ) = dρ ρ ((pull1 φ A - 1) τ) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, pull2_dρ hA, map_sub]
      rfl
    rw [this, ih]

theorem sub_one_pow_isCocycle (k : ℕ) {ω : G → G → V} (hω : IsCocycle2 ρ ω) :
    IsCocycle2 ρ (((pull2 φ A - 1) ^ k) ω) := by
  induction k with
  | zero => exact hω
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    intro a b c
    have h1 := pull2_isCocycle hA ih a b c
    have h2 := ih a b c
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, map_sub] at h1 h2 ⊢
    linear_combination (norm := abel) h1 - h2

omit hA

/-! ## The filtration induction -/

variable (F : ℕ → Submodule ℂ V) (mono : Monotone F) (bot : F 0 = ⊥)
  (hρF : ∀ i g v, v ∈ F (i + 1) → ρ g v - v ∈ F i)
  (hAF : ∀ i v, v ∈ F (i + 1) → A v - v ∈ F i)

include mono hAF in
theorem A_mem {i : ℕ} {v : V} (hv : v ∈ F (i + 1)) : A v ∈ F (i + 1) := by
  have := mono (Nat.le_succ i) (hAF i v hv)
  simpa using (F (i + 1)).add_mem this hv

include mono hρF in
theorem ρ_mem {i : ℕ} (g : G) {v : V} (hv : v ∈ F (i + 1)) : ρ g v ∈ F (i + 1) := by
  have := mono (Nat.le_succ i) (hρF i g v hv)
  simpa using (F (i + 1)).add_mem this hv

include hAF in
theorem mkQ_A {i : ℕ} {v : V} (hv : v ∈ F (i + 1)) : (F i).mkQ (A v) = (F i).mkQ v := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hAF i v hv

include hρF in
theorem mkQ_ρ {i : ℕ} (g : G) {v : V} (hv : v ∈ F (i + 1)) : (F i).mkQ (ρ g v) = (F i).mkQ v := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hρF i g v hv

include mono hAF in
theorem step2 {i : ℕ} (ω : G → G → V) (hω : ∀ a b, ω a b ∈ F (i + 1)) :
    (∀ a b, ((pull2 φ A - 1) ω) a b ∈ F (i + 1)) ∧
      ∀ a b, (F i).mkQ (((pull2 φ A - 1) ω) a b) =
        delta φ (fun x y => (F i).mkQ (ω x y)) a b := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull2_apply]
    exact (F (i + 1)).sub_mem (A_mem F mono hAF (hω _ _)) (hω a b)
  · simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull2_apply, delta,
      map_sub]
    rw [mkQ_A F hAF (hω _ _)]

include mono hAF in
theorem step2_iter {i : ℕ} (k : ℕ) (ω : G → G → V) (hω : ∀ a b, ω a b ∈ F (i + 1)) :
    (∀ a b, (((pull2 φ A - 1) ^ k) ω) a b ∈ F (i + 1)) ∧
      ∀ a b, (F i).mkQ ((((pull2 φ A - 1) ^ k) ω) a b) =
        (delta φ)^[k] (fun x y => (F i).mkQ (ω x y)) a b := by
  induction k with
  | zero => exact ⟨hω, fun a b => rfl⟩
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := step2 F mono hAF _ ih.1
    refine ⟨h1, fun a b => ?_⟩
    rw [h2]
    congr 1
    funext x y
    exact ih.2 x y

include mono hAF in
theorem step1 {i : ℕ} (τ : G → V) (hτ : ∀ a, τ a ∈ F (i + 1)) :
    (∀ a, ((pull1 φ A - 1) τ) a ∈ F (i + 1)) ∧
      ∀ a, (F i).mkQ (((pull1 φ A - 1) τ) a) = delta1 φ (fun x => (F i).mkQ (τ x)) a := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull1_apply]
    exact (F (i + 1)).sub_mem (A_mem F mono hAF (hτ _)) (hτ a)
  · simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull1_apply, delta1,
      map_sub]
    rw [mkQ_A F hAF (hτ _)]

/-- The lift of `cubePrimitive`. -/
def cubeLift (φ : G →* G) (A : V →ₗ[ℂ] V) (ω : G → G → V) : G → V :=
  -(((pull1 φ A - 1 : (G → V) →ₗ[ℂ] (G → V)) ^ 2) (fun a => ω a (defect φ a)))

include mono hρF hAF in
/-- One filtration step: `(α - 1)^3 ω` is a coboundary modulo `F i`. -/
theorem cube_step {i : ℕ} (hcen : ∀ a x, defect φ a * x = x * defect φ a)
    (hfix : ∀ a, φ (defect φ a) = defect φ a) (ω : G → G → V) (hω : IsCocycle2 ρ ω)
    (hωF : ∀ a b, ω a b ∈ F (i + 1)) :
    ∀ a b, (((pull2 φ A - 1 : Module.End ℂ (G → G → V)) ^ 3) ω) a b -
      dρ ρ (cubeLift φ A ω) a b ∈ F i := by
  set ω' : G → G → V ⧸ F i := fun x y => (F i).mkQ (ω x y)
  have hω' : CentralTwist.IsCocycle ω' := by
    intro a b c
    have := congrArg (F i).mkQ (hω a b c)
    simp only [map_sub, map_add, map_zero, mkQ_ρ F hρF a (hωF b c)] at this
    exact this
  set τ : G → V := fun a => ω a (defect φ a)
  have hτ : ∀ a, τ a ∈ F (i + 1) := fun a => hωF _ _
  obtain ⟨hτ1, hτ1'⟩ := step1 F mono hAF τ hτ
  obtain ⟨hτ2, hτ2'⟩ := step1 F mono hAF _ hτ1
  have hlift : ∀ a, cubeLift φ A ω a ∈ F (i + 1) := by
    intro a
    simp only [cubeLift, pow_two, Module.End.mul_apply, Pi.neg_apply]
    exact (F (i + 1)).neg_mem (hτ2 a)
  have hliftQ : ∀ a, (F i).mkQ (cubeLift φ A ω a) = cubePrimitive (φ := φ) ω' a := by
    intro a
    simp only [cubeLift, pow_two, Module.End.mul_apply, Pi.neg_apply, map_neg, cubePrimitive]
    rw [hτ2']
    congr 2
    funext x
    exact hτ1' x
  obtain ⟨-, hcube⟩ := step2_iter F mono hAF 3 ω hωF
  intro a b
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hcube a b]
  have key := delta_cube hcen hfix hω' a b
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at key ⊢
  rw [key, dρ_apply, map_add, map_sub, mkQ_ρ F hρF a (hlift b), hliftQ, hliftQ, hliftQ]
  simp only [d1]
  abel

include hA mono bot hρF hAF in
/-- **Unipotence on filtered coefficients.** -/
theorem sub_one_pow_mem_range (hcen : ∀ a x, defect φ a * x = x * defect φ a)
    (hfix : ∀ a, φ (defect φ a) = defect φ a) (i : ℕ) (ω : G → G → V) (hω : IsCocycle2 ρ ω)
    (hωF : ∀ a b, ω a b ∈ F i) :
    ((pull2 φ A - 1) ^ (3 * i)) ω ∈ LinearMap.range (dρ ρ) := by
  induction i generalizing ω with
  | zero =>
    have : ω = 0 := by
      funext a b
      have := hωF a b
      rw [bot, Submodule.mem_bot] at this
      exact this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  | succ i ih =>
    set E : G → G → V := ((pull2 φ A - 1 : Module.End ℂ (G → G → V)) ^ 3) ω - dρ ρ (cubeLift φ A ω)
    have hE : IsCocycle2 ρ E := by
      intro a b c
      have h1 := sub_one_pow_isCocycle hA 3 hω a b c
      have h2 := dρ_isCocycle ρ (cubeLift φ A ω) a b c
      simp only [E, Pi.sub_apply, map_sub] at h1 h2 ⊢
      linear_combination (norm := abel) h1 - h2
    have hEF : ∀ a b, E a b ∈ F i := cube_step F mono hρF hAF hcen hfix ω hω hωF
    obtain ⟨τ', hτ'⟩ := ih E hE hEF
    have hsplit : ((pull2 φ A - 1 : Module.End ℂ (G → G → V)) ^ 3) ω = E + dρ ρ (cubeLift φ A ω) := by
      simp [E]
    rw [show 3 * (i + 1) = 3 * i + 3 by ring, pow_add, Module.End.mul_apply, hsplit, map_add,
      sub_one_pow_dρ hA]
    exact Submodule.add_mem _ ⟨τ', hτ'⟩ ⟨_, rfl⟩

/-! ## Unipotent and periodic implies fixed (characteristic zero) -/

section Periodic

open Polynomial

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem aeval_mem {f : M →ₗ[ℂ] M} {B : Submodule ℂ M} (hB : ∀ x ∈ B, f x ∈ B) (p : ℂ[X])
    {x : M} (hx : x ∈ B) : (aeval f p) x ∈ B := by
  have hpow : ∀ k : ℕ, (f ^ k) x ∈ B := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hB _ ih
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact B.add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact B.smul_mem c (hpow n)

theorem isCoprime_sub_one_geom (K : ℕ) (hK : 0 < K) :
    IsCoprime (X - 1 : ℂ[X]) (∑ i ∈ Finset.range K, X ^ i) := by
  set P : ℂ[X] := ∑ i ∈ Finset.range K, X ^ i
  have heval : P.eval 1 = K := by simp [P, eval_finsetSum]
  obtain ⟨Q, hQ⟩ : X - C 1 ∣ P - C (P.eval 1) := X_sub_C_dvd_sub_C_eval
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  refine ⟨-(C (K : ℂ)⁻¹ * Q), C (K : ℂ)⁻¹, ?_⟩
  have hP : P = C (K : ℂ) + (X - 1) * Q := by
    rw [heval, C_1] at hQ
    linear_combination hQ
  rw [hP]
  have : C (K : ℂ)⁻¹ * C (K : ℂ) = 1 := by rw [← C_mul, inv_mul_cancel₀ hK', C_1]
  linear_combination this

/-- If `f` preserves `B`, `(f - 1)^N x ∈ B` and `f^K x - x ∈ B` with `0 < K`, then
`f x - x ∈ B`. -/
theorem sub_mem_of_unipotent_periodic (f : M →ₗ[ℂ] M) (B : Submodule ℂ M)
    (hB : ∀ x ∈ B, f x ∈ B) (x : M) (N K : ℕ) (hK : 0 < K)
    (hN : ((f - 1) ^ N) x ∈ B) (hper : (f ^ K) x - x ∈ B) : f x - x ∈ B := by
  obtain ⟨u, v, huv⟩ := (isCoprime_sub_one_geom K hK).pow_left (m := N)
  have hgeom : (∑ i ∈ Finset.range K, (X : ℂ[X]) ^ i) * (X - 1) = X ^ K - 1 := geom_sum_mul X K
  have hpoly : (X - 1 : ℂ[X]) = u * (X - 1) ^ (N + 1) + v * (X ^ K - 1) := by
    rw [← hgeom, pow_succ]
    linear_combination (1 - X : ℂ[X]) * huv
  have hsub : (f - 1) ∈ ({g | ∀ y ∈ B, g y ∈ B} : Set (M →ₗ[ℂ] M)) := by
    intro y hy
    simpa using B.sub_mem (hB y hy) hy
  have key := congrArg (fun p => (aeval f p) x) hpoly
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one, LinearMap.add_apply,
    Module.End.mul_apply] at key
  have e : f x - x = (f - 1) x := by simp
  rw [e, key]
  refine B.add_mem (aeval_mem hB u ?_) (aeval_mem hB v ?_)
  · rw [pow_succ', Module.End.mul_apply]
    exact hsub _ hN
  · simpa using hper

end Periodic

end TernaryPeriodPolynomials.FlagExactness.FilteredUnipotence
