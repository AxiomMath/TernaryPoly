module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.HomogeneousCohomology
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section


/-!
# Level transfer (L2), step 1: the `S`-action and the averaging projector on homogeneous cochains

Formalized by Claude Sonnet 5.5.
Convention C6 (level group `S` versus the neat subgroup `N = Γ(6)`).

In the homogeneous-cochain model of `GeneralEisenstein.Homogeneous`, a group `S ≤ G` with a normal
finite-index subgroup `N` acts on the `N`-equivariant cochains by `(s • f)(x) = ρ(s) f(s⁻¹ x)`; the
`S`-equivariant cochains are exactly the fixed points, and `Avg f = |S/N|⁻¹ ∑_{q ∈ S/N} q • f` is a
projection of the `N`-cochains onto them which commutes with the differentials.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelTransfer

open GeneralEisenstein.Homogeneous

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- Raw functions on `(k+1)`-tuples of vertices. -/
abbrev FunSpace (G V : Type) (k : ℕ) := (Fin (k + 1) → G) → V

/-- The action `(s • f)(x) = ρ(s) f(s⁻¹ x)` on raw functions. -/
def actFun (s : G) {k : ℕ} : FunSpace G V k →ₗ[ℂ] FunSpace G V k where
  toFun f x := ρ s (f (fun i => s⁻¹ * x i))
  map_add' f g := by funext x; simp
  map_smul' a f := by funext x; simp

theorem actFun_apply (s : G) {k : ℕ} (f : FunSpace G V k) (x : Fin (k + 1) → G) :
    actFun ρ s f x = ρ s (f (fun i => s⁻¹ * x i)) := rfl

theorem actFun_mul (s t : G) {k : ℕ} (f : FunSpace G V k) :
    actFun ρ (s * t) f = actFun ρ s (actFun ρ t f) := by
  funext x
  simp only [actFun_apply, map_mul, Module.End.mul_apply, mul_inv_rev, mul_assoc]

theorem actFun_one {k : ℕ} (f : FunSpace G V k) : actFun ρ 1 f = f := by
  funext x
  simp [actFun_apply]

/-- Raw degree-one-to-two differential. -/
def rd1 : FunSpace G V 1 →ₗ[ℂ] FunSpace G V 2 where
  toFun f x := f ![x 1, x 2] - f ![x 0, x 2] + f ![x 0, x 1]
  map_add' f g := by funext x; simp only [Pi.add_apply]; abel
  map_smul' a f := by funext x; simp only [Pi.smul_apply, RingHom.id_apply, smul_add, smul_sub]

/-- Raw degree-two differential. -/
def rd2 : FunSpace G V 2 →ₗ[ℂ] FunSpace G V 3 where
  toFun f x := f ![x 1, x 2, x 3] - f ![x 0, x 2, x 3] + f ![x 0, x 1, x 3] - f ![x 0, x 1, x 2]
  map_add' f g := by funext x; simp only [Pi.add_apply]; abel
  map_smul' a f := by funext x; simp only [Pi.smul_apply, RingHom.id_apply, smul_add, smul_sub]

theorem actFun_rd1 (s : G) (f : FunSpace G V 1) : actFun ρ s (rd1 f) = rd1 (actFun ρ s f) := by
  funext x
  have h : ∀ (a b : Fin 3), (fun i : Fin 2 => s⁻¹ * (![x a, x b] : Fin 2 → G) i) =
      ![s⁻¹ * x a, s⁻¹ * x b] := by
    intro a b; funext i; fin_cases i <;> rfl
  simp only [actFun_apply, rd1, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sub, h]

theorem actFun_rd2 (s : G) (f : FunSpace G V 2) : actFun ρ s (rd2 f) = rd2 (actFun ρ s f) := by
  funext x
  have h : ∀ (a b c : Fin 4), (fun i : Fin 3 => s⁻¹ * (![x a, x b, x c] : Fin 3 → G) i) =
      ![s⁻¹ * x a, s⁻¹ * x b, s⁻¹ * x c] := by
    intro a b c; funext i; fin_cases i <;> rfl
  simp only [actFun_apply, rd2, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sub, h]

/-- `N`-equivariance of a raw function. -/
def IsEq (N : Subgroup G) {k : ℕ} (f : FunSpace G V k) : Prop :=
  ∀ γ ∈ N, ∀ x : Fin (k + 1) → G, f (fun i => γ * x i) = ρ γ (f x)

theorem mem_cochains_iff (N : Subgroup G) (k : ℕ) (f : FunSpace G V k) :
    f ∈ cochains N ρ k ↔ IsEq ρ N f :=
  ⟨fun h γ hγ x => h ⟨γ, hγ⟩ x, fun h γ x => h γ.1 γ.2 x⟩

theorem IsEq.act {N : Subgroup G} {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f) {s : G}
    (hs : ∀ n ∈ N, s⁻¹ * n * s ∈ N) : IsEq ρ N (actFun ρ s f) := by
  intro γ hγ x
  simp only [actFun_apply]
  have h1 : (fun i => s⁻¹ * (γ * x i)) = fun i => (s⁻¹ * γ * s) * (s⁻¹ * x i) := by
    funext i; group
  rw [h1, hf _ (hs γ hγ), ← Module.End.mul_apply, ← map_mul]
  have : s * (s⁻¹ * γ * s) = γ * s := by group
  rw [this, map_mul, Module.End.mul_apply]

theorem IsEq.act_mem {N : Subgroup G} {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f) {n : G}
    (hn : n ∈ N) : actFun ρ n f = f := by
  funext x
  simp only [actFun_apply]
  rw [show (fun i => n⁻¹ * x i) = fun i => n⁻¹ * x i from rfl, hf n⁻¹ (N.inv_mem hn) x,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

section Avg

variable (N S : Subgroup G) [Fintype (S ⧸ N.subgroupOf S)]

/-- The averaging operator `|S/N|⁻¹ ∑_{q ∈ S/N} q • (-)` (on `N`-equivariant functions). -/
def avg {k : ℕ} : FunSpace G V k →ₗ[ℂ] FunSpace G V k :=
  ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
    ∑ q : S ⧸ N.subgroupOf S, actFun ρ ((Quotient.out q : S) : G)

theorem avg_apply {k : ℕ} (f : FunSpace G V k) :
    avg ρ N S f = ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
      ∑ q : S ⧸ N.subgroupOf S, actFun ρ ((Quotient.out q : S) : G) f := by
  simp [avg, LinearMap.sum_apply]

theorem actFun_avg {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f) {s : G} (hs : s ∈ S) :
    actFun ρ s (avg ρ N S f) = avg ρ N S f := by
  rw [avg_apply, map_smul, map_sum]
  congr 1
  have key : ∀ q : S ⧸ N.subgroupOf S, actFun ρ s (actFun ρ ((Quotient.out q : S) : G) f) =
      actFun ρ ((Quotient.out ((⟨s, hs⟩ : S) • q) : S) : G) f := by
    intro q
    rw [← actFun_mul]
    have h1 : (QuotientGroup.mk (s := N.subgroupOf S) (Quotient.out ((⟨s, hs⟩ : S) • q))) =
        QuotientGroup.mk (s := N.subgroupOf S) ((⟨s, hs⟩ : S) * Quotient.out q) := by
      rw [QuotientGroup.out_eq']
      have hq := QuotientGroup.out_eq' q
      calc (⟨s, hs⟩ : S) • q = (⟨s, hs⟩ : S) • (QuotientGroup.mk (s := N.subgroupOf S) (Quotient.out q)) := by
            rw [hq]
        _ = _ := rfl
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : s * ((Quotient.out q : S) : G) =
        ((Quotient.out ((⟨s, hs⟩ : S) • q) : S) : G) *
          (((Quotient.out ((⟨s, hs⟩ : S) • q) : S) : G)⁻¹ * (s * ((Quotient.out q : S) : G))) := by
      group
    rw [h3, actFun_mul, hf.act_mem]
    simpa using h2
  simp only [key]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨s, hs⟩ : S)) _ _ (fun q => rfl)

theorem IsEq.add {M : Subgroup G} {k : ℕ} {f g : FunSpace G V k} (hf : IsEq ρ M f)
    (hg : IsEq ρ M g) : IsEq ρ M (f + g) := by
  intro γ hγ x
  simp only [Pi.add_apply, hf γ hγ x, hg γ hγ x, map_add]

theorem IsEq.smul {M : Subgroup G} {k : ℕ} {f : FunSpace G V k} (a : ℂ) (hf : IsEq ρ M f) :
    IsEq ρ M (a • f) := by
  intro γ hγ x
  simp only [Pi.smul_apply, hf γ hγ x, map_smul]

theorem IsEq.zero (M : Subgroup G) (k : ℕ) : IsEq ρ M (0 : FunSpace G V k) := by
  intro γ hγ x
  simp

theorem isEq_avg {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f)
    (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) : IsEq ρ N (avg ρ N S f) := by
  classical
  rw [avg_apply]
  apply IsEq.smul
  have : ∀ (T : Finset (S ⧸ N.subgroupOf S)),
      IsEq ρ N (∑ q ∈ T, actFun ρ ((Quotient.out q : S) : G) f) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using IsEq.zero ρ N k
    | insert a T ha ih =>
      rw [Finset.sum_insert ha]
      exact IsEq.add ρ (hf.act ρ (hnorm _ (Quotient.out a).2)) ih
  exact this _

theorem isEq_iff_fixed {N S : Subgroup G} (hNS : N ≤ S) {k : ℕ} (f : FunSpace G V k) :
    IsEq ρ S f ↔ IsEq ρ N f ∧ ∀ s ∈ S, actFun ρ s f = f := by
  constructor
  · intro h
    exact ⟨fun γ hγ x => h γ (hNS hγ) x, fun s hs => IsEq.act_mem ρ h hs⟩
  · rintro ⟨-, h⟩ s hs x
    have := congrFun (h s⁻¹ (S.inv_mem hs)) x
    simp only [actFun_apply, inv_inv] at this
    have h2 := congrArg (ρ s) this
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h2
    exact h2

theorem avg_of_isEq_S {N S : Subgroup G} [Fintype (S ⧸ N.subgroupOf S)] {k : ℕ}
    {f : FunSpace G V k} (hf : IsEq ρ S f) : avg ρ N S f = f := by
  rw [avg_apply]
  have h : ∀ q : S ⧸ N.subgroupOf S, actFun ρ ((Quotient.out q : S) : G) f = f :=
    fun q => IsEq.act_mem ρ hf (Quotient.out q).2
  simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : (Fintype.card (S ⧸ N.subgroupOf S) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ this, one_smul]

theorem avg_rd1 (f : FunSpace G V 1) : avg ρ N S (rd1 f) = rd1 (avg ρ N S f) := by
  simp only [avg_apply, map_smul, map_sum, actFun_rd1]

theorem avg_rd2 (f : FunSpace G V 2) : avg ρ N S (rd2 f) = rd2 (avg ρ N S f) := by
  simp only [avg_apply, map_smul, map_sum, actFun_rd2]

end Avg

end TernaryPeriodPolynomials.Argument.LevelTransfer
