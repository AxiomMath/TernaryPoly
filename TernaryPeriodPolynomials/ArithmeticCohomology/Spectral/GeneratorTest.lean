module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.FiniteSupport.Basic
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
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Peel

@[expose] public section


/-!
# Generalized eigenvalues of a commutative algebra are detected on generators

Let `𝒜 = Algebra.adjoin ℂ S ≤ End(W)` be commutative, `W` finite dimensional, and let `V` be an
`𝒜`-stable subspace on which every generator `s ∈ S` acts with the single generalized eigenvalue
`c s`. Then every `f ∈ 𝒜` acts on `V` as a scalar plus a nilpotent operator. This is the linear
algebra that turns separation tested on generators into separation for the whole algebra.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Spectral

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pow_apply_mem (V : Submodule ℂ W) (Y : Module.End ℂ W) (hY : ∀ y ∈ V, Y y ∈ V)
    (j : ℕ) : ∀ y ∈ V, (Y ^ j) y ∈ V := by
  induction j with
  | zero => intro y hy; simpa using hy
  | succ j ih =>
    intro y hy
    rw [pow_succ', Module.End.mul_apply]
    exact hY _ (ih y hy)

/-- Sum of two commuting operators nilpotent on a common stable subspace. -/
theorem add_pow_apply_eq_zero (V : Submodule ℂ W) (X Y : Module.End ℂ W) (hXY : Commute X Y)
    (hY : ∀ y ∈ V, Y y ∈ V) (K L : ℕ)
    (hK : ∀ y ∈ V, (X ^ K) y = 0) (hL : ∀ y ∈ V, (Y ^ L) y = 0) :
    ∀ v ∈ V, ((X + Y) ^ (K + L)) v = 0 := by
  intro v hv
  rw [hXY.add_pow, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply]
  have hcv : ((K + L).choose i) • v ∈ V := V.toAddSubmonoid.nsmul_mem hv _
  by_cases hiK : K ≤ i
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hiK
    rw [show X ^ (K + d) = X ^ d * X ^ K by rw [← pow_add, add_comm], Module.End.mul_apply,
      hK _ (pow_apply_mem V Y hY _ _ hcv), map_zero]
  · have hLi : L ≤ K + L - i := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hLi
    rw [hd, show Y ^ (L + d) = Y ^ d * Y ^ L by rw [← pow_add, add_comm], Module.End.mul_apply,
      hL _ hcv, map_zero, map_zero]

/-- **Generator test.** In a commutative adjoined algebra, generalized eigenvalues on a stable
subspace are controlled by the generators. -/
theorem adjoin_scalar_add_nilpotent [FiniteDimensional ℂ W] (S : Set (Module.End ℂ W))
    (hcomm : ∀ f ∈ Algebra.adjoin ℂ S, ∀ g ∈ Algebra.adjoin ℂ S, Commute f g)
    (V : Submodule ℂ W) (hV : ∀ f ∈ Algebra.adjoin ℂ S, ∀ v ∈ V, f v ∈ V)
    (c : Module.End ℂ W → ℂ) (hS : ∀ s ∈ S, ∀ v ∈ V, v ∈ s.maxGenEigenspace (c s)) :
    ∀ f ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∃ K : ℕ, ∀ v ∈ V, ((f - μ • 1) ^ K) v = 0 := by
  have hsub : ∀ f ∈ Algebra.adjoin ℂ S, ∀ μ : ℂ, ∀ v ∈ V, (f - μ • 1) v ∈ V := by
    intro f hf μ v hv
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact V.sub_mem (hV f hf v hv) (V.smul_mem μ hv)
  intro f hf
  induction hf using Algebra.adjoin_induction with
  | mem s hs =>
    refine ⟨c s, Module.finrank ℂ W, fun v hv => ?_⟩
    have h := hS s hs v hv
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at h
    exact h
  | algebraMap r =>
    refine ⟨r, 1, fun v _ => ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, sub_self, pow_one, LinearMap.zero_apply]
  | add f g hf hg ihf ihg =>
    obtain ⟨μ, K, hK⟩ := ihf
    obtain ⟨ν, L, hL⟩ := ihg
    refine ⟨μ + ν, K + L, ?_⟩
    have hfg := hcomm f hf g hg
    have hrw : f + g - (μ + ν) • 1 = (f - μ • 1) + (g - ν • 1) := by
      rw [add_smul]; abel
    rw [hrw]
    refine add_pow_apply_eq_zero V _ _ ?_ (hsub g hg ν) K L hK hL
    exact ((hfg.sub_right ((Commute.one_right f).smul_right ν)).sub_left
      (((Commute.one_left g).smul_left μ).sub_right ((Commute.one_right 1).smul_right ν |>.smul_left μ)))
  | mul f g hf hg ihf ihg =>
    obtain ⟨μ, K, hK⟩ := ihf
    obtain ⟨ν, L, hL⟩ := ihg
    refine ⟨μ * ν, K + L, ?_⟩
    have hfg := hcomm f hf g hg
    have hrw : f * g - (μ * ν) • 1 = (f - μ • 1) * g + μ • (g - ν • 1) := by
      rw [sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul]; abel
    rw [hrw]
    have hfmg : Commute (f - μ • 1) g := hfg.sub_left ((Commute.one_left g).smul_left μ)
    have hY : ∀ y ∈ V, (μ • (g - ν • 1)) y ∈ V := fun y hy => by
      rw [LinearMap.smul_apply]; exact V.smul_mem μ (hsub g hg ν y hy)
    refine add_pow_apply_eq_zero V _ _ ?_ hY K L ?_ ?_
    · have hgg : Commute g (g - ν • 1) :=
        (Commute.refl g).sub_right ((Commute.one_right g).smul_right ν)
      have hfg' : Commute (f - μ • 1) (g - ν • 1) :=
        hfmg.sub_right ((Commute.one_right _).smul_right ν)
      exact ((hfg'.mul_left hgg).smul_right μ)
    · intro y hy
      rw [hfmg.mul_pow, Module.End.mul_apply]
      exact hK _ (pow_apply_mem V g (hV g hg) K y hy)
    · intro y hy
      rw [smul_pow, LinearMap.smul_apply, hL y hy, smul_zero]

end TernaryPeriodPolynomials.Spectral
