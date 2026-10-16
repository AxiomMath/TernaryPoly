module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Tp

@[expose] public section


/-!
# Semisimplicity of the Hecke operators on `S_k(Γ₁(3))`

The Petersson product `petThree` is a positive definite Hermitian form on `S_k(Γ₁(3))`
(`petThree_self_eq_zero`) and `⟨T_p f, g⟩ = χ_k(p) ⟨f, T_p g⟩` with `χ_k(p) = ±1`
(`petThree_hecke`). If `χ_k(p) = 1`, `T_p` is self-adjoint; if `χ_k(p) = -1`, then `i T_p` is
self-adjoint. In either case there is a scalar `c ≠ 0` with `c T_p` self-adjoint
(`maxGenEigenspace_le_eigenspace_twisted`), and a self-adjoint operator for a positive definite
form has no nilpotent part (level-one abstract lemma). Hence generalized eigenvectors of `T_p` are
eigenvectors (`levelThree_semisimple`), and the joint generalized eigenspace of `{T_p : p ≠ 3}`
equals the joint eigenspace (`jointGenEigenspaceAwayThree_eq`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open ComplexConjugate

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonSemisimple

open TernaryPeriodPolynomials.Spectral.PeterssonSemisimple
  (maxGenEigenspace_le_eigenspace_abstract)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonForm
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonTp

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V → V → ℂ)
  (sub_left : ∀ x y z, B (x - y) z = B x z - B y z)
  (smul_left : ∀ (a : ℂ) x z, B (a • x) z = conj a * B x z)
  (sub_right : ∀ x y z, B z (x - y) = B z x - B z y)
  (smul_right : ∀ (a : ℂ) x z, B z (a • x) = a * B z x)
  (definite : ∀ x, B x x = 0 → x = 0)
  (T : Module.End ℂ V) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
  (adj : ∀ x y, B (T x) y = ε * B x (T y))

include sub_left smul_left sub_right smul_right definite hε adj in
/-- **No Jordan blocks for a `±`-self-adjoint operator**: if `⟨T x, y⟩ = ε ⟨x, T y⟩` with
`ε = ±1` for a positive definite Hermitian form, generalized eigenvectors are eigenvectors. -/
theorem maxGenEigenspace_le_eigenspace_twisted (μ : ℂ) :
    T.maxGenEigenspace μ ≤ T.eigenspace μ := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ conj c * ε = c := by
    rcases hε with rfl | rfl
    · exact ⟨1, one_ne_zero, by simp⟩
    · exact ⟨Complex.I, Complex.I_ne_zero, by simp⟩
  have hS : ∀ x y, B ((c • T) x) y = B x ((c • T) y) := by
    intro x y
    simp only [LinearMap.smul_apply]
    rw [smul_left, adj, smul_right, ← mul_assoc, hc]
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨n, hn⟩ := hv
  have hv' : v ∈ (c • T).maxGenEigenspace (c * μ) := by
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨n, ?_⟩
    have e : c • T - (c * μ) • (1 : Module.End ℂ V) = c • (T - μ • 1) := by
      rw [smul_sub, mul_smul]
    rw [e, smul_pow, LinearMap.smul_apply, hn, smul_zero]
  have h := maxGenEigenspace_le_eigenspace_abstract B sub_left smul_left sub_right smul_right
    definite (c • T) hS (c * μ) hv'
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  rw [LinearMap.smul_apply, mul_smul] at h
  exact (smul_right_inj hc0).mp h

end Abstract

variable (k : ℤ)

/-- **Each Hecke operator `T_p` (`p ≠ 3`) on `S_k(Γ₁(3))` is semisimple**: generalized
eigenvectors are eigenvectors. -/
theorem levelThree_semisimple :
    ∀ (p : Nat.Primes) (hp : p.val ≠ 3) (μ : ℂ),
      Module.End.maxGenEigenspace (levelThreeHecke k p hp) μ ≤
        Module.End.eigenspace (levelThreeHecke k p hp) μ :=
  fun p hp μ => maxGenEigenspace_le_eigenspace_twisted (petThree k) (petThree_sub_left k)
    (petThree_smul_left k) (petThree_sub_right k) (petThree_smul_right k)
    (petThree_self_eq_zero k) (levelThreeHecke k p hp) (levelThreeChar k p.val)
    (levelThreeChar_cases k p.val) (petThree_hecke p hp) μ

/-- The joint generalized eigenspace of the Hecke operators `T_p`, `p ≠ 3`. -/
def jointGenEigenspaceAwayThree (eigenvalues : Nat.Primes → ℂ) :
    Submodule ℂ (CuspForm levelThree k) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3},
    Module.End.maxGenEigenspace (levelThreeHecke k p.1 p.2) (eigenvalues p.1)

/-- The joint eigenspace of the Hecke operators `T_p`, `p ≠ 3`. -/
def jointEigenspaceAwayThree (eigenvalues : Nat.Primes → ℂ) :
    Submodule ℂ (CuspForm levelThree k) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3},
    Module.End.eigenspace (levelThreeHecke k p.1 p.2) (eigenvalues p.1)

/-- **Joint generalized eigenspaces equal joint eigenspaces** (away from `3`, on
`S_k(Γ₁(3))`). -/
theorem jointGenEigenspaceAwayThree_eq (eigenvalues : Nat.Primes → ℂ) :
    jointGenEigenspaceAwayThree k eigenvalues = jointEigenspaceAwayThree k eigenvalues :=
  le_antisymm (iInf_mono fun p => levelThree_semisimple k p.1 p.2 _)
    (iInf_mono fun _ => Module.End.eigenspace_le_maxGenEigenspace)

end TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonSemisimple
