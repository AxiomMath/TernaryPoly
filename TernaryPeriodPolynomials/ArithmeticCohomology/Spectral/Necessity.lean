module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Boundary

@[expose] public section


/-!
# Eigencharacter separation is necessary for the projector targets

`EigenSeparated 𝒜 A` holds as soon as `𝒜` contains an idempotent with range `A` that is the
identity on `A`. Together with `spectral_of_eigenSeparated`, separation of the associate pair
is *equivalent* to the existence of an isotypical projection inside the away-three algebra.
Consequently the conjunction of the targets `cuspidal_associate_projector` (existence)
and `associate_projector_away_three_algebra` (membership) implies separation: the `EigenSeparated` obligation is not an artefact of the chosen proof route.

We also record that separation does not depend on the chosen realization of the Hecke
action (every `ActualBoundaryHecke` family equals `canonicalStratumHecke`), and that it is
vacuous for a zero associate pair.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Spectral

open TernaryPeriodPolynomials.SpectralSeparation

section Generic

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- For an idempotent `p`, every power `(p - 1) ^ (k + 1)` is `± (1 - p)`. -/
theorem idempotent_sub_one_pow_apply_eq_zero (p : Module.End ℂ W) (hp : p * p = p) (w : W)
    (k : ℕ) (hk : ((p - (1 : ℂ) • 1) ^ k) w = 0) : p w = w := by
  have hq : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hp]; abel
  have hpow : ∀ j : ℕ, (p - (1 : ℂ) • 1) ^ (j + 1) = (-1 : ℂ) ^ (j + 1) • (1 - p) := by
    intro j
    induction j with
    | zero => simp [one_smul]
    | succ j ih =>
      have hm : (1 - p) * (p - (1 : ℂ) • 1) = -(1 - p) := by
        rw [one_smul, show p - 1 = -(1 - p) by abel, mul_neg, hq]
      rw [pow_succ, ih, smul_mul_assoc, hm, smul_neg, ← neg_smul, pow_succ (-1 : ℂ) (j + 1),
        mul_neg_one]
  cases k with
  | zero =>
    rw [pow_zero, Module.End.one_apply] at hk
    rw [hk, map_zero]
  | succ j =>
    rw [hpow j, LinearMap.smul_apply] at hk
    have h1 : (1 - p) w = 0 :=
      (smul_eq_zero.mp hk).resolve_left (pow_ne_zero _ (by norm_num))
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact h1.symm

/-- An algebra containing an idempotent onto `A` separates `A`. No commutativity or finiteness
is needed. -/
theorem eigenSeparated_of_mem (𝒜 : Subalgebra ℂ (Module.End ℂ W)) (A : Submodule ℂ W)
    (p : Module.End ℂ W) (hp : p ∈ 𝒜) (hrange : LinearMap.range p = A)
    (hid : ∀ x ∈ A, p x = x) : EigenSeparated 𝒜 A := by
  intro a w ha ha0 hshare
  obtain ⟨μ, ⟨k, hka⟩, ⟨l, hlw⟩⟩ := hshare p hp
  have hidem : p * p = p := by
    apply LinearMap.ext
    intro x
    exact hid _ (hrange ▸ LinearMap.mem_range_self p x)
  -- the shared eigenvalue of `p` is `1`, because `p a = a ≠ 0`
  have hval : ∀ j : ℕ, ((p - μ • 1) ^ j) a = (1 - μ) ^ j • a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep : (p - μ • 1) a = (1 - μ) • a := by
        rw [LinearMap.sub_apply, hid a ha, LinearMap.smul_apply, Module.End.one_apply, sub_smul,
          one_smul]
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hstep, smul_smul, ← pow_succ]
  rw [hval k] at hka
  have hμ : μ = 1 := by
    rcases smul_eq_zero.mp hka with h | h
    · exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)).symm
    · exact absurd h ha0
  subst hμ
  have := idempotent_sub_one_pow_apply_eq_zero p hidem w l hlw
  rw [← this, ← hrange]
  exact LinearMap.mem_range_self p w

/-- A generalized eigenvalue of an eigenvector is its eigenvalue. -/
theorem eq_of_genEigen_of_eigen (T : Module.End ℂ W) (a : W) (c μ : ℂ) (ha : T a = c • a)
    (ha0 : a ≠ 0) (k : ℕ) (hk : ((T - μ • 1) ^ k) a = 0) : μ = c := by
  have hval : ∀ j : ℕ, ((T - μ • 1) ^ j) a = (c - μ) ^ j • a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep : (T - μ • 1) a = (c - μ) • a := by
        rw [LinearMap.sub_apply, ha, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hstep, smul_smul, ← pow_succ]
  rw [hval k] at hk
  rcases smul_eq_zero.mp hk with h | h
  · exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)).symm
  · exact absurd h ha0

/-- A vector sharing a generalized eigenvalue with an eigenvector lies in the corresponding
maximal generalized eigenspace. -/
theorem mem_maxGenEigenspace_of_shared (T : Module.End ℂ W) (a w : W) (c : ℂ) (ha : T a = c • a)
    (ha0 : a ≠ 0)
    (h : ∃ μ : ℂ, (∃ k : ℕ, ((T - μ • 1) ^ k) a = 0) ∧ ∃ k : ℕ, ((T - μ • 1) ^ k) w = 0) :
    w ∈ T.maxGenEigenspace c := by
  obtain ⟨μ, ⟨k, hk⟩, ⟨l, hl⟩⟩ := h
  obtain rfl := eq_of_genEigen_of_eigen T a c μ ha ha0 k hk
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨l, hl⟩

/-- Cancellation of a nonzero vector. -/
theorem smul_cancel_of_ne_zero (a : W) (ha0 : a ≠ 0) (μ ν : ℂ) (h : μ • a = ν • a) : μ = ν := by
  have h' : (μ - ν) • a = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h'' | h''
  · exact sub_eq_zero.mp h''
  · exact absurd h'' ha0

end Generic

section Product

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- Powers of a shifted product operator act componentwise. -/
theorem prodMap_sub_smul_pow_apply (f : Module.End ℂ X) (g : Module.End ℂ Y) (c : ℂ) (k : ℕ)
    (v : X × Y) :
    (((f.prodMap g) - c • 1) ^ k) v = (((f - c • 1) ^ k) v.1, ((g - c • 1) ^ k) v.2) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, pow_succ, Module.End.mul_apply,
      Module.End.mul_apply]
    rfl

end Product

variable {n : ℕ}

/-- Separation of the associate pair is equivalent to the existence of an isotypical projection
inside the away-three Hecke algebra. -/
theorem eigenSeparated_iff_exists_mem (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) ↔
      ∃ p ∈ awayThreeHeckeAlgebra D hecke, IsIsotypicalProjection D hecke p := by
  constructor
  · intro hsep
    have h := spectral_of_eigenSeparated D hecke hhecke hsep
    exact ⟨h.choose, h.choose_spec.1,
      TernaryPeriodPolynomials.HeckeCommutativity.isIsotypicalProjection_of_mem_awayThree
        D hecke hhecke h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2⟩
  · intro h
    exact eigenSeparated_of_mem _ _ h.choose h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.1

/-- **Necessity.** Existence of an isotypical projection (the content of
`cuspidal_associate_projector`) together with membership of every isotypical projection in the
away-three algebra (the content of `associate_projector_away_three_algebra`) implies separation. -/
theorem eigenSeparated_of_projector_targets (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hex : ∃ p, IsIsotypicalProjection D hecke p)
    (hmem : ∀ p, IsIsotypicalProjection D hecke p → p ∈ awayThreeHeckeAlgebra D hecke) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  exact eigenSeparated_of_mem _ _ hex.choose (hmem _ hex.choose_spec) hex.choose_spec.1
    hex.choose_spec.2.1

/-- Separation is vacuous for a zero associate pair. -/
theorem eigenSeparated_of_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hbot : associatePair D = ⊥) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  intro a w ha ha0
  rw [hbot, Submodule.mem_bot] at ha
  exact absurd ha ha0

end TernaryPeriodPolynomials.Spectral
