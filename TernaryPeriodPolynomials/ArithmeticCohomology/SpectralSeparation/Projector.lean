module

public import Mathlib

@[expose] public section


/-!
# Spectral projectors in a commutative algebra of endomorphisms

Let `𝒜` be a commutative subalgebra of `End(W)`, `W` finite dimensional over `ℂ`,
and `A ≤ W` an `𝒜`-stable subspace. Suppose `A` is closed under the eigencharacter
separation property: whenever `w` and a nonzero `a ∈ A` share a simultaneous
generalized eigenvalue for every element of `𝒜`, then `w ∈ A`. Then some idempotent
of `𝒜` has range exactly `A` and is the identity on `A`.

The proof is elementary linear algebra:
* single-operator spectral projectors are polynomials obtained from a Bezout identity;
* products over a finite spanning family give simultaneous spectral projectors;
* nilpotency of commuting sums in the quotient by an annihilator ideal.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open Polynomial Module

namespace TernaryPeriodPolynomials.SpectralSeparation

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
theorem aeval_X_sub_C_pow (f : Module.End ℂ W) (μ : ℂ) (k : ℕ) :
    aeval f ((X - C μ) ^ k) = (f - μ • 1) ^ k := by
  simp [Algebra.algebraMap_eq_smul_one]

omit [FiniteDimensional ℂ W] in
theorem commute_aeval (f : Module.End ℂ W) (p : ℂ[X]) : Commute f (aeval f p) := by
  have h := (Commute.all (X : ℂ[X]) p).map (aeval f)
  simpa using h

/-- A polynomial in `f` that is the spectral projector of `f` at `μ`. -/
theorem exists_spectral_poly (f : Module.End ℂ W) (μ : ℂ) :
    ∃ P : ℂ[X], (∀ w, aeval f P w ∈ f.maxGenEigenspace μ) ∧
      (∀ w ∈ f.maxGenEigenspace μ, aeval f P w = w) ∧
      (∀ ν, ν ≠ μ → ∀ w ∈ f.maxGenEigenspace ν, aeval f P w = 0) := by
  set N := Module.finrank ℂ W
  set χ := LinearMap.charpoly f
  set r := rootMultiplicity μ χ
  set q := χ /ₘ (X - C μ) ^ r
  have hχ : χ ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  have hq : eval μ q ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero μ hχ
  have hfac : (X - C μ) ^ r * q = χ := pow_mul_divByMonic_rootMultiplicity_eq χ μ
  have hCH : aeval f χ = 0 := LinearMap.aeval_self_charpoly f
  have hrN : r ≤ N := by
    have h := LinearMap.finrank_maxGenEigenspace_eq f μ
    show rootMultiplicity μ (LinearMap.charpoly f) ≤ Module.finrank ℂ W
    rw [← h]
    exact Submodule.finrank_le _
  have hcop : IsCoprime ((X - C μ) ^ N) q := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C μ).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hq
  obtain ⟨u, v, huv⟩ := hcop
  have hkill : ∀ w, ((f - μ • 1) ^ r) (aeval f q w) = 0 := by
    intro w
    rw [← aeval_X_sub_C_pow, ← Module.End.mul_apply, ← map_mul, hfac, hCH]
    rfl
  have hone : aeval f u * (f - μ • 1) ^ N + aeval f v * aeval f q = 1 := by
    rw [← aeval_X_sub_C_pow, ← map_mul, ← map_mul, ← map_add, huv, map_one]
  refine ⟨v * q, ?_, ?_, ?_⟩
  · intro w
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨r, ?_⟩
    rw [map_mul, Module.End.mul_apply]
    have hc : Commute ((f - μ • 1) ^ r) (aeval f v) := by
      rw [← aeval_X_sub_C_pow]
      exact (Commute.all _ _).map (aeval f)
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hkill, map_zero]
  · intro w hw
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hw
    have hw' : ((f - μ • 1) ^ N) w = 0 := hw
    have h := congrArg (fun T : Module.End ℂ W => T w) hone
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at h
    rw [hw', map_zero, zero_add] at h
    rw [map_mul, Module.End.mul_apply]
    exact h
  · intro ν hν w hw
    set y := aeval f q w
    have hyν : y ∈ f.maxGenEigenspace ν :=
      Module.End.mapsTo_maxGenEigenspace_of_comm (commute_aeval f q) ν hw
    have hyμ : y ∈ f.maxGenEigenspace μ := by
      rw [Module.End.mem_maxGenEigenspace]
      exact ⟨r, hkill w⟩
    have hdisj : Disjoint (f.maxGenEigenspace ν) (f.maxGenEigenspace μ) :=
      (Module.End.independent_maxGenEigenspace f).pairwiseDisjoint hν
    have hy : y = 0 := by
      have hmem : y ∈ f.maxGenEigenspace ν ⊓ f.maxGenEigenspace μ := ⟨hyν, hyμ⟩
      rw [hdisj.eq_bot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    rw [map_mul, Module.End.mul_apply]
    change aeval f v y = 0
    rw [hy, map_zero]

/-- The chosen spectral polynomial. -/
def spectralPoly (f : Module.End ℂ W) (μ : ℂ) : ℂ[X] := (exists_spectral_poly f μ).choose

theorem spectralPoly_mem (f : Module.End ℂ W) (μ : ℂ) (w : W) :
    aeval f (spectralPoly f μ) w ∈ f.maxGenEigenspace μ :=
  (exists_spectral_poly f μ).choose_spec.1 w

theorem spectralPoly_id (f : Module.End ℂ W) (μ : ℂ) {w : W} (hw : w ∈ f.maxGenEigenspace μ) :
    aeval f (spectralPoly f μ) w = w :=
  (exists_spectral_poly f μ).choose_spec.2.1 w hw

theorem spectralPoly_zero (f : Module.End ℂ W) {μ ν : ℂ} (h : ν ≠ μ) {w : W}
    (hw : w ∈ f.maxGenEigenspace ν) : aeval f (spectralPoly f μ) w = 0 :=
  (exists_spectral_poly f μ).choose_spec.2.2 ν h w hw

theorem maxGenEigenspace_eq_bot_of_not_root (f : Module.End ℂ W) {ν : ℂ}
    (hν : ν ∉ (LinearMap.charpoly f).roots.toFinset) : f.maxGenEigenspace ν = ⊥ := by
  have hχ : LinearMap.charpoly f ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  have hroot : ¬ (LinearMap.charpoly f).IsRoot ν := by
    intro h
    exact hν (Multiset.mem_toFinset.mpr ((mem_roots hχ).mpr h))
  have h0 : rootMultiplicity ν (LinearMap.charpoly f) = 0 := rootMultiplicity_eq_zero hroot
  rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq, h0]

/-- The spectral projectors of a single operator sum to the identity. -/
theorem sum_spectralPoly (f : Module.End ℂ W) :
    ∑ μ ∈ (LinearMap.charpoly f).roots.toFinset, aeval f (spectralPoly f μ) = 1 := by
  classical
  apply LinearMap.ext
  intro w
  have hw : w ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; exact Submodule.mem_top
  rw [LinearMap.sum_apply, Module.End.one_apply]
  induction hw using Submodule.iSup_induction' with
  | mem ν x hx =>
    by_cases hν : ν ∈ (LinearMap.charpoly f).roots.toFinset
    · rw [Finset.sum_eq_single ν]
      · exact spectralPoly_id f ν hx
      · intro μ _ hμ
        exact spectralPoly_zero f (Ne.symm hμ) hx
      · intro h; exact absurd hν h
    · rw [maxGenEigenspace_eq_bot_of_not_root f hν] at hx
      rw [(Submodule.mem_bot ℂ).mp hx]
      simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

end TernaryPeriodPolynomials.SpectralSeparation
