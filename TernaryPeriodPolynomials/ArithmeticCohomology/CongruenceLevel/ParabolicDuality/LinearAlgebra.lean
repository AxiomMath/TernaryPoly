module

public import Mathlib

@[expose] public section

/-!
# Linear algebra for the cellular Poincaré duality: the annihilator of a kernel

Formalized by Claude Sonnet 5.5.

`exists_eq_of_perfect`: a perfect pairing of finite-dimensional complex spaces represents every functional.
`annihilator_ker_eq_range`: if `A : V → W` and `B : W' → V'` are adjoint up to a scalar for perfect pairings `V × V'`, `W × W'`
of finite-dimensional spaces, the annihilator of `ker A` in `V'` is `range B` (used for `ker d_c` against `coker δ'`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

section LinearAlgebra

variable {V V' W W' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- A perfect pairing of finite-dimensional spaces identifies the second space with the dual of the first. -/
theorem exists_eq_of_perfect [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] (p : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hl : ∀ v, (∀ v', p v v' = 0) → v = 0) (hr : ∀ v', (∀ v, p v v' = 0) → v' = 0)
    (lam0 : Module.Dual ℂ V) : ∃ v', ∀ v, p v v' = lam0 v := by
  have hinj : Function.Injective p.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v' h
    exact hr v' (fun v => by simpa using LinearMap.congr_fun h v)
  have hinj' : Function.Injective p := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v h
    exact hl v (fun v' => by simpa using LinearMap.congr_fun h v')
  have h1 : Module.finrank ℂ V' ≤ Module.finrank ℂ (Module.Dual ℂ V) := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℂ V ≤ Module.finrank ℂ (Module.Dual ℂ V') := LinearMap.finrank_le_finrank_of_injective hinj'
  rw [Subspace.dual_finrank_eq] at h1 h2
  have hsurj : Function.Surjective p.flip := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj, Subspace.dual_finrank_eq]
    omega
  obtain ⟨v', hv'⟩ := hsurj lam0
  exact ⟨v', fun v => by simpa using LinearMap.congr_fun hv' v⟩

/-- **Annihilator of a kernel**: for a map `A : V → W` and the adjoint `B : W' → V'` (up to a nonzero scalar `c`) with respect to
perfect pairings of finite-dimensional spaces, the annihilator of `ker A` in `V'` is `range B`. -/
theorem annihilator_ker_eq_range [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ W']
    (pV : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hVr : ∀ v', (∀ v, pV v v' = 0) → v' = 0)
    (pW : W →ₗ[ℂ] W' →ₗ[ℂ] ℂ) (hWl : ∀ w, (∀ w', pW w w' = 0) → w = 0) (hWr : ∀ w', (∀ w, pW w w' = 0) → w' = 0)
    (A : V →ₗ[ℂ] W) (B : W' →ₗ[ℂ] V') (c : ℂ)
    (hAB : ∀ v w', pW (A v) w' = c * pV v (B w')) (v' : V')
    (h : ∀ v ∈ LinearMap.ker A, pV v v' = 0) : v' ∈ LinearMap.range B := by
  have hmem : (pV.flip v') ∈ (LinearMap.ker A).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    exact h v hv
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨lam, hlam⟩ := hmem
  obtain ⟨w', hw'⟩ := exists_eq_of_perfect pW hWl hWr lam
  refine ⟨c • w', ?_⟩
  apply sub_eq_zero.mp
  apply hVr
  intro v
  have e1 : pV v v' = lam (A v) := by
    have := LinearMap.congr_fun hlam v
    simpa using this.symm
  have e2 : lam (A v) = pW (A v) w' := (hw' (A v)).symm
  have e3 := hAB v w'
  have : pV v v' = c * pV v (B w') := by rw [e1, e2, e3]
  rw [map_sub, map_smul, map_smul, this, smul_eq_mul]
  ring

end LinearAlgebra

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
