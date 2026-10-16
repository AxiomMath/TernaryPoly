module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Duality

@[expose] public section


/-!
# Annihilators for perfect pairings and the duality of a cusp stabilizer

Formalized by Claude Sonnet 5.5.

* `perp p S`: the annihilator in `V'` of a subspace `S ≤ V` for a pairing `p : V × V' → ℂ`; for a perfect pairing of finite-dimensional
  spaces `finrank_perp : dim S^⊥ + dim S = dim V` and `mem_of_perp_perp : S^⊥⊥ = S`.
* `exists_coboundary_of_orth`: for a perfect `σ`-invariant pairing, `u' ∈ E'` orthogonal to the fixed vectors `E^σ` is in `(σ - 1) E'`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open Module

section Perp

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (p : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)

/-- The annihilator in `V'` of a subspace of `V`. -/
def perp (S : Submodule ℂ V) : Submodule ℂ V' := S.dualAnnihilator.comap p.flip

theorem mem_perp {S : Submodule ℂ V} {v' : V'} : v' ∈ perp p S ↔ ∀ s ∈ S, p s v' = 0 := by
  unfold perp
  rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  rfl

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']
  (hl : ∀ v, (∀ v', p v v' = 0) → v = 0) (hr : ∀ v', (∀ v, p v v' = 0) → v' = 0)

include hl hr in
/-- A perfect pairing of finite-dimensional spaces identifies `V'` with the dual of `V`. -/
theorem perfect_bijective : Function.Bijective p.flip := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v' h
    exact hr v' (fun v => by simpa using LinearMap.congr_fun h v)
  · intro lam
    obtain ⟨v', hv'⟩ := exists_eq_of_perfect p hl hr lam
    exact ⟨v', LinearMap.ext fun v => by simpa using hv' v⟩

include hl hr in
theorem finrank_perp (S : Submodule ℂ V) : finrank ℂ (perp p S) + finrank ℂ S = finrank ℂ V := by
  let e : V' ≃ₗ[ℂ] Module.Dual ℂ V := LinearEquiv.ofBijective p.flip (perfect_bijective p hl hr)
  have h1 : perp p S = S.dualAnnihilator.comap e.toLinearMap := rfl
  have h2 : finrank ℂ (perp p S) = finrank ℂ S.dualAnnihilator := by
    rw [h1, Submodule.comap_equiv_eq_map_symm]
    exact LinearEquiv.finrank_map_eq e.symm S.dualAnnihilator
  rw [h2, add_comm]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq S

include hl hr in
/-- Double annihilator: a vector orthogonal to `S^⊥` lies in `S`. -/
theorem mem_of_perp_perp (S : Submodule ℂ V) {v : V} (h : ∀ v' ∈ perp p S, p v v' = 0) : v ∈ S := by
  by_contra hv
  obtain ⟨f, hf, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  obtain ⟨v', hv'⟩ := (perfect_bijective p hl hr).2 f
  have hv'S : v' ∈ perp p S := by
    rw [mem_perp]
    intro s hs
    have : f s = 0 := by
      have := Submodule.mem_map_of_mem (f := f) hs
      rw [hfS] at this
      simpa using this
    rw [← this, ← hv']
    rfl
  apply hf
  rw [← hv']
  exact h v' hv'S

end Perp

section CuspDuality

variable {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  [FiniteDimensional ℂ E'] (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ)
  (hinv : ∀ (g : G) v w, e (ρ g v) (ρ' g w) = e v w) (hL : ∀ v, (∀ w, e v w = 0) → v = 0)
  (hR : ∀ w, (∀ v, e v w = 0) → w = 0)

include hinv hL hR in
/-- **Duality at a cusp.**  A vector `u'` orthogonal to the `σ`-fixed vectors of `E` is of the form `σ w - w`. -/
theorem exists_coboundary_of_orth [FiniteDimensional ℂ E] (σ : G) (u' : E')
    (h : ∀ v, ρ σ v = v → e v u' = 0) : ∃ w : E', u' = ρ' σ w - w := by
  by_contra hne
  have hnot : u' ∉ LinearMap.range (ρ' σ - 1) := by
    rintro ⟨w, hw⟩
    exact hne ⟨w, by simpa using hw.symm⟩
  obtain ⟨f, hf, hfR⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  obtain ⟨v, hv⟩ := exists_eq_of_perfect e.flip hR hL f
  have hfv : ∀ w, e v w = f w := fun w => by simpa using hv w
  have hfR' : ∀ w, f (ρ' σ w - w) = 0 := by
    intro w
    have : f (ρ' σ w - w) ∈ (LinearMap.range (ρ' σ - 1)).map f :=
      Submodule.mem_map_of_mem ⟨w, by simp⟩
    rw [hfR] at this
    simpa using this
  have hfix : ρ σ v = v := by
    apply sub_eq_zero.mp
    apply hL
    intro w'
    have hw : ρ' σ (ρ' σ⁻¹ w') = w' := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 := hinv σ v (ρ' σ⁻¹ w')
    rw [hw] at h1
    have h2 := hfR' (ρ' σ⁻¹ w')
    rw [hw, map_sub, ← hfv, ← hfv] at h2
    rw [map_sub, LinearMap.sub_apply, h1]
    linear_combination (-1 : ℂ) * h2
  exact hf (by rw [← hfv]; exact h v hfix)

end CuspDuality

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
