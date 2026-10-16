module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Basic

@[expose] public section


/-!
# Equivariant lifting from free permutation modules

A map out of a permutation module on a free `Λ`-set whose values on basis chains lie in the range
of an equivariant map `d` lifts through `d` by an equivariant map: choose orbit representatives,
lift on the representatives, and translate.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

/-- Equivariant lifting from a free permutation module: a map whose basis values lie in the range
of `d` lifts through `d`. -/
theorem exists_equivariant_lift {Λ : Type} [Group Λ] {S T U : Type}
    [MulAction Λ S] [MulAction Λ T] [MulAction Λ U]
    (free : ∀ (γ : Λ) (s : S), γ • s = s → γ = 1)
    (F : (S →₀ ℂ) →ₗ[ℂ] (U →₀ ℂ)) (hF : Equivariant Λ F)
    (d : (T →₀ ℂ) →ₗ[ℂ] (U →₀ ℂ)) (hd : Equivariant Λ d)
    (range : ∀ s : S, F (Finsupp.single s 1) ∈ LinearMap.range d) :
    ∃ L : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ), Equivariant Λ L ∧ d ∘ₗ L = F := by
  classical
  obtain ⟨rep, hrep, hrep_smul⟩ : ∃ rep : S → S, (∀ s, ∃ g : Λ, g • rep s = s) ∧
      ∀ (γ : Λ) (s : S), rep (γ • s) = rep s := by
    refine ⟨fun s => (Quotient.mk (MulAction.orbitRel Λ S) s).out, fun s => ?_, fun γ s => ?_⟩
    · obtain ⟨h, hh⟩ : (Quotient.mk (MulAction.orbitRel Λ S) s).out ∈ MulAction.orbit Λ s :=
        MulAction.orbitRel_apply.1 (@Quotient.mk_out _ (MulAction.orbitRel Λ S) s)
      refine ⟨h⁻¹, ?_⟩
      show h⁻¹ • (Quotient.mk (MulAction.orbitRel Λ S) s).out = s
      rw [← hh, inv_smul_smul]
    · exact congrArg Quotient.out
        (Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit s γ)))
  choose g hg using hrep
  have hg_smul : ∀ (γ : Λ) (s : S), g (γ • s) = γ * g s := by
    intro γ s
    have h0 : g (γ • s) • rep (γ • s) = γ • s := hg (γ • s)
    rw [hrep_smul γ s] at h0
    have h1 : g (γ • s) • rep s = (γ * g s) • rep s := by
      rw [h0, mul_smul, hg s]
    have h2 : ((g (γ • s))⁻¹ * (γ * g s)) • rep s = rep s := by
      rw [mul_smul, ← h1, inv_smul_smul]
    exact inv_mul_eq_one.1 (free _ (rep s) h2)
  have hex : ∀ r : S, ∃ y : T →₀ ℂ, d y = F (Finsupp.single r 1) := fun r =>
    LinearMap.mem_range.1 (range r)
  choose t ht using hex
  refine ⟨Finsupp.linearCombination ℂ (fun s => chainAct Λ (g s) (t (rep s))), ?_, ?_⟩
  · apply equivariant_of_single
    intro γ s
    simp only [Finsupp.linearCombination_single, one_smul, hg_smul, hrep_smul, chainAct_mul,
      LinearMap.comp_apply]
  · apply Finsupp.lhom_ext
    intro s a
    have key : d (chainAct Λ (g s) (t (rep s))) = F (Finsupp.single s 1) := by
      rw [hd.apply, ht, ← hF.apply, chainAct_single, hg]
    have hs : Finsupp.single s a = a • Finsupp.single s (1 : ℂ) := by simp
    rw [hs]
    simp only [LinearMap.comp_apply, map_smul, Finsupp.linearCombination_single, one_smul, key]

end TernaryPeriodPolynomials.TopVanishing
