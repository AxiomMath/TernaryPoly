module

public import Mathlib

@[expose] public section


/-!
# Functionals on a finite product, and on a space of dimension `≤ 1`

Formalized by Claude Sonnet 5.5.  Formal steps of the decomposition of the corner functional over the flag orbits:
a linear functional on `∏_f M_f` is the sum of its restrictions `φ ∘ Pi.single f` (`pi_functional_decomp`), and a functional on a space of dimension `≤ 1` is a multiple of any
nonzero functional (`functional_eq_smul`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

theorem pi_functional_decomp {I : Type} [Fintype I] [DecidableEq I] {M : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℚ (M i)] (φ : (∀ i, M i) →ₗ[ℚ] ℚ) (m : ∀ i, M i) :
    φ m = ∑ i, φ (Pi.single i (m i)) := by
  conv_lhs => rw [← Finset.univ_sum_single m]
  rw [map_sum]

theorem functional_eq_smul {M : Type} [AddCommGroup M] [Module ℚ M] [Module.Finite ℚ M] (h : Module.finrank ℚ M ≤ 1)
    (l φ : M →ₗ[ℚ] ℚ) (hl : l ≠ 0) : ∃ c : ℚ, φ = c • l := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h
  by_cases h0 : l v = 0
  · exfalso
    apply hl
    ext w
    obtain ⟨a, rfl⟩ := hv w
    simp [h0]
  · refine ⟨φ v / l v, ?_⟩
    ext w
    obtain ⟨a, rfl⟩ := hv w
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
