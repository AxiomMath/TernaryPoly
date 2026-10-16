module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Multiplicity

@[expose] public section


/-!
# Multiplicity at most two away from three, unconditionally

The hypothesis `FiniteDimensional ℂ S_k(SL₂ℤ)` of `finrank_eigenspaceAwayThree_le_two` is
discharged from Mathlib's dimension formula for level-one modular forms (even weight), and is not
needed in odd weight, so for every `k > 0` the joint eigenspace of the Hecke operators `T_p`
(`p ≠ 3`) on `S_k(Γ₁(3))` has dimension at most two.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeMultiplicityFinal

open LevelThreeMultiplicity

theorem cuspForm_levelOne_finiteDimensional (n : ℕ) (hn : Even n) :
    FiniteDimensional ℂ (CuspForm Spectral.LevelOneHecke.levelOne (n : ℤ)) := by
  have hrank := ModularForm.dimension_level_one n hn
  have hlt : Module.rank ℂ (ModularForm Spectral.LevelOneHecke.levelOne (n : ℤ)) <
      Cardinal.aleph0 := by
    rw [hrank]
    exact Cardinal.natCast_lt_aleph0
  have : Module.Finite ℂ (ModularForm Spectral.LevelOneHecke.levelOne (n : ℤ)) :=
    Module.rank_lt_aleph0_iff.mp hlt
  exact FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- **Multiplicity at most two away from three** for every positive weight: the joint
eigenspace of `T_p` (`p ≠ 3` prime) on `S_k(Γ₁(3))` has dimension at most `2`. -/
theorem finrank_eigenspaceAwayThree_le_two_of_pos {k : ℤ} (hk : 0 < k)
    (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) ≤ 2 := by
  rcases Int.even_or_odd k with he | ho
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    have := cuspForm_levelOne_finiteDimensional n ((Int.even_coe_nat n).mp he)
    exact finrank_eigenspaceAwayThree_le_two hk eigenvalues
  · have := finrank_eigenspaceAwayThree_le_one_of_odd ho eigenvalues
    omega

end TernaryPeriodPolynomials.LevelThree.LevelThreeMultiplicityFinal
