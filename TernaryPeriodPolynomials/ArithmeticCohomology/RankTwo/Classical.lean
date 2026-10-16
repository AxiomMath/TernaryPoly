module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointGen
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Semisimple

@[expose] public section


/-!
# A two-dimensional eigenspace at level three contains an oldform

Let `W_c ⊆ S_k(Γ₁(3))` be the joint eigenspace of the Hecke operators `T_p`, `p ≠ 3`, for the
system of eigenvalues `c`. The coefficient `a_1` is a linear functional on `W_c`, and by the
Atkin–Lehner lemma at three every form of its kernel is `g(3τ)` for a level-one cusp form `g` in the
level-one joint eigenspace with the same eigenvalues
(`LevelThreeMultiplicity.exists_levelOne_eigen`). Hence if `dim W_c = 2` there is a nonzero level-one cusp eigenform with the eigenvalues `c`
(`exists_levelOne_of_finrank_eigenspace_two`), and the weight is even
(`even_of_finrank_eigenspace_two`). By Petersson semisimplicity the same holds for the joint
generalized eigenspace (`exists_levelOne_of_finrank_jointGen_two`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm

namespace TernaryPeriodPolynomials.RankTwo

open TernaryPeriodPolynomials
open LevelThree
open LevelThree.LevelThreeHeckeSum LevelThree.LevelThreeMultiplicity
open LevelThree.LevelThreeAtkinLehnerEmbed

variable {k : ℤ}

/-- **A two-dimensional joint eigenspace away from three contains an oldform**: there is a nonzero
level-one cusp form with the same Hecke eigenvalues `T_p`, `p ≠ 3`. -/
theorem exists_levelOne_of_finrank_eigenspace_two {eigenvalues : Nat.Primes → ℂ}
    (h : Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) = 2) :
    ∃ g : CuspForm Spectral.LevelOneHecke.levelOne k, g ≠ 0 ∧
      g ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues := by
  set W := eigenspaceAwayThree k eigenvalues
  have hfin : FiniteDimensional ℂ W := FiniteDimensional.of_finrank_pos (by omega)
  let φ : W →ₗ[ℂ] ℂ := coeffOne k ∘ₗ W.subtype
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
    calc Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ ℂ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℂ
  have hnull := LinearMap.finrank_range_add_finrank_ker φ
  have hker : LinearMap.ker φ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hnull
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  obtain ⟨g, hg, hgx⟩ := exists_levelOne_eigen x.2 (LinearMap.mem_ker.mp hx)
  refine ⟨g, ?_, hg⟩
  rintro rfl
  exact hx0 (Subtype.ext (hgx.symm.trans (map_zero _)))

/-- A two-dimensional joint eigenspace away from three only occurs in even weight. -/
theorem even_of_finrank_eigenspace_two {eigenvalues : Nat.Primes → ℂ}
    (h : Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) = 2) : Even k := by
  by_contra hk
  have h1 := finrank_eigenspaceAwayThree_le_one_of_odd (Int.not_even_iff_odd.mp hk) eigenvalues
  omega

/-- The joint generalized eigenspace and the joint eigenspace away from three have the same
dimension (Petersson semisimplicity). -/
theorem finrank_eigenspace_eq_jointGen (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) =
      Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace k eigenvalues) := by
  rw [LevelThreeJointGen.jointGen_eq_eigenspaceAwayThree (k := k)
    (LevelThreePeterssonSemisimple.levelThree_semisimple k) eigenvalues]

/-- **A two-dimensional joint generalized eigenspace away from three contains an oldform**, and
the weight is even. -/
theorem exists_levelOne_of_finrank_jointGen_two {eigenvalues : Nat.Primes → ℂ}
    (h : Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace k eigenvalues) = 2) :
    Even k ∧ ∃ g : CuspForm Spectral.LevelOneHecke.levelOne k, g ≠ 0 ∧
      g ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues := by
  rw [← finrank_eigenspace_eq_jointGen] at h
  exact ⟨even_of_finrank_eigenspace_two h, exists_levelOne_of_finrank_eigenspace_two h⟩

end TernaryPeriodPolynomials.RankTwo
