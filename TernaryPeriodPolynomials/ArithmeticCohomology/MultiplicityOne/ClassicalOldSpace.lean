module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.ClassicalTrace2
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Multiplicity

@[expose] public section


/-!
# Level-three eigenforms with vanishing traces are zero (old-space theorem)

Let `k > 0` be even, `f ≠ 0` a level-one eigenform away from `3` and `g ∈ S_k(Γ₁(3))` a joint
eigenform with the same eigenvalues. By multiplicity one (level one) and the Atkin-Lehner lemma,
`g = a · f + b · f(3τ)` (`exists_decomposition`). The Petersson products of `g` with `f` and
`f(3τ)` are `∫_𝒟 ⟨f, Tr g⟩` and `∫_𝒟 ⟨f, Tr (g ∣ W)⟩`; if both traces vanish, `⟨g, g⟩ = 0`, so
`g = 0` (`eq_zero_of_traceThree_eq_zero`).

Original work by AxiomCode.
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped ModularForm MatrixGroups Manifold

namespace TernaryPeriodPolynomials.MultiplicityOne.Classical

open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum (levelThree)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonForm
  (petThree petThree_sub_left petThree_smul_left petThree_self_eq_zero)
open TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehnerEmbed
  (levelOneToThree)

/-- The inclusion of level one maps the level-one eigenspace into the level-three one. -/
theorem restrictThree_mem {k : ℤ} (hk : Even k) {eigenvalues : Nat.Primes → ℂ}
    {f : CuspForm levelOne k}
    (hf : f ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues) :
    restrictThree k f ∈
      LevelThree.LevelThreeMultiplicity.eigenspaceAwayThree k eigenvalues := by
  rw [LevelThree.LevelThreeMultiplicity.mem_eigenspaceAwayThree]
  rw [Spectral.LevelOneMultiplicityOne.mem_eigenspaceAwayThree] at hf
  intro p hp
  apply LevelThree.LevelThreeHecke.cuspForm_ext_coeff
  intro n
  have h : (qExpansion 1 (Spectral.LevelOneHecke.levelOneHecke k p f)).coeff n =
      (qExpansion 1 ((eigenvalues p • f : CuspForm levelOne k) : ℍ → ℂ)).coeff n := by
    rw [hf p hp]
  rw [Spectral.LevelOneHecke.levelOneHecke_coeff,
    Spectral.LevelOneMultiplicityOne.coeff_smul] at h
  rw [LevelThree.LevelThreeHecke.levelThreeHecke_coeff,
    LevelThree.LevelThreeHecke.coeff_smul,
    LevelThree.LevelThreeMultiplicity.levelThreeChar_of_even hk, one_mul]
  exact h

/-- **Decomposition**: a level-three eigenform with the eigenvalues of a nonzero level-one
eigenform `f` is a combination of `f` and `f(3τ)`. -/
theorem exists_decomposition {k : ℤ} (hk : Even k) (hk0 : 0 < k) {eigenvalues : Nat.Primes → ℂ}
    {f : CuspForm levelOne k} (hf0 : f ≠ 0)
    (hf : f ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues)
    {g : CuspForm levelThree k}
    (hg : g ∈ LevelThree.LevelThreeMultiplicity.eigenspaceAwayThree k eigenvalues) :
    ∃ a b : ℂ, g = a • restrictThree k f + b • levelOneToThree k f := by
  have hc1 : (qExpansion 1 f).coeff 1 ≠ 0 := by
    intro h
    exact hf0 (Spectral.LevelOneThreeVanishing.eq_zero_of_coeff_coprime_three f hk0
      (Spectral.LevelOneMultiplicityOne.coeff_eq_zero_of_first hf h))
  have hR := restrictThree_mem hk hf
  have hg' : g - ((qExpansion 1 g).coeff 1 / (qExpansion 1 f).coeff 1) • restrictThree k f ∈
      LevelThree.LevelThreeMultiplicity.eigenspaceAwayThree k eigenvalues :=
    Submodule.sub_mem _ hg (Submodule.smul_mem _ _ hR)
  have h1 : (qExpansion 1 ((g - ((qExpansion 1 g).coeff 1 / (qExpansion 1 f).coeff 1) •
      restrictThree k f : CuspForm levelThree k) : ℍ → ℂ)).coeff 1 = 0 := by
    rw [LevelThree.LevelThreeHecke.coeff_sub,
      LevelThree.LevelThreeHecke.coeff_smul]
    change (qExpansion 1 g).coeff 1 - ((qExpansion 1 g).coeff 1 / (qExpansion 1 f).coeff 1) *
      (qExpansion 1 f).coeff 1 = 0
    rw [div_mul_cancel₀ _ hc1, sub_self]
  obtain ⟨h, hh, hhe⟩ := LevelThree.LevelThreeMultiplicity.exists_levelOne_eigen hg' h1
  have hprop := Spectral.LevelOneMultiplicityOne.proportional hk0 hf hh
  have hh' : h = ((qExpansion 1 h).coeff 1 / (qExpansion 1 f).coeff 1) • f := by
    rw [div_eq_inv_mul, mul_smul, hprop, smul_smul, inv_mul_cancel₀ hc1, one_smul]
  obtain ⟨B, hB⟩ : ∃ B : ℂ, h = B • f := ⟨_, hh'⟩
  refine ⟨(qExpansion 1 g).coeff 1 / (qExpansion 1 f).coeff 1, B, ?_⟩
  have hL : levelOneToThree k h = B • levelOneToThree k f := by
    rw [hB, map_smul]
  rw [← hL, hhe]
  abel

/-- **Old-space theorem at level `Γ₁(3)`.** A level-three joint eigenform with the eigenvalues
of a nonzero level-one eigenform `f`, whose traces `Tr g` and `Tr (g ∣ W)` to level one both
vanish, is zero. -/
theorem eq_zero_of_traceThree_eq_zero {k : ℤ} (hk : Even k) (hk0 : 0 < k)
    {eigenvalues : Nat.Primes → ℂ} {f : CuspForm levelOne k} (hf0 : f ≠ 0)
    (hf : f ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues)
    {g : CuspForm levelThree k}
    (hg : g ∈ LevelThree.LevelThreeMultiplicity.eigenspaceAwayThree k eigenvalues)
    (h1 : traceThree k hk g = 0) (h2 : traceThree k hk (atkinLehnerThree k g) = 0) : g = 0 := by
  obtain ⟨a, b, hab⟩ := exists_decomposition hk hk0 hf0 hf hg
  have hP1 : petThree k (restrictThree k f) g = 0 := by
    rw [petThree_restrict hk, h1]
    simp [petersson]
  have hP2 : petThree k (levelOneToThree k f) g = 0 := by
    rw [petThree_levelOneToThree hk, h2]
    simp [petersson]
  have hsub : g - a • restrictThree k f = b • levelOneToThree k f := by
    rw [hab]
    abel
  have h := petThree_sub_left k g (a • restrictThree k f) g
  rw [hsub, petThree_smul_left, petThree_smul_left, hP1, hP2] at h
  simp only [mul_zero, sub_zero] at h
  exact petThree_self_eq_zero k g h.symm

end TernaryPeriodPolynomials.MultiplicityOne.Classical
