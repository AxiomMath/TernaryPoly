module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneThreeVanishing

@[expose] public section


/-!
# Multiplicity one away from three at level one

For a system of eigenvalues `λ_p` (`p ≠ 3`) the joint eigenspace
`{f ∈ S_k(SL₂ℤ) : T_p f = λ_p f for all primes p ≠ 3}` has dimension at most one
(`finrank_eigenspaceAwayThree_le_one`). Indeed, in that eigenspace `a_{pm} = λ_p a_m - p^{k-1} a_{m/p}`,
so a form with `a_1 = 0` has `a_n = 0` for every `n` prime to `3`, and vanishes by
`LevelOneThreeVanishing.eq_zero_of_coeff_coprime_three` (the elliptic-element argument). This is the
level-one case of strong multiplicity one with the single prime `3` removed.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open UpperHalfPlane
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.LevelOneMultiplicityOne

open LevelOneHecke

variable {k : ℤ}

/-- The joint eigenspace of the Hecke operators `T_p`, `p ≠ 3`, for eigenvalues `λ`. -/
def eigenspaceAwayThree (k : ℤ) (eigenvalues : Nat.Primes → ℂ) : Submodule ℂ (CuspForm levelOne k) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3}, Module.End.eigenspace (levelOneHecke k p.1) (eigenvalues p.1)

theorem mem_eigenspaceAwayThree {eigenvalues : Nat.Primes → ℂ} {f : CuspForm levelOne k} :
    f ∈ eigenspaceAwayThree k eigenvalues ↔
      ∀ p : Nat.Primes, p.val ≠ 3 → levelOneHecke k p f = eigenvalues p • f := by
  simp only [eigenspaceAwayThree, Submodule.mem_iInf, Subtype.forall, Module.End.mem_eigenspace_iff]

theorem coeff_smul (a : ℂ) (f : CuspForm levelOne k) (n : ℕ) :
    (qExpansion 1 ((a • f : CuspForm levelOne k) : ℍ → ℂ)).coeff n = a * (qExpansion 1 f).coeff n := by
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods,
    PowerSeries.coeff_smul, smul_eq_mul]

theorem coeff_add (f g : CuspForm levelOne k) (n : ℕ) :
    (qExpansion 1 ((f + g : CuspForm levelOne k) : ℍ → ℂ)).coeff n =
      (qExpansion 1 f).coeff n + (qExpansion 1 g).coeff n := by
  rw [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num : (0 : ℝ) < 1)
    one_mem_strictPeriods, map_add]

theorem coeff_sub (f g : CuspForm levelOne k) (n : ℕ) :
    (qExpansion 1 ((f - g : CuspForm levelOne k) : ℍ → ℂ)).coeff n =
      (qExpansion 1 f).coeff n - (qExpansion 1 g).coeff n := by
  have h : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h, coeff_add, coeff_smul]
  ring

/-- In the eigenspace, `a_1 = 0` forces `a_n = 0` for every `n` prime to `3`. -/
theorem coeff_eq_zero_of_first {eigenvalues : Nat.Primes → ℂ} {f : CuspForm levelOne k}
    (hf : f ∈ eigenspaceAwayThree k eigenvalues) (h1 : (qExpansion 1 f).coeff 1 = 0) :
    ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0 := by
  rw [mem_eigenspaceAwayThree] at hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h3
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact absurd (dvd_zero 3) h3
      · exact h1
    · set p := n.minFac with hp
      have hprime : p.Prime := Nat.minFac_prime (by omega)
      have hp3 : p ≠ 3 := by
        intro h
        apply h3
        rw [← h]
        exact Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm; omega
        · exact h0
      have hmlt : m < n := by
        rw [hm, ← hp]
        have := hprime.two_le
        nlinarith
      have hm3 : ¬ 3 ∣ m := fun h => h3 (hm ▸ Dvd.dvd.mul_left h _)
      let P : Nat.Primes := ⟨p, hprime⟩
      have hcoeff := levelOneHecke_coeff k P f m
      rw [hf P hp3, coeff_smul] at hcoeff
      have hmzero := ih m hmlt hm3
      have hdil : qSeriesDilateCoefficients (fun i => (qExpansion 1 f).coeff i) p m = 0 := by
        unfold qSeriesDilateCoefficients
        split_ifs with hpm
        · apply ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hmlt)
          exact fun h => hm3 (h.trans (Nat.div_dvd_of_dvd hpm))
        · rfl
      change eigenvalues P * (qExpansion 1 f).coeff m =
        (p : ℂ) ^ (k - 1) * qSeriesDilateCoefficients (fun i => (qExpansion 1 f).coeff i) p m +
          (qExpansion 1 f).coeff (p * m) at hcoeff
      rw [hmzero, hdil, mul_zero, mul_zero, zero_add] at hcoeff
      rw [hm, ← hp]
      exact hcoeff.symm

/-- **Multiplicity one away from three**: two forms of the joint eigenspace are proportional. -/
theorem proportional (hk : 0 < k) {eigenvalues : Nat.Primes → ℂ} {f g : CuspForm levelOne k}
    (hf : f ∈ eigenspaceAwayThree k eigenvalues) (hg : g ∈ eigenspaceAwayThree k eigenvalues) :
    (qExpansion 1 g).coeff 1 • f = (qExpansion 1 f).coeff 1 • g := by
  set h := (qExpansion 1 g).coeff 1 • f - (qExpansion 1 f).coeff 1 • g
  have hh : h ∈ eigenspaceAwayThree k eigenvalues :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg)
  have h1 : (qExpansion 1 h).coeff 1 = 0 := by
    rw [coeff_sub, coeff_smul, coeff_smul]
    ring
  have hzero := LevelOneThreeVanishing.eq_zero_of_coeff_coprime_three h hk
    (coeff_eq_zero_of_first hh h1)
  exact sub_eq_zero.mp hzero

/-- The joint eigenspace away from three has dimension at most one. -/
theorem finrank_eigenspaceAwayThree_le_one [FiniteDimensional ℂ (CuspForm levelOne k)]
    (hk : 0 < k) (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) ≤ 1 := by
  apply finrank_le_one_iff.mpr
  by_cases hex : ∃ f ∈ eigenspaceAwayThree k eigenvalues, (qExpansion 1 f).coeff 1 ≠ 0
  · obtain ⟨f, hf, hf1⟩ := hex
    refine ⟨⟨f, hf⟩, fun ⟨g, hg⟩ => ⟨(qExpansion 1 g).coeff 1 / (qExpansion 1 f).coeff 1, ?_⟩⟩
    apply Subtype.ext
    change ((qExpansion 1 g).coeff 1 / (qExpansion 1 f).coeff 1) • f = g
    have hprop := proportional hk hf hg
    rw [div_eq_mul_inv, mul_comm, mul_smul, hprop, smul_smul, inv_mul_cancel₀ hf1, one_smul]
  · push Not at hex
    refine ⟨0, fun ⟨g, hg⟩ => ⟨0, ?_⟩⟩
    apply Subtype.ext
    change (0 : ℂ) • (0 : CuspForm levelOne k) = g
    rw [smul_zero]
    exact (LevelOneThreeVanishing.eq_zero_of_coeff_coprime_three g hk
      (coeff_eq_zero_of_first hg (hex g hg))).symm

end TernaryPeriodPolynomials.Spectral.LevelOneMultiplicityOne
