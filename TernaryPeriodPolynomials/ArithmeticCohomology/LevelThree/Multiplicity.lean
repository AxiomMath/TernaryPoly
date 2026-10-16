module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.AtkinLehner
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneMultiplicityOne

@[expose] public section


/-!
# Multiplicity away from three at level three

For a system of eigenvalues `c_p` (`p ≠ 3` prime) let `W_c ⊆ S_k(Γ₁(3))` be the joint eigenspace
`{f : T_p f = c_p f for all primes p ≠ 3}` (`eigenspaceAwayThree`). On `W_c`
`a_{pm} = c_p a_m - χ_k(p) p^{k-1} a_{m/p}`, so a form with `a_1 = 0` has `a_n = 0` for every `n`
prime to `3` (`coeff_eq_zero_of_first`). By the Atkin–Lehner lemma `f = g(3τ)` for a level-one cusp
form `g`, which lies in the level-one joint eigenspace with the same eigenvalues
(`exists_levelOne_eigen`), of dimension at most one (`LevelOneMultiplicityOne`). Hence
`dim W_c ≤ 2` (`finrank_eigenspaceAwayThree_le_two`) and, for odd weight, `dim W_c ≤ 1`
(`finrank_eigenspaceAwayThree_le_one_of_odd`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open UpperHalfPlane
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeMultiplicity

open TernaryPeriodPolynomials
open LevelThreeHeckeSum LevelThreeHeckeCosets LevelThreeAtkinLehnerEmbed LevelThreeAtkinLehner
open LevelThreeHecke

variable {k : ℤ}

/-- The joint eigenspace of the Hecke operators `T_p`, `p ≠ 3`, on `S_k(Γ₁(3))`. -/
def eigenspaceAwayThree (k : ℤ) (eigenvalues : Nat.Primes → ℂ) :
    Submodule ℂ (CuspForm levelThree k) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3},
    Module.End.eigenspace (levelThreeHecke k p.1 p.2) (eigenvalues p.1)

theorem mem_eigenspaceAwayThree {eigenvalues : Nat.Primes → ℂ} {f : CuspForm levelThree k} :
    f ∈ eigenspaceAwayThree k eigenvalues ↔
      ∀ (p : Nat.Primes) (hp : p.val ≠ 3), levelThreeHecke k p hp f = eigenvalues p • f := by
  simp only [eigenspaceAwayThree, Submodule.mem_iInf, Subtype.forall,
    Module.End.mem_eigenspace_iff]

theorem levelThreeChar_of_even (hk : Even k) (p : ℕ) : levelThreeChar k p = 1 := by
  unfold levelThreeChar
  split_ifs
  · exact hk.neg_one_zpow
  · rfl

theorem dilate_const_mul (a : ℂ) (b : ℕ → ℂ) (p n : ℕ) :
    qSeriesDilateCoefficients (fun m => a * b m) p n = a * qSeriesDilateCoefficients b p n := by
  unfold qSeriesDilateCoefficients
  split_ifs <;> simp

/-- In the joint eigenspace, `a_1 = 0` forces `a_n = 0` for every `n` prime to `3`. -/
theorem coeff_eq_zero_of_first {eigenvalues : Nat.Primes → ℂ} {f : CuspForm levelThree k}
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
      have hcoeff := levelThreeHecke_coeff P hp3 f m
      rw [hf P hp3, coeff_smul] at hcoeff
      have hmzero := ih m hmlt hm3
      have hdil : qSeriesDilateCoefficients (fun i => (qExpansion 1 f).coeff i) p m = 0 := by
        unfold qSeriesDilateCoefficients
        split_ifs with hpm
        · apply ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hmlt)
          exact fun h => hm3 (h.trans (Nat.div_dvd_of_dvd hpm))
        · rfl
      change eigenvalues P * (qExpansion 1 f).coeff m = levelThreeChar k p * (p : ℂ) ^ (k - 1) *
        qSeriesDilateCoefficients (fun i => (qExpansion 1 f).coeff i) p m +
          (qExpansion 1 f).coeff (p * m) at hcoeff
      rw [hmzero, hdil, mul_zero, mul_zero, zero_add] at hcoeff
      rw [hm, ← hp]
      exact hcoeff.symm

/-- The `a_1` coefficient as a linear functional on `S_k(Γ₁(3))`. -/
def coeffOne (k : ℤ) : CuspForm levelThree k →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 f).coeff 1
  map_add' f g := coeff_add f g 1
  map_smul' a f := coeff_smul a f 1

theorem eigen_aux (b A : ℕ → ℂ) (hA : ∀ m, A (3 * m) = (3 : ℂ) ^ (k - 1) * b m)
    (p : Nat.Primes) (hp : p.val ≠ 3) (c : ℂ) (n : ℕ)
    (h : c * A (3 * n) = 1 * (p.val : ℂ) ^ (k - 1) * qSeriesDilateCoefficients A p.val (3 * n) +
      A (p.val * (3 * n))) :
    (p.val : ℂ) ^ (k - 1) * qSeriesDilateCoefficients b p.val n + b (p.val * n) = c * b n := by
  have hAfun : (fun m => A (3 * m)) = fun m => (3 : ℂ) ^ (k - 1) * b m := funext hA
  have hdil : qSeriesDilateCoefficients A p.val (3 * n) =
      (3 : ℂ) ^ (k - 1) * qSeriesDilateCoefficients b p.val n := by
    rw [← Spectral.LevelOneHecke.dilate_comp_mul p.property Nat.prime_three hp A n,
      hAfun, dilate_const_mul]
  rw [hdil, hA, show p.val * (3 * n) = 3 * (p.val * n) by ring, hA] at h
  have h3 : (3 : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ h3
  linear_combination (-1 : ℂ) * h

/-- If `ι g` is in the joint eigenspace then `g` is in the level-one joint eigenspace
(same eigenvalues), for even weight. -/
theorem mem_levelOne_of_mem {eigenvalues : Nat.Primes → ℂ} (hk : Even k)
    {g : CuspForm Spectral.LevelOneHecke.levelOne k}
    (hf : levelOneToThree k g ∈ eigenspaceAwayThree k eigenvalues) :
    g ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues := by
  rw [mem_eigenspaceAwayThree] at hf
  rw [Spectral.LevelOneMultiplicityOne.mem_eigenspaceAwayThree]
  intro p hp
  apply Spectral.LevelOneHecke.cuspForm_ext_coeff
  intro n
  rw [Spectral.LevelOneHecke.levelOneHecke_coeff,
    Spectral.LevelOneMultiplicityOne.coeff_smul]
  have h := levelThreeHecke_coeff p hp (levelOneToThree k g) (3 * n)
  rw [hf p hp, coeff_smul, levelThreeChar_of_even hk] at h
  exact eigen_aux (fun m => (qExpansion 1 g).coeff m)
    (fun m => (qExpansion 1 (levelOneToThree k g)).coeff m)
    (fun m => levelOneToThree_coeff_mul g m) p hp (eigenvalues p) n h

/-- Atkin–Lehner for the joint eigenspace: a form of `W_c` with `a_1 = 0` is the image of a level-one
form of the level-one joint eigenspace (with the same eigenvalues) under `g ↦ g(3τ)`. -/
theorem exists_levelOne_eigen {eigenvalues : Nat.Primes → ℂ} {f : CuspForm levelThree k}
    (hf : f ∈ eigenspaceAwayThree k eigenvalues) (h1 : (qExpansion 1 f).coeff 1 = 0) :
    ∃ g ∈ Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues,
      levelOneToThree k g = f := by
  obtain ⟨g, hg⟩ := atkinLehner_three f (coeff_eq_zero_of_first hf h1)
  by_cases hk : Even k
  · exact ⟨g, mem_levelOne_of_mem hk (hg ▸ hf), hg⟩
  · have hodd : Odd k := Int.not_even_iff_odd.mp hk
    have hg0 : g = 0 := eq_zero_of_odd g hodd
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [← hg, hg0]

/-- **Multiplicity at most two away from three.** The joint eigenspace of `T_p` (`p ≠ 3`) on
`S_k(Γ₁(3))` has dimension at most two (for `k > 0`, given finite-dimensionality of the level-one
space). -/
theorem finrank_eigenspaceAwayThree_le_two
    [FiniteDimensional ℂ (CuspForm Spectral.LevelOneHecke.levelOne k)]
    (hk : 0 < k) (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) ≤ 2 := by
  by_cases hfin : Module.Finite ℂ (eigenspaceAwayThree k eigenvalues)
  swap
  · rw [Module.finrank_of_not_finite hfin]
    norm_num
  set W := eigenspaceAwayThree k eigenvalues with hW
  set E := Spectral.LevelOneMultiplicityOne.eigenspaceAwayThree k eigenvalues with hE
  let φ : W →ₗ[ℂ] ℂ := coeffOne k ∘ₗ W.subtype
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
    calc Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ ℂ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℂ
  let ι' : E →ₗ[ℂ] CuspForm levelThree k := levelOneToThree k ∘ₗ E.subtype
  have hmem : ∀ x : LinearMap.ker φ, (x.1 : CuspForm levelThree k) ∈ LinearMap.range ι' := by
    intro x
    obtain ⟨g, hg, hgx⟩ := exists_levelOne_eigen x.1.2 (LinearMap.mem_ker.mp x.2)
    exact ⟨⟨g, hg⟩, hgx⟩
  let j : LinearMap.ker φ →ₗ[ℂ] LinearMap.range ι' :=
    LinearMap.codRestrict (LinearMap.range ι') (W.subtype ∘ₗ (LinearMap.ker φ).subtype) hmem
  have hj : Function.Injective j := by
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hker : Module.finrank ℂ (LinearMap.ker φ) ≤ 1 := by
    calc Module.finrank ℂ (LinearMap.ker φ) ≤ Module.finrank ℂ (LinearMap.range ι') :=
          LinearMap.finrank_le_finrank_of_injective hj
      _ ≤ Module.finrank ℂ E := LinearMap.finrank_range_le _
      _ ≤ 1 := Spectral.LevelOneMultiplicityOne.finrank_eigenspaceAwayThree_le_one hk
        eigenvalues
  have hnull := LinearMap.finrank_range_add_finrank_ker φ
  omega

/-- For odd weight the joint eigenspace away from three has dimension at most one. -/
theorem finrank_eigenspaceAwayThree_le_one_of_odd (hk : Odd k) (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (eigenspaceAwayThree k eigenvalues) ≤ 1 := by
  by_cases hfin : Module.Finite ℂ (eigenspaceAwayThree k eigenvalues)
  swap
  · rw [Module.finrank_of_not_finite hfin]
    norm_num
  set W := eigenspaceAwayThree k eigenvalues with hW
  let φ : W →ₗ[ℂ] ℂ := coeffOne k ∘ₗ W.subtype
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
    calc Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ ℂ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℂ
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply atkinLehner_three_odd hk
    exact coeff_eq_zero_of_first x.2 hx
  have hnull := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, finrank_bot] at hnull
  omega

end TernaryPeriodPolynomials.LevelThree.LevelThreeMultiplicity
