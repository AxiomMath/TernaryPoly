module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeCosets

@[expose] public section


/-!
# Hecke operators on cusp forms for `Γ₁(3)`

For a prime `p ≠ 3` and `f ∈ S_k(Γ₁(3))` (Mathlib's `CuspForm binaryRealGammaOneThree k`) put
`T_p f = ∑_{0 ≤ j < p} f ∣[k] [[1,j],[0,p]] + f ∣[k] (ε_p [[p,0],[0,1]])`, the sum over the right
cosets of `Γ₁(3) [[1,0],[0,p]] Γ₁(3)` (`LevelThreeHeckeCosets.tpFamily`), with `ε_p = ±1 ≡ p mod 3`
and Mathlib's slash action `(f ∣[k] α)(τ) = det(α)^{k-1} (cτ+d)^{-k} f(ατ)`. Since `-1` acts on
`S_k(Γ₁(3))` by `(-1)^k`, `f ∣[k] ε_p [[p,0],[0,1]] = χ_k(p) p^{k-1} f(pτ)` with the character
`χ_k(p) = 1` for `p ≡ 1` and `χ_k(p) = (-1)^k` for `p ≡ 2 mod 3` (`levelThreeChar`); thus
`T_p f(τ) = χ_k(p) p^{k-1} f(pτ) + p⁻¹ ∑_j f((τ+j)/p)` (`levelThreeHecke_apply`) and, for the
`q`-expansion at `∞` with period `1`,

  `a_n(T_p f) = a_{pn}(f) + χ_k(p) p^{k-1} a_{n/p}(f)`  (`levelThreeHecke_coeff`).

The operator `U_3 f = ∑_{j<3} f ∣[k] [[1,j],[0,3]]` (`levelThreeU3`), i.e.
`U_3 f(τ) = 3⁻¹ ∑_j f((τ+j)/3)`, has `a_n(U_3 f) = a_{3n}(f)` (`levelThreeU3_coeff`).
All these operators commute (`levelThreeHecke_comm`, `levelThreeHecke_comm_U3`), proved on
coefficients with `cuspForm_ext_coeff`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeHecke

open TernaryPeriodPolynomials
open LevelThreeHeckeSum LevelThreeHeckeCosets Spectral.LevelOneHecke

variable {k : ℤ}

/-- The character `χ_k(p)`: `1` if `p ≡ 1 mod 3`, `(-1)^k` if `p ≡ 2 mod 3` (it is the scalar
by which the diamond operator `⟨p⟩` acts on `S_k(Γ₁(3))`). -/
def levelThreeChar (k : ℤ) (p : ℕ) : ℂ := if p % 3 = 2 then (-1 : ℂ) ^ k else 1

theorem neg_one_zpow_neg (k : ℤ) : (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k := by
  rw [_root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]

/-- **The Hecke operator `T_p` (`p ≠ 3` prime) on `S_k(Γ₁(3))`.** -/
def levelThreeHecke (k : ℤ) (p : Nat.Primes) (hp : p.val ≠ 3) :
    CuspForm levelThree k →ₗ[ℂ] CuspForm levelThree k :=
  (tpFamily hp).sumOp k

/-- **The operator `U_3` on `S_k(Γ₁(3))`.** -/
def levelThreeU3 (k : ℤ) : CuspForm levelThree k →ₗ[ℂ] CuspForm levelThree k :=
  u3Family.sumOp k

theorem slash_heckeSign (p : Nat.Primes) (f : CuspForm levelThree k) (i : Option (Fin p.val)) :
    (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (heckeSign p i) =
      (match i with
        | none => levelThreeChar k p.val
        | some _ => 1) • (f : ℍ → ℂ) := by
  cases i with
  | none =>
    simp only [heckeSign, levelThreeChar]
    split_ifs
    · rw [show SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) = ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl,
        ← ModularForm.SL_slash, scalar_slash_neg_one, neg_one_zpow_neg]
    · rw [map_one, SlashAction.slash_one, one_smul]
  | some _ =>
    simp only [heckeSign]
    rw [map_one, SlashAction.slash_one, one_smul]

/-- The values of `T_p f`. -/
theorem levelThreeHecke_apply (p : Nat.Primes) (hp : p.val ≠ 3) (f : CuspForm levelThree k)
    (τ : ℍ) :
    levelThreeHecke k p hp f τ =
      levelThreeChar k p.val * ((p.val : ℂ) ^ (k - 1) *
          f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p.val p.property.pos) • τ))
        + (p.val : ℂ)⁻¹ * ∑ j : Fin p.val,
          f (GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (binaryHeckeTranslate p.val p.property.pos j) • τ) := by
  change CosetFamily.sumFun (tpFamily hp) k f τ = _
  have hterm : ∀ i, (f : ℍ → ℂ) ∣[k] real ((tpFamily hp).rep i) =
      (match i with
        | none => levelThreeChar k p.val
        | some _ => 1) • ((f : ℍ → ℂ) ∣[k] heckeMatrix p i) := by
    intro i
    change (f : ℍ → ℂ) ∣[k] real (tpRep p i) = _
    rw [tpRep_real, SlashAction.slash_mul, slash_heckeSign, ModularForm.smul_slash,
      sigma_heckeMatrix]
  simp only [CosetFamily.sumFun, hterm, Finset.sum_apply, Fintype.sum_option, Pi.smul_apply,
    smul_eq_mul, one_mul]
  rw [dilate_slash_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact translate_slash_apply k p j f τ

/-- The values of `U_3 f`. -/
theorem levelThreeU3_apply (f : CuspForm levelThree k) (τ : ℍ) :
    levelThreeU3 k f τ = ((3 : ℕ) : ℂ)⁻¹ * ∑ j : Fin 3,
      f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate 3 (by norm_num) j) • τ) := by
  change CosetFamily.sumFun u3Family k f τ = _
  simp only [CosetFamily.sumFun, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact translate_slash_apply k primeThree j f τ

theorem hasSum_qExpansion_levelThree (f : CuspForm levelThree k) (τ : ℍ) :
    HasSum (fun m => (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 τ ^ m) (f τ) :=
  ModularForm.hasSum_qExpansion f (by norm_num : (0 : ℝ) < 1) LevelThreeHeckeSum.one_mem_strictPeriods τ

/-- Uniqueness of `q`-expansion coefficients, packaged for `S_k(Γ₁(3))`. -/
theorem coeff_eq_of_hasSum (F : CuspForm levelThree k) (a : ℕ → ℂ)
    (h : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (F τ)) (n : ℕ) :
    (qExpansion 1 F).coeff n = a n :=
  (ModularFormClass.qExpansion_coeff_unique (by norm_num : (0 : ℝ) < 1)
    LevelThreeHeckeSum.one_mem_strictPeriods h n).symm

/-- **`q`-expansion of `T_p f`**: `a_n(T_p f) = χ_k(p) p^{k-1} a_{n/p}(f) + a_{pn}(f)`. -/
theorem levelThreeHecke_coeff (p : Nat.Primes) (hp : p.val ≠ 3) (f : CuspForm levelThree k)
    (n : ℕ) :
    (qExpansion 1 (levelThreeHecke k p hp f)).coeff n =
      levelThreeChar k p.val * (p.val : ℂ) ^ (k - 1) *
          qSeriesDilateCoefficients (fun m => (qExpansion 1 f).coeff m) p.val n +
        (qExpansion 1 f).coeff (p.val * n) := by
  have series (τ : ℍ) : HasSum (fun m =>
      (levelThreeChar k p.val * (p.val : ℂ) ^ (k - 1) *
          qSeriesDilateCoefficients (fun m => (qExpansion 1 f).coeff m) p.val m +
        (qExpansion 1 f).coeff (p.val * m)) • Function.Periodic.qParam 1 τ ^ m)
      (levelThreeHecke k p hp f τ) := by
    rw [levelThreeHecke_apply, ← mul_assoc]
    simp only [smul_eq_mul]
    apply qSeries_hecke_hasSum _ τ p.val p.property.pos
    · simpa only [binaryHeckeDilate_smul] using hasSum_qExpansion_levelThree f
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p.val p.property.pos) • τ)
    · intro j
      simpa only [binaryHeckeTranslate_smul] using hasSum_qExpansion_levelThree f
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p.val p.property.pos j) • τ)
  exact coeff_eq_of_hasSum _ _ series n

theorem hasSum_average (f : CuspForm levelThree k) (m : ℕ) (hm : 0 < m) (τ : ℍ) :
    HasSum (fun n => (qExpansion 1 f).coeff (m * n) * Function.Periodic.qParam 1 τ ^ n)
      ((m : ℂ)⁻¹ * ∑ j : Fin m,
        f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate m hm j) • τ)) := by
  apply qSeries_average_hasSum (fun m => (qExpansion 1 f).coeff m) τ m hm
  intro j
  simpa only [binaryHeckeTranslate_smul] using hasSum_qExpansion_levelThree f
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate m hm j) • τ)

/-- **`q`-expansion of `U_3 f`**: `a_n(U_3 f) = a_{3n}(f)`. -/
theorem levelThreeU3_coeff (f : CuspForm levelThree k) (n : ℕ) :
    (qExpansion 1 (levelThreeU3 k f)).coeff n = (qExpansion 1 f).coeff (3 * n) := by
  have series (τ : ℍ) : HasSum (fun m =>
      (qExpansion 1 f).coeff (3 * m) • Function.Periodic.qParam 1 τ ^ m) (levelThreeU3 k f τ) := by
    rw [levelThreeU3_apply]
    exact hasSum_average f 3 (by norm_num) τ
  exact coeff_eq_of_hasSum _ _ series n

/-- Two cusp forms for `Γ₁(3)` with the same `q`-expansion coefficients are equal. -/
theorem cuspForm_ext_coeff {f g : CuspForm levelThree k}
    (h : ∀ n, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  ext τ
  have hf := hasSum_qExpansion_levelThree f τ
  have hg := hasSum_qExpansion_levelThree g τ
  simp only [h] at hf
  exact hf.unique hg

theorem coeff_smul (a : ℂ) (f : CuspForm levelThree k) (n : ℕ) :
    (qExpansion 1 ((a • f : CuspForm levelThree k) : ℍ → ℂ)).coeff n =
      a * (qExpansion 1 f).coeff n := by
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1)
    LevelThreeHeckeSum.one_mem_strictPeriods, PowerSeries.coeff_smul, smul_eq_mul]

theorem coeff_add (f g : CuspForm levelThree k) (n : ℕ) :
    (qExpansion 1 ((f + g : CuspForm levelThree k) : ℍ → ℂ)).coeff n =
      (qExpansion 1 f).coeff n + (qExpansion 1 g).coeff n := by
  rw [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num : (0 : ℝ) < 1)
    LevelThreeHeckeSum.one_mem_strictPeriods, map_add]

theorem coeff_sub (f g : CuspForm levelThree k) (n : ℕ) :
    (qExpansion 1 ((f - g : CuspForm levelThree k) : ℍ → ℂ)).coeff n =
      (qExpansion 1 f).coeff n - (qExpansion 1 g).coeff n := by
  have h : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h, coeff_add, coeff_smul]
  ring

/-- **The Hecke operators `T_p`, `T_q` (`p, q ≠ 3`) commute.** -/
theorem levelThreeHecke_comm (p q : Nat.Primes) (hp : p.val ≠ 3) (hq : q.val ≠ 3)
    (f : CuspForm levelThree k) :
    levelThreeHecke k p hp (levelThreeHecke k q hq f) =
      levelThreeHecke k q hq (levelThreeHecke k p hp f) := by
  by_cases hpq : p = q
  · subst hpq
    rfl
  have hne : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  apply cuspForm_ext_coeff
  intro n
  simp only [levelThreeHecke_coeff, dilate_add_smul]
  rw [dilate_dilate p.property q.property hne,
    dilate_comp_mul p.property q.property hne (fun m => (qExpansion 1 f).coeff m),
    dilate_comp_mul q.property p.property hne.symm (fun m => (qExpansion 1 f).coeff m),
    show q.val * (p.val * n) = p.val * (q.val * n) by ring]
  ring

/-- **`T_p` (`p ≠ 3`) commutes with `U_3`.** -/
theorem levelThreeHecke_comm_U3 (p : Nat.Primes) (hp : p.val ≠ 3) (f : CuspForm levelThree k) :
    levelThreeHecke k p hp (levelThreeU3 k f) = levelThreeU3 k (levelThreeHecke k p hp f) := by
  apply cuspForm_ext_coeff
  intro n
  simp only [levelThreeHecke_coeff, levelThreeU3_coeff]
  rw [dilate_comp_mul p.property Nat.prime_three hp (fun m => (qExpansion 1 f).coeff m),
    show 3 * (p.val * n) = p.val * (3 * n) by ring]

end TernaryPeriodPolynomials.LevelThree.LevelThreeHecke
