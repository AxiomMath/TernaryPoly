module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.AtkinLehnerEmbed

@[expose] public section


/-!
# The Atkin–Lehner lemma at the prime `3`

Let `f ∈ S_k(Γ₁(3))` have `q`-expansion supported on multiples of `3`. Then `f(τ + 1/3) = f(τ)`,
so `G := f ∣[k] [[1,0],[0,3]]`, `G(τ) = f(τ/3)/3`, satisfies `G ∣ T = G`. Since
`[[1,0],[0,3]] · [[1,0],[1,1]] = [[1,0],[3,1]] · [[1,0],[0,3]]` with `[[1,0],[3,1]] ∈ Γ₁(3)`,
also `G ∣ L = G` for `L = [[1,0],[1,1]]`. As `S = T⁻¹ L T⁻¹` and `S, T` generate `SL₂(ℤ)`, `G` is a
level-one cusp form (`gForm`), and `f = 3^{2-k}·(G ∣ [[3,0],[0,1]])` is the image of a level-one
cusp form under `levelOneToThree` (`atkinLehner_three`). For odd `k` level-one cusp forms vanish
(`eq_zero_of_odd`), so then `f = 0` (`atkinLehner_three_odd`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups Manifold
open Matrix UpperHalfPlane
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehner

open TernaryPeriodPolynomials
open LevelThreeHeckeSum LevelThreeHeckeCosets LevelThreeAtkinLehnerEmbed
open Spectral.LevelOneHecke LevelThreeHecke

variable {k : ℤ}

/-- The point `τ + 1/3`. -/
abbrev third (τ : ℍ) : ℍ := (1 / 3 : ℝ) +ᵥ τ

theorem coe_third (τ : ℍ) : ((third τ : ℍ) : ℂ) = (τ : ℂ) + 1 / 3 := by
  simp only [third, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem qParam_third (τ : ℍ) :
    Function.Periodic.qParam 1 (third τ : ℍ) =
      Complex.exp (2 * Real.pi * Complex.I / 3) * Function.Periodic.qParam 1 τ := by
  simp only [Function.Periodic.qParam, coe_third, Complex.ofReal_one, div_one]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- A cusp form for `Γ₁(3)` whose `q`-expansion is supported on multiples of `3` is invariant
under `τ ↦ τ + 1/3`. -/
theorem third_period (f : CuspForm levelThree k)
    (h : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0) (τ : ℍ) : f (third τ) = f τ := by
  have hz : Complex.exp (2 * Real.pi * Complex.I / 3) ^ 3 = 1 := by
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_two_pi_mul_I using 2
    push_cast
    ring
  have h1 := hasSum_qExpansion_levelThree f (third τ)
  have h2 := hasSum_qExpansion_levelThree f τ
  rw [qParam_third] at h1
  have hterm : ∀ m : ℕ, (qExpansion 1 f).coeff m *
      (Complex.exp (2 * Real.pi * Complex.I / 3) * Function.Periodic.qParam 1 τ) ^ m =
        (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 τ ^ m := by
    intro m
    by_cases hm : 3 ∣ m
    · obtain ⟨j, rfl⟩ := hm
      rw [mul_pow, pow_mul (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 j, hz, one_pow, one_mul]
    · rw [h m hm, zero_mul, zero_mul]
  simp only [hterm] at h1
  exact h1.unique h2

/-- The matrix `[[1,0],[0,3]]`. -/
abbrev E3 : GL (Fin 2) ℝ := heckeMatrix primeThree (some (0 : Fin 3))

/-- The point `τ/3`, i.e. the image of `τ` under `[[1,0],[0,3]]`. -/
def tr (τ : ℍ) : ℍ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (binaryHeckeTranslate primeThree.val primeThree.property.pos (0 : Fin 3)) • τ

theorem coe_tr (τ : ℍ) : ((tr τ : ℍ) : ℂ) = (τ : ℂ) / 3 := by
  have h := binaryHeckeTranslate_smul primeThree.val primeThree.property.pos (0 : Fin 3) τ
  refine h.trans ?_
  simp [primeThree]

theorem primeThree_cast : ((primeThree.val : ℕ) : ℂ) = 3 := by
  simp [primeThree]

theorem E3_apply (f : ℍ → ℂ) (τ : ℍ) : (f ∣[k] E3) τ = (3 : ℂ)⁻¹ * f (tr τ) := by
  have h := translate_slash_apply k primeThree (0 : Fin 3) f τ
  rw [primeThree_cast] at h
  exact h

theorem tr_vadd (τ : ℍ) : tr ((1 : ℝ) +ᵥ τ) = third (tr τ) := by
  apply UpperHalfPlane.ext
  simp only [coe_tr, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem tr_dilate (τ : ℍ) :
    tr (GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (binaryHeckeDilate primeThree.val primeThree.property.pos) • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [coe_tr, binaryHeckeDilate_smul, primeThree_cast]
  field_simp

theorem E3_slash_T (f : CuspForm levelThree k) (per : ∀ τ, f (third τ) = f τ) :
    (⇑f ∣[k] E3) ∣[k] (ModularGroup.T : SL(2, ℤ)) = ⇑f ∣[k] E3 := by
  ext τ
  rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul, E3_apply, E3_apply, tr_vadd,
    per]
  have hd : UpperHalfPlane.denom (ModularGroup.T : SL(2, ℤ)) τ = 1 := by
    simp [UpperHalfPlane.denom, ModularGroup.coe_T]
  rw [hd, _root_.one_zpow, mul_one]

/-- `[[1,0],[1,1]]`. -/
def lowerOne : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

/-- `[[1,0],[3,1]] ∈ Γ₁(3)`. -/
def lowerThree : SL(2, ℤ) := ⟨!![1, 0; 3, 1], by simp [Matrix.det_fin_two_of]⟩

theorem lowerThree_mem : lowerThree ∈ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  decide

theorem E3_lower :
    E3 * SpecialLinearGroup.mapGL ℝ lowerOne = SpecialLinearGroup.mapGL ℝ lowerThree * E3 := by
  have hint : modularHeckeMatrix primeThree (some (0 : Fin 3)) * lowerOne.val =
      lowerThree.val * modularHeckeMatrix primeThree (some (0 : Fin 3)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [modularHeckeMatrix, lowerOne, lowerThree, Matrix.mul_apply, Fin.sum_univ_two,
        primeThree]
  exact real_relation (rat_relation (modularHeckeMatrix_rational primeThree (some (0 : Fin 3)))
    (modularHeckeMatrix_rational primeThree (some (0 : Fin 3))) hint)

theorem E3_slash_lower (f : CuspForm levelThree k) :
    (⇑f ∣[k] E3) ∣[k] SpecialLinearGroup.mapGL ℝ lowerOne = ⇑f ∣[k] E3 := by
  rw [← SlashAction.slash_mul, E3_lower, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (mapGL_mem_levelThree lowerThree_mem)]

/-- The stabilizer of a function under the weight-`k` slash action of `SL₂(ℤ)`. -/
def stab (k : ℤ) (g : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | g ∣[k] γ = g}
  one_mem' := SlashAction.slash_one k g
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [SlashAction.slash_mul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem S_eq : (ModularGroup.S : SL(2, ℤ)) =
    (ModularGroup.T : SL(2, ℤ))⁻¹ * lowerOne * (ModularGroup.T : SL(2, ℤ))⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, lowerOne, Matrix.mul_apply, Fin.sum_univ_two]

theorem E3_slash_SL (f : CuspForm levelThree k) (per : ∀ τ, f (third τ) = f τ) (γ : SL(2, ℤ)) :
    (⇑f ∣[k] E3) ∣[k] γ = ⇑f ∣[k] E3 := by
  have hT : (ModularGroup.T : SL(2, ℤ)) ∈ stab k (⇑f ∣[k] E3) := E3_slash_T f per
  have hL : lowerOne ∈ stab k (⇑f ∣[k] E3) := E3_slash_lower f
  have hS : (ModularGroup.S : SL(2, ℤ)) ∈ stab k (⇑f ∣[k] E3) := by
    rw [S_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hT) hL)
      (Subgroup.inv_mem _ hT)
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ stab k (⇑f ∣[k] E3) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  exact hle (by rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top _)

theorem isCusp_one_three (a : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c levelOne) :
    IsCusp (real a • c) levelThree := by
  have hc1 : IsCusp c levelThree := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc
  exact CosetFamily.isCusp_real_smul a hc1

/-- **The level-one cusp form `τ ↦ f(τ/3)/3`** attached to `f ∈ S_k(Γ₁(3))` with `f(τ+1/3) = f(τ)`. -/
def gForm (f : CuspForm levelThree k) (per : ∀ τ, f (third τ) = f τ) : CuspForm levelOne k where
  toFun := ⇑f ∣[k] E3
  slash_action_eq' := by
    rintro γ ⟨g, rfl⟩
    exact E3_slash_SL f per g
  holo' := (CuspForm.translate f E3).holo'
  zero_at_cusps' := by
    intro c hc γ hγ
    rw [← SlashAction.slash_mul]
    apply CuspFormClass.zero_at_cusps f (isCusp_one_three (binaryHeckeRepresentative primeThree
      (some (0 : Fin 3))) hc)
    rw [mul_smul, hγ]
    try rfl

theorem gForm_apply (f : CuspForm levelThree k) (per : ∀ τ, f (third τ) = f τ) (τ : ℍ) :
    gForm f per τ = (3 : ℂ)⁻¹ * f (tr τ) := E3_apply f τ

theorem levelOneToThree_gForm (f : CuspForm levelThree k) (per : ∀ τ, f (third τ) = f τ) :
    levelOneToThree k (gForm f per) = (3 : ℂ) ^ (k - 2) • f := by
  ext τ
  rw [levelOneToThree_apply', gForm_apply, tr_dilate, primeThree_cast]
  change (3 : ℂ) ^ (k - 1) * ((3 : ℂ)⁻¹ * f τ) = (3 : ℂ) ^ (k - 2) * f τ
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have h : (3 : ℂ) ^ (k - 2) = (3 : ℂ) ^ (k - 1) * 3⁻¹ := by
    rw [show k - 2 = (k - 1) + (-1) by ring, zpow_add₀ h3, _root_.zpow_neg_one]
  rw [h]
  ring

/-- **Atkin–Lehner at `3`.** A cusp form for `Γ₁(3)` whose `q`-expansion is supported on multiples
of `3` is `g(3τ)` (up to the normalization of `levelOneToThree`) for a level-one cusp form `g`. -/
theorem atkinLehner_three (f : CuspForm levelThree k)
    (h : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm levelOne k, levelOneToThree k g = f := by
  have per := third_period f h
  refine ⟨(3 : ℂ) ^ (2 - k) • gForm f per, ?_⟩
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  rw [map_smul, levelOneToThree_gForm, smul_smul, ← zpow_add₀ h3,
    show 2 - k + (k - 2) = 0 by ring, zpow_zero, one_smul]

/-- Level-one cusp forms of odd weight vanish (because `-1 ∈ SL₂(ℤ)`). -/
theorem eq_zero_of_odd (g : CuspForm levelOne k) (hk : Odd k) : g = 0 := by
  have h1 : (⇑g ∣[k] (-1 : SL(2, ℤ))) = ⇑g := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq g _ ⟨-1, rfl⟩
  have h2 := scalar_slash_neg_one k ⇑g
  rw [h1] at h2
  ext τ
  have h3 := congrFun h2 τ
  rw [Pi.smul_apply, smul_eq_mul, _root_.zpow_neg, hk.neg_one_zpow] at h3
  have : (g τ : ℂ) = 0 := by linear_combination (1 / 2 : ℂ) * h3
  simpa using this

/-- For odd weight, a cusp form for `Γ₁(3)` supported on multiples of `3` vanishes. -/
theorem atkinLehner_three_odd (hk : Odd k) (f : CuspForm levelThree k)
    (h : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  obtain ⟨g, rfl⟩ := atkinLehner_three f h
  rw [eq_zero_of_odd g hk, map_zero]

end TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehner
