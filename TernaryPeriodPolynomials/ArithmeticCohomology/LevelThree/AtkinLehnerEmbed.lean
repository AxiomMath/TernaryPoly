module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Hecke

@[expose] public section


/-!
# Level-one cusp forms inside level three: `g ↦ g(3τ)`

For a level-one cusp form `g` the function `τ ↦ g(3τ)` is a cusp form for `Γ₁(3)` (indeed for
`Γ₀(3)`): with `D = [[3,0],[0,1]]` one has `D γ = γ' D` for `γ = [[a,b],[c,d]] ∈ Γ₀(3)` and
`γ' = [[a,3b],[c/3,d]] ∈ SL₂(ℤ)`. We use Mathlib's slash action, so the operator
`levelOneToThree : S_k(SL₂ℤ) →ₗ[ℂ] S_k(Γ₁(3))` is `g ↦ g ∣[k] D = 3^{k-1} g(3τ)`; its `q`-expansion is
`a_n = 3^{k-1} b_{n/3}` (`levelOneToThree_coeff`), i.e. supported on multiples of `3`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups Manifold
open Matrix UpperHalfPlane
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehnerEmbed

open TernaryPeriodPolynomials
open LevelThreeHeckeSum LevelThreeHeckeCosets Spectral.LevelOneHecke

variable {k : ℤ}

/-- The integer matrix `[[3,0],[0,1]]` commutes past `Γ₀(3)` into `SL₂(ℤ)`. -/
theorem d3_matrix (a b c₁ d : ℤ) :
    !![3, 0; 0, 1] * !![a, b; 3 * c₁, d] = !![a, 3 * b; c₁, d] * !![3, 0; 0, 1] := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem d3_transition {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma1 3) :
    ∃ γ : SL(2, ℤ), modularHeckeMatrix primeThree none * g.val =
      γ.val * modularHeckeMatrix primeThree none := by
  rw [CongruenceSubgroup.Gamma1_mem] at hg
  obtain ⟨a, b, c, d, hgv⟩ : ∃ a b c d : ℤ, g.val = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two g.val⟩
  have e10 : g.val 1 0 = c := by simp [hgv]
  have hdet : a * d - b * c = 1 := by
    have := g.property
    rwa [hgv, Matrix.det_fin_two_of] at this
  have hc : (3 : ℤ) ∣ c - 0 := dvd_of_zmod_eq (by rw [← e10, hg.2.2]; simp)
  obtain ⟨c₁, hc₁⟩ := hc
  have hc' : c = 3 * c₁ := by linarith
  have hM : modularHeckeMatrix primeThree none = !![3, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [modularHeckeMatrix, primeThree]
  have hγ : (!![a, 3 * b; c₁, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + b * hc'
  refine ⟨⟨_, hγ⟩, ?_⟩
  rw [hM, hgv, hc']
  exact d3_matrix a b c₁ d

/-- The cusps of `Γ₁(3)` are carried to cusps of `SL₂(ℤ)` by rational matrices. -/
theorem isCusp_three_one (a : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c levelThree) :
    IsCusp (real a • c) levelOne := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  have hc1 : IsCusp c levelOne := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact hc
  have h := hc1.smul (real a)
  have := Subgroup.IsArithmetic.conj levelOne a
  exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp h

/-- The function `g ↦ g ∣[k] [[3,0],[0,1]]`. -/
def iotaFun (k : ℤ) (g : ℍ → ℂ) : ℍ → ℂ := g ∣[k] heckeMatrix primeThree none

theorem iotaFun_slash (g : ℍ → ℂ) (hg : ∀ γ ∈ levelOne, g ∣[k] γ = g) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    iotaFun k g ∣[k] SpecialLinearGroup.mapGL ℝ γ = iotaFun k g := by
  obtain ⟨γ', h⟩ := d3_transition hγ
  have hr : heckeMatrix primeThree none * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ γ' * heckeMatrix primeThree none :=
    real_relation (rat_relation (modularHeckeMatrix_rational primeThree none)
      (modularHeckeMatrix_rational primeThree none) h)
  unfold iotaFun
  rw [← SlashAction.slash_mul, hr, SlashAction.slash_mul, hg _ ⟨γ', rfl⟩]

theorem iotaFun_mdifferentiable (g : CuspForm levelOne k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (iotaFun k g) :=
  (CuspForm.translate g (heckeMatrix primeThree none)).holo'

theorem iotaFun_zeroAt (g : CuspForm levelOne k) {c : OnePoint ℝ} (hc : IsCusp c levelThree) :
    c.IsZeroAt (iotaFun k g) k := by
  intro γ hγ
  unfold iotaFun
  rw [← SlashAction.slash_mul]
  apply CuspFormClass.zero_at_cusps g
    (isCusp_three_one (binaryHeckeRepresentative primeThree none) hc)
  rw [mul_smul, hγ]
  try rfl

/-- **The embedding `g ↦ g ∣[k] [[3,0],[0,1]] = 3^{k-1} g(3τ)`** of level-one cusp forms into
cusp forms for `Γ₁(3)`. -/
def levelOneToThree (k : ℤ) : CuspForm levelOne k →ₗ[ℂ] CuspForm levelThree k where
  toFun g :=
    { toFun := iotaFun k g
      slash_action_eq' := by
        rintro γ ⟨h, hh, rfl⟩
        exact iotaFun_slash g (fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ) h hh
      holo' := iotaFun_mdifferentiable g
      zero_at_cusps' := fun hc => iotaFun_zeroAt g hc }
  map_add' f g := by
    ext τ
    change iotaFun k (⇑f + ⇑g) τ = iotaFun k f τ + iotaFun k g τ
    simp only [iotaFun, SlashAction.add_slash, Pi.add_apply]
  map_smul' a f := by
    ext τ
    change iotaFun k (a • ⇑f) τ = a • iotaFun k f τ
    simp only [iotaFun, ModularForm.smul_slash, Pi.smul_apply, sigma_heckeMatrix]

theorem levelOneToThree_apply (g : CuspForm levelOne k) :
    (levelOneToThree k g : ℍ → ℂ) = ⇑g ∣[k] heckeMatrix primeThree none := rfl

theorem levelOneToThree_apply' (g : CuspForm levelOne k) (τ : ℍ) :
    levelOneToThree k g τ = (primeThree.val : ℂ) ^ (k - 1) *
      g (GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (binaryHeckeDilate primeThree.val primeThree.property.pos) • τ) :=
  dilate_slash_apply k primeThree g τ

/-- **`q`-expansion of `g(3τ)`**: `a_n = 3^{k-1} b_{n/3}` (and `0` if `3 ∤ n`). -/
theorem levelOneToThree_coeff (g : CuspForm levelOne k) (n : ℕ) :
    (qExpansion 1 (levelOneToThree k g)).coeff n =
      (primeThree.val : ℂ) ^ (k - 1) *
        qSeriesDilateCoefficients (fun m => (qExpansion 1 g).coeff m) primeThree.val n := by
  have series (τ : ℍ) : HasSum (fun m =>
      ((primeThree.val : ℂ) ^ (k - 1) *
        qSeriesDilateCoefficients (fun m => (qExpansion 1 g).coeff m) primeThree.val m) •
          Function.Periodic.qParam 1 τ ^ m) (levelOneToThree k g τ) := by
    rw [levelOneToThree_apply']
    have hs : HasSum (fun m => (qExpansion 1 g).coeff m * Function.Periodic.qParam 1
        (primeThree.val * (τ : ℂ)) ^ m)
        (g (GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (binaryHeckeDilate primeThree.val primeThree.property.pos) • τ)) := by
      simpa only [binaryHeckeDilate_smul] using
        ModularForm.hasSum_qExpansion g (by norm_num : (0 : ℝ) < 1)
            Spectral.LevelOneHecke.one_mem_strictPeriods
          (GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (binaryHeckeDilate primeThree.val primeThree.property.pos) • τ)
    have h := qSeries_dilate_hasSum (fun m => (qExpansion 1 g).coeff m) (τ : ℂ) primeThree.val
      primeThree.property.pos _ hs
    simpa only [smul_eq_mul, mul_assoc] using h.mul_left ((primeThree.val : ℂ) ^ (k - 1))
  exact (ModularFormClass.qExpansion_coeff_unique (by norm_num : (0 : ℝ) < 1)
    LevelThreeHeckeSum.one_mem_strictPeriods series n).symm

/-- The coefficients of `g(3τ)` at multiples of `3`: `a_{3m} = 3^{k-1} b_m`. -/
theorem levelOneToThree_coeff_mul (g : CuspForm levelOne k) (m : ℕ) :
    (qExpansion 1 (levelOneToThree k g)).coeff (3 * m) =
      (3 : ℂ) ^ (k - 1) * (qExpansion 1 g).coeff m := by
  have h3 : primeThree.val = 3 := rfl
  rw [levelOneToThree_coeff]
  unfold qSeriesDilateCoefficients
  rw [h3, ite_eq_left (dvd_mul_right 3 m), Nat.mul_div_cancel_left m (by norm_num : 0 < 3)]
  try norm_num

end TernaryPeriodPolynomials.LevelThree.LevelThreeAtkinLehnerEmbed
