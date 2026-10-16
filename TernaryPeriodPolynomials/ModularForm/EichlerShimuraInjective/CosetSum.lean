module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Covariance

@[expose] public section


/-!
# The coset sum is `SL₂(ℤ)`-covariant

`Atil_cov`: the sum over `SL₂(ℤ)/Γ` of the translates `conj(cz+d)⁻² A(gz)` transforms like weight `(0, 2)` under all of `SL₂(ℤ)`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

/-- The real matrix of an element of `SL₂(ℤ)`. -/
abbrev toR (g : SL(2, ℤ)) : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ g

theorem toR_det (g : SL(2, ℤ)) : (toR g).det = 1 := by
  ext
  simp only [toR, Matrix.GeneralLinearGroup.val_det_apply]
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have := (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g).det_coe
  simpa using this

theorem toR_mul (g h : SL(2, ℤ)) : toR (g * h) = toR g * toR h := map_mul _ _ _

theorem dnm_mul (γ δ : GL (Fin 2) ℝ) (_hγ : γ.det = 1) (_hδ : δ.det = 1) {z : ℂ} (hz : 0 < z.im) :
    dnm (γ * δ) z = dnm γ (mob δ z) * dnm δ z := by
  have hden := dnm_ne_zero δ hz
  unfold dnm mob at *
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

/-- The `g`-translate of a function: `A_g(z) = conj(cz+d)⁻² A(g z)`. -/
def Ag (A : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (conj (dnm (toR g) z) ^ 2)⁻¹ * A (mob (toR g) z)

theorem Ag_cov (A : ℂ → ℂ) (g δ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    Ag A g (mob (toR δ) z) = conj (dnm (toR δ) z) ^ 2 * Ag A (g * δ) z := by
  unfold Ag
  have hδp : 0 < (toR δ).det.val := by rw [toR_det]; simp
  have hw : 0 < (mob (toR δ) z).im := mob_im_pos _ hδp hz
  rw [toR_mul, dnm_mul _ _ (toR_det g) (toR_det δ) hz, mob_mul _ _ (toR_det g) (toR_det δ) hz]
  have h1 : dnm (toR g) (mob (toR δ) z) ≠ 0 := dnm_ne_zero _ hw
  have h2 : dnm (toR δ) z ≠ 0 := dnm_ne_zero _ hz
  have h1' : conj (dnm (toR g) (mob (toR δ) z)) ≠ 0 := by rwa [map_ne_zero]
  have h2' : conj (dnm (toR δ) z) ≠ 0 := by rwa [map_ne_zero]
  rw [map_mul]
  field_simp

theorem Ag_left_Γ (A : ℂ → ℂ) {Γ : Subgroup SL(2, ℤ)}
    (hΓ : ∀ γ ∈ Γ, ∀ w : ℂ, 0 < w.im → A (mob (toR γ) w) = conj (dnm (toR γ) w) ^ 2 * A w)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (h : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    Ag A (γ * h) z = Ag A h z := by
  unfold Ag
  have hhp : 0 < (toR h).det.val := by rw [toR_det]; simp
  have hw : 0 < (mob (toR h) z).im := mob_im_pos _ hhp hz
  rw [toR_mul, dnm_mul _ _ (toR_det γ) (toR_det h) hz, mob_mul _ _ (toR_det γ) (toR_det h) hz,
    hΓ γ hγ _ hw]
  have h1 : dnm (toR γ) (mob (toR h) z) ≠ 0 := dnm_ne_zero _ hw
  have h2 : dnm (toR h) z ≠ 0 := dnm_ne_zero _ hz
  have h1' : conj (dnm (toR γ) (mob (toR h) z)) ≠ 0 := by rwa [map_ne_zero]
  have h2' : conj (dnm (toR h) z) ≠ 0 := by rwa [map_ne_zero]
  rw [map_mul]
  field_simp

section Sum

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

instance fintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex

/-- The coset representative term. -/
def Ahat (A : ℂ → ℂ) (q : SL(2, ℤ) ⧸ Γ) (z : ℂ) : ℂ := Ag A (Quotient.out q)⁻¹ z

/-- The sum over the cosets `G/Γ` of the translates of `A`. -/
def Atil (A : ℂ → ℂ) (z : ℂ) : ℂ := ∑ q : SL(2, ℤ) ⧸ Γ, Ahat Γ A q z

variable {Γ}

omit [Γ.FiniteIndex] in
theorem Ahat_mk (A : ℂ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ∀ w : ℂ, 0 < w.im → A (mob (toR γ) w) = conj (dnm (toR γ) w) ^ 2 * A w)
    (x : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    Ahat Γ A (QuotientGroup.mk x) z = Ag A x⁻¹ z := by
  unfold Ahat
  have hy : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : SL(2, ℤ) ⧸ Γ)) : SL(2, ℤ) ⧸ Γ) =
      QuotientGroup.mk x := QuotientGroup.out_eq' _
  generalize Quotient.out (QuotientGroup.mk x : SL(2, ℤ) ⧸ Γ) = y at hy ⊢
  have hmem : y⁻¹ * x ∈ Γ := QuotientGroup.eq.mp hy
  have h' : y⁻¹ = (y⁻¹ * x) * x⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [h']
  exact Ag_left_Γ A hΓ hmem x⁻¹ hz

theorem Atil_cov (A : ℂ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ∀ w : ℂ, 0 < w.im → A (mob (toR γ) w) = conj (dnm (toR γ) w) ^ 2 * A w)
    (δ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    Atil Γ A (mob (toR δ) z) = conj (dnm (toR δ) z) ^ 2 * Atil Γ A z := by
  unfold Atil
  rw [Finset.mul_sum]
  have h1 : ∀ q : SL(2, ℤ) ⧸ Γ, Ahat Γ A q (mob (toR δ) z) =
      conj (dnm (toR δ) z) ^ 2 * Ahat Γ A (δ⁻¹ • q) z := by
    intro q
    unfold Ahat
    rw [Ag_cov A _ δ hz]
    congr 1
    have hq : (δ⁻¹ • q : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk (δ⁻¹ * Quotient.out q) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have := Ahat_mk A hΓ (δ⁻¹ * Quotient.out q) hz
    unfold Ahat at this
    rw [← hq] at this
    rw [this]
    congr 1
    group
  simp_rw [h1]
  exact Fintype.sum_equiv (MulAction.toPerm δ⁻¹) _ _ (fun q => rfl)

end Sum

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
