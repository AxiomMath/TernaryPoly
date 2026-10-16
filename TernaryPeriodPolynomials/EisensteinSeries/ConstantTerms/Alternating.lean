module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Equivariance
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

@[expose] public section


/-!
# Proposition C.4: the summed components form an alternating two-form

The seed is antisymmetric in its two form indices (`seedForm_antisymm`); the pullback by a smooth map
(`formPullback_antisymm`), the coefficient action `ρ` (`rho_neg`) and coefficientwise conjugation
preserve this, so every summand (`summandK_antisymm`, `summandPoly_antisymm`) and hence the sum of the
series is antisymmetric in `(i, j)` and vanishes for `i = j`: `seriesForm_antisymm`,
`seriesFormK_antisymm` (holomorphic or antiholomorphic seed, every plane cusp). Antisymmetric
components define an alternating bilinear form on the tangent space `ℝ⁵` with values in the
coefficient space (`componentBil`, `componentBil_isAlt`), whose coefficients are smooth in the point as
soon as those of the components are (`contDiffOn_componentBil_coeff`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Antisymmetry of the components -/

theorem formPullback_antisymm (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (hom : ∀ y a b, om y a b = - om y b a) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ om p i j = - formPullback Φ om p j i := by
  unfold formPullback
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hom (Φ p) b a, mul_neg]
  congr 3
  push_cast
  ring

theorem rho_neg (g : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (-q) = - SeedC3.rho g q := by
  have : -q = C (-1 : ℂ) * q := by simp
  rw [this, rho_C_mul]
  have h1 : (C (-1 : ℂ) : MvPolynomial (Fin 3) ℂ) = -1 := by simp
  rw [h1, neg_one_mul]

theorem seedFormK_antisymm (b : Bool) (n : ℕ) (h : ℂ → ℂ) (y : Fin 5 → ℝ) (a c : Fin 5) :
    seedFormK b n h y a c = - seedFormK b n h y c a := by
  unfold seedFormK
  rw [seedForm_antisymm n h y a c, map_neg]

theorem summandK_antisymm (b : Bool) (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i j : Fin 5) :
    summandK b n h g q i j = - summandK b n h g q j i := by
  unfold summandK
  rw [formPullback_antisymm _ _ (fun y a c => seedFormK_antisymm b n h y a c) q i j, rho_neg]

theorem summandK_diag (b : Bool) (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i : Fin 5) : summandK b n h g q i i = 0 := by
  have := summandK_antisymm b n h g q i i
  exact self_eq_neg.1 this

theorem summandPoly_antisymm (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i j : Fin 5) :
    summandPoly n h g q i j = - summandPoly n h g q j i := by
  rw [← summandK_false, ← summandK_false, summandK_antisymm]

section Series

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (b : Bool) (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem termFunK_antisymm (c : CuspCoset Γ D.r) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (x : Fin 5 → ℝ) :
    termFunK b D Γ n f c i j m x = - termFunK b D Γ n f c j i m x := by
  unfold termFunK
  rw [summandK_antisymm, MvPolynomial.coeff_neg]

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesFormK_antisymm (y : Fin 5 → ℝ) (i j : Fin 5) :
    seriesFormK b D Γ n f y i j = - seriesFormK b D Γ n f y j i := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [MvPolynomial.coeff_neg, coeff_seriesFormK, coeff_seriesFormK]
  unfold seriesCoeffK
  rw [← tsum_neg]
  exact tsum_congr fun c => termFunK_antisymm b D Γ n f c i j m y

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesFormK_diag (y : Fin 5 → ℝ) (i : Fin 5) : seriesFormK b D Γ n f y i i = 0 :=
  self_eq_neg.1 (seriesFormK_antisymm b D Γ n f y i i)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesForm_antisymm (y : Fin 5 → ℝ) (i j : Fin 5) :
    seriesForm Γ n f y i j = - seriesForm Γ n f y j i := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [MvPolynomial.coeff_neg, coeff_seriesForm, coeff_seriesForm]
  unfold seriesCoeff
  rw [← tsum_neg]
  refine tsum_congr fun c => ?_
  unfold termFun
  rw [summandPoly_antisymm, MvPolynomial.coeff_neg]

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesForm_diag (y : Fin 5 → ℝ) (i : Fin 5) : seriesForm Γ n f y i i = 0 :=
  self_eq_neg.1 (seriesForm_antisymm Γ n f y i i)

end Series


/-! ### Components as an alternating bilinear form on the tangent space -/

/-- The bilinear form on `ℝ⁵` with values in `M` whose components are `E a c`. -/
def componentBil {M : Type*} [AddCommGroup M] [Module ℝ M] (E : Fin 5 → Fin 5 → M) :
    (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) →ₗ[ℝ] M :=
  LinearMap.mk₂ ℝ (fun v w => ∑ a, ∑ c, v a • w c • E a c)
    (fun v v' w => by simp [add_smul, Finset.sum_add_distrib])
    (fun r v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by congr 1; ring)
    (fun v w w' => by simp [add_smul, smul_add, Finset.sum_add_distrib])
    (fun r v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by congr 1; ring)

theorem componentBil_apply {M : Type*} [AddCommGroup M] [Module ℝ M] (E : Fin 5 → Fin 5 → M)
    (v w : Fin 5 → ℝ) : componentBil E v w = ∑ a, ∑ c, v a • w c • E a c := rfl

theorem componentBil_isAlt {M : Type*} [AddCommGroup M] [Module ℝ M]
    (E : Fin 5 → Fin 5 → M)
    (hE : ∀ a c, E a c = - E c a) : LinearMap.IsAlt (componentBil E) := by
  intro v
  rw [componentBil_apply]
  have : ∑ a, ∑ c, v a • v c • E a c = - ∑ a, ∑ c, v a • v c • E a c := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hE c a, hE a c, neg_neg, smul_neg, smul_neg, neg_neg, smul_comm]
  have h2 : (2 : ℝ) • (∑ a, ∑ c, v a • v c • E a c) = 0 := by
    rw [two_smul]; nth_rewrite 1 [this]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem componentBil_single {M : Type*} [AddCommGroup M] [Module ℝ M] (E : Fin 5 → Fin 5 → M)
    (a c : Fin 5) : componentBil E (Pi.single a 1) (Pi.single c 1) = E a c := by
  rw [componentBil_apply]
  simp [Pi.single_apply]

/-- The `m`-th coefficient of the bilinear form with `E_n`-valued components is the
corresponding bilinear combination of the coefficients of the components. -/
theorem coeff_componentBil (n : ℕ) (E : Fin 5 → Fin 5 → MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n)
    (v w : Fin 5 → ℝ) (m : Fin 3 →₀ ℕ) :
    ((componentBil E v w : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n) :
        MvPolynomial (Fin 3) ℂ).coeff m =
      ∑ a, ∑ c, ((v a * w c : ℝ) : ℂ) * ((E a c : MvPolynomial (Fin 3) ℂ)).coeff m := by
  rw [componentBil_apply]
  simp only [Submodule.coe_sum, MvPolynomial.coeff_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Submodule.coe_smul_of_tower, MvPolynomial.coeff_smul, Complex.real_smul]

/-- Smoothness of the coefficients of the components gives smoothness of the coefficients of the
bilinear form, for every pair of tangent vectors. -/
theorem contDiffOn_componentBil_coeff (n : ℕ) (U : Set (Fin 5 → ℝ))
    (E : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n)
    (hE : ∀ a c m, ContDiffOn ℝ ∞ (fun y => ((E y a c : MvPolynomial (Fin 3) ℂ)).coeff m) U)
    (v w : Fin 5 → ℝ) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (fun y => ((componentBil (E y) v w :
      MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n) : MvPolynomial (Fin 3) ℂ).coeff m) U := by
  simp_rw [coeff_componentBil]
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ => ?_
  exact contDiffOn_const.mul (hE a c m)


end TernaryPeriodPolynomials.Argument.ConvergenceC4
