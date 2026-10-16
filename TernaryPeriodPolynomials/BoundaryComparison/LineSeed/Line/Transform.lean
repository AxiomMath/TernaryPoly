module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Eta

@[expose] public section


/-!
# The transformation law of the line primitive `η` (LS5)

For `g` with `lam g = [[a,b],[c,d]]` and `v = v(g)`, `x = (w, τ)`:
`Ψ(g·x) = (cτ+d)² h(τ)(τ(w₀+v₀) + (w₁+v₁)) ρ(g)(P_τⁿ)`, hence
`(cτ+d)⁻² Ψ(g·x) - ρ(g)Ψ(x) = h(τ)(τ v₀ + v₁) ρ(g)(P_τⁿ)` (`defect_poly`), and `dτ ∘ D(g) = (cτ+d)⁻² dτ` (`dtau_fderiv_act`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi

theorem rho_eq_bind_of_det {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det = 1) (q : MvPolynomial (Fin 3) ℂ) :
    rho M q = bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C (((M⁻¹ i j : ℝ)) : ℂ) * X j) q := by
  unfold rho
  rw [hM]
  simp

theorem rho_pow_of_det {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det = 1) (q : MvPolynomial (Fin 3) ℂ) (n : ℕ) :
    rho M (q ^ n) = rho M q ^ n := by
  rw [rho_eq_bind_of_det hM, rho_eq_bind_of_det hM, map_pow]

theorem rho_C_mul_general (M : Matrix (Fin 3) (Fin 3) ℝ) (a : ℂ) (q : MvPolynomial (Fin 3) ℂ) :
    rho M (C a * q) = C a * rho M q := by
  unfold rho
  rw [map_mul, bind₁_C_right]
  ring

namespace LineData

variable {G : Type} [Group G] (D : LineData G)

theorem dnm_ne_zero' (g : G) {x : Face} (hx : x ∈ faceSet) : dnm (D.lam g) (faceTau x) ≠ 0 :=
  dnm_ne_zero _ (faceTau_im hx)

/-- The linear form `τ w₀ + w₁` after the action: `τ'(w₀' ) + w₁' = (τ(w₀+v₀) + (w₁+v₁))/(cτ+d)`. -/
theorem act_lin (g : G) {x : Face} (hx : x ∈ faceSet) :
    faceTau (D.act g x) * ((D.act g x 0 : ℝ) : ℂ) + ((D.act g x 1 : ℝ) : ℂ) =
      (faceTau x * (((x 0 + D.v g 0 : ℝ)) : ℂ) + (((x 1 + D.v g 1 : ℝ)) : ℂ)) / dnm (D.lam g) (faceTau x) := by
  have hne := D.dnm_ne_zero' g hx
  have hd := det_eq_one (D.lam g) (D.det_one g)
  have hdC : ((D.lam g 0 0 : ℝ) : ℂ) * (D.lam g 1 1 : ℝ) - (D.lam g 0 1 : ℝ) * (D.lam g 1 0 : ℝ) = 1 := by
    exact_mod_cast hd
  have hm : mob (D.lam g) (faceTau x) * dnm (D.lam g) (faceTau x) =
      ((D.lam g 0 0 : ℝ) : ℂ) * faceTau x + ((D.lam g 0 1 : ℝ) : ℂ) := by
    unfold mob dnm at *
    exact div_mul_cancel₀ _ hne
  rw [D.faceTau_act, D.act_zero, D.act_one, eq_div_iff hne]
  unfold dnm at hm ⊢
  push_cast
  linear_combination (((x 0 : ℂ) + D.v g 0) * ((D.lam g 1 1 : ℝ) : ℂ) -
      ((x 1 : ℂ) + D.v g 1) * ((D.lam g 1 0 : ℝ) : ℂ)) * hm +
    (faceTau x * ((x 0 : ℂ) + D.v g 0) + ((x 1 : ℂ) + D.v g 1)) * hdC

/-- `dτ` after the action of `g`: `dτ ∘ D(g) = (cτ+d)^{-2} dτ`. -/
theorem dtau_fderiv_act (g : G) {x : Face} (hx : x ∈ faceSet) (v : Face) :
    dtau (fderiv ℝ (D.act g) x v) = (dnm (D.lam g) (faceTau x) ^ 2)⁻¹ * dtau v := by
  have hdet := D.det_one g
  have hτ : HasFDerivAt faceTau dtau x := by
    have : faceTau = ⇑dtau := funext faceTau_eq
    rw [this]; exact dtau.hasFDerivAt
  have hact : DifferentiableAt ℝ (D.act g) x :=
    (((D.act_contDiffOn g) x hx).contDiffAt (isOpen_faceSet.mem_nhds hx)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun y => dtau (D.act g y)) (dtau.comp (fderiv ℝ (D.act g) x)) x :=
    dtau.hasFDerivAt.comp x hact.hasFDerivAt
  have h2 : HasFDerivAt (fun y => mob (D.lam g) (faceTau y))
      (((1 / dnm (D.lam g) (faceTau x) ^ 2) : ℂ) • dtau) x :=
    (mob_hasDerivAt (D.lam g) hdet (faceTau_im hx)).comp_hasFDerivAt x hτ
  have hfun : (fun y => dtau (D.act g y)) = fun y => mob (D.lam g) (faceTau y) := by
    funext y
    rw [← faceTau_eq, D.faceTau_act]
  rw [hfun] at h1
  have := h1.unique h2
  have := congrArg (fun L => L v) this
  simpa [one_div] using this

variable (h : ℂ → ℂ) (n : ℕ)

/-- **The defect of `Ψ`** (polynomial form): `(cτ+d)⁻² Ψ(g·x) - ρ(g)Ψ(x) = h(τ)(τ v₀ + v₁) ρ(g)(P_τⁿ)`. -/
theorem defect_poly (g : G) {x : Face} (hx : x ∈ faceSet)
    (hmod : h (mob (D.lam g) (faceTau x)) = dnm (D.lam g) (faceTau x) ^ (n + 3) * h (faceTau x)) :
    C (((dnm (D.lam g) (faceTau x))⁻¹) ^ 2) * Coef.toPoly (linePsiVal h n (D.act g x)) -
        rho (D.lmat g) (Coef.toPoly (linePsiVal h n x)) =
      C (h (faceTau x) * (faceTau x * (D.v g 0 : ℂ) + (D.v g 1 : ℂ))) *
        rho (D.lmat g) (Ppoly (faceTau x) ^ n) := by
  set c := dnm (D.lam g) (faceTau x) with hc
  set τ := faceTau x with hτ
  have hne : c ≠ 0 := D.dnm_ne_zero' g hx
  have hτ' : h (faceTau (D.act g x)) = c ^ (n + 3) * h τ := by
    rw [D.faceTau_act]; exact hmod
  have e1 := D.act_lin g hx
  have hP : Ppoly (faceTau (D.act g x)) = C c⁻¹ * rho (D.lmat g) (Ppoly τ) := by
    rw [D.faceTau_act, rho_lmat_Ppoly D g (faceTau_im hx), ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne,
      map_one, one_mul]
  have hPn : Ppoly (faceTau (D.act g x)) ^ n = C ((c⁻¹) ^ n) * rho (D.lmat g) (Ppoly τ ^ n) := by
    rw [hP, mul_pow, ← map_pow, rho_pow_of_det (D.det_lmat g)]
  rw [toPoly_linePsiVal, toPoly_linePsiVal, hτ', e1, hPn, rho_C_mul_general]
  set R := rho (D.lmat g) (Ppoly τ ^ n)
  have hscal : (c⁻¹) ^ 2 * (c ^ (n + 3) * h τ * ((τ * ((x 0 + D.v g 0 : ℝ) : ℂ) +
      ((x 1 + D.v g 1 : ℝ) : ℂ)) / c)) * (c⁻¹) ^ n - h τ * (τ * (x 0 : ℂ) + (x 1 : ℂ)) =
      h τ * (τ * (D.v g 0 : ℂ) + (D.v g 1 : ℂ)) := by
    have hcn : c ^ n * (c⁻¹) ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hne, one_pow]
    push_cast
    field_simp
    linear_combination (h τ * c ^ 3 * (τ * ((x 0 : ℂ) + D.v g 0) + ((x 1 : ℂ) + D.v g 1))) * hcn
  have hfin : C ((c⁻¹) ^ 2) * (C (c ^ (n + 3) * h τ * ((τ * ((x 0 + D.v g 0 : ℝ) : ℂ) +
      ((x 1 + D.v g 1 : ℝ) : ℂ)) / c)) * (C ((c⁻¹) ^ n) * R)) - C (h τ * (τ * (x 0 : ℂ) + (x 1 : ℂ))) * R =
      C ((c⁻¹) ^ 2 * (c ^ (n + 3) * h τ * ((τ * ((x 0 + D.v g 0 : ℝ) : ℂ) +
      ((x 1 + D.v g 1 : ℝ) : ℂ)) / c)) * (c⁻¹) ^ n - h τ * (τ * (x 0 : ℂ) + (x 1 : ℂ))) * R := by
    simp only [map_mul, map_sub]
    ring
  rw [hfin, hscal]

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
