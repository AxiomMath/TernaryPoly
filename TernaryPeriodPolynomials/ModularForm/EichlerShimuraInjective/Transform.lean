module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass

@[expose] public section


/-!
# Transformation of binary integrands

The primitive of the binary integrand has a constant transformation defect (`primitive_defect_const'`).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

/-- The binary integrand transforms along any `γ` with `h(γ z) = (cz+d)^{n+3} h'(z)`. -/
theorem binaryIntegrand_transform' (n : ℕ) (h h' : ℂ → ℂ) (γ : GL (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hmod : h (mob γ z) = dnm γ z ^ (n + 3) * h' z) (v : Fin 2 → ℂ) :
    binaryIntegrand n h v (mob γ z) * (1 / dnm γ z ^ 2) =
      binaryIntegrand n h' (invCoord γ v) z := by
  have hden := dnm_ne_zero γ hz
  have he : mob γ z * v 1 - v 0 =
      (z * (invCoord γ v 1) - invCoord γ v 0) / dnm γ z := by
    apply (eq_div_iff hden).2
    unfold mob dnm invCoord
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [sub_mul, mul_right_comm (_ / _) (v 1) _, div_mul_cancel₀ _ (by simpa [dnm] using hden)]
    ring
  unfold binaryIntegrand
  rw [hmod, he, div_pow, pow_add]
  field_simp
  ring

/-- Constancy of the transformation defect, for primitives of two different integrands. -/
theorem primitive_defect_const' (n : ℕ) (h h' : ℂ → ℂ) (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1)
    (hmod : ∀ z : ℂ, 0 < z.im → h (mob γ z) = dnm γ z ^ (n + 3) * h' z)
    (F F' : (Fin 2 → ℂ) → ℂ → ℂ)
    (hF : ∀ v z, 0 < z.im → HasDerivAt (F v) (binaryIntegrand n h v z) z)
    (hF' : ∀ v z, 0 < z.im → HasDerivAt (F' v) (binaryIntegrand n h' v z) z)
    (v : Fin 2 → ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    F v (mob γ z) - F' (invCoord γ v) z = F v (mob γ w) - F' (invCoord γ v) w := by
  have hpos : 0 < γ.det.val := by simp [hdet]
  have hder : ∀ u : ℂ, 0 < u.im →
      HasDerivAt (fun u => F v (mob γ u) - F' (invCoord γ v) u) 0 u := by
    intro u hu
    have h1 := (hF v (mob γ u) (mob_im_pos γ hpos hu)).comp u (mob_hasDerivAt γ hdet hu)
    have h2 := hF' (invCoord γ v) u hu
    have h3 := h1.sub h2
    have h4 := binaryIntegrand_transform' n h h' γ hu (hmod u hu) v
    have h5 : binaryIntegrand n h v (mob γ u) * (1 / dnm γ u ^ 2) -
        binaryIntegrand n h' (invCoord γ v) u = 0 := by rw [h4, sub_self]
    exact h3.congr_deriv h5
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconv : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  exact IsOpen.is_const_of_deriv_eq_zero hopen hconv
    (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hder u hu).deriv) hz hw

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
