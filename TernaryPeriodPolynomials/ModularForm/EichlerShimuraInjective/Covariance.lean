module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.CombinedPrimitive

@[expose] public section


/-!
# The Petersson-type function `A(z) = conj f(z) · Φ(z; (z̄, 1))`

`Aval_cov`: if the combined period cocycle is a coboundary, `A(γz) = conj(cz+d)² A(z)` for `γ` in the group.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

theorem eval_smul_homog (v : MvPolynomial (Fin 2) ℂ) (d : ℕ) (hv : v.IsHomogeneous d) (t : ℂ)
    (a : Fin 2 → ℂ) : MvPolynomial.eval (t • a) v = t ^ d * MvPolynomial.eval a v := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hdeg : ∑ i ∈ e.support, e i = d := by
    have := hv (MvPolynomial.mem_support_iff.mp he)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The combined (holomorphic plus antiholomorphic) Eichler integral shifted by `v`. -/
def Phi (n : ℕ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) (a : Fin 2 → ℂ) (z : ℂ) : ℂ :=
  Phi0 n Gf Gg a z + MvPolynomial.eval a v

theorem Phi0_smul (n : ℕ) (G H : ℕ → ℂ → ℂ) (a : Fin 2 → ℂ) (z t : ℂ) :
    Phi0 n G H (t • a) z = t ^ (n + 1) * Phi0 n G H a z := by
  rw [Phi0_eq_sum, Phi0_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  have : t ^ (n + 1) = t ^ j * t ^ (n + 1 - j) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

theorem Phi_smul (n : ℕ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) (hvh : v.IsHomogeneous (n + 1))
    (a : Fin 2 → ℂ) (z t : ℂ) : Phi n Gf Gg v (t • a) z = t ^ (n + 1) * Phi n Gf Gg v a z := by
  unfold Phi
  rw [Phi0_smul, eval_smul_homog v (n + 1) hvh]
  ring

/-- Equivariance of the combined Eichler integral under `γ`, given the coboundary relation. -/
theorem Phi_cov (n : ℕ) (f g : ℂ → ℂ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ)
    (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1)
    (hGf : ∀ j z, 0 < z.im → HasDerivAt (Gf j) (f z * z ^ j) z)
    (hGg : ∀ j z, 0 < z.im → HasDerivAt (Gg j) (g z * z ^ j) z)
    (hmf : ∀ z : ℂ, 0 < z.im → f (mob γ z) = dnm γ z ^ (n + 3) * f z)
    (hmg : ∀ z : ℂ, 0 < z.im → g (mob γ z) = dnm γ z ^ (n + 3) * g z)
    (hGf0 : ∀ j, Gf j Complex.I = 0) (hGg0 : ∀ j, Gg j Complex.I = 0)
    (hv : eichlerCocycle n Gf γ + MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n Gg γ) =
      MvPolynomial.bind₁ (invCoordPoly γ) v - v)
    (a : Fin 2 → ℂ) {z : ℂ} (hz : 0 < z.im) :
    Phi n Gf Gg v a (mob γ z) = Phi n Gf Gg v (invCoord γ a) z := by
  unfold Phi
  rw [Phi0_transform n f f g g Gf Gf Gg Gg γ hdet hGf hGf hGg hGg hmf hmg hGf0 hGg0 a hz]
  have h1 : Phi0 n Gf Gg a (mob γ Complex.I) = MvPolynomial.eval a
      (eichlerCocycle n Gf γ + MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n Gg γ)) := by
    unfold Phi0 eichlerCocycle
    rw [map_add]
  rw [h1, hv, map_sub, eval_bind₁_invCoordPoly]
  ring

/-- The scalar function `A(z) = conj f(z) · Φ(z; (z̄, 1))` whose Wirtinger derivative is the Petersson density. -/
def Aval (n : ℕ) (f : ℂ → ℂ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℂ :=
  conj (f z) * Phi n Gf Gg v ![conj z, 1] z

theorem conj_dnm (γ : GL (Fin 2) ℝ) (z : ℂ) :
    conj (dnm γ z) = (γ 1 0 : ℝ) * conj z + (γ 1 1 : ℝ) := by
  simp [dnm, map_add, map_mul]

theorem conj_mob (γ : GL (Fin 2) ℝ) (z : ℂ) :
    conj (mob γ z) = ((γ 0 0 : ℝ) * conj z + (γ 0 1 : ℝ)) / ((γ 1 0 : ℝ) * conj z + (γ 1 1 : ℝ)) := by
  simp [mob, map_add, map_mul, map_div₀]

theorem invCoord_conj_mob (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1) {z : ℂ} (hz : 0 < z.im) :
    invCoord γ ![conj (mob γ z), 1] = (conj (dnm γ z))⁻¹ • ![conj z, 1] := by
  have hd : conj (dnm γ z) ≠ 0 := by
    rw [map_ne_zero]; exact dnm_ne_zero γ hz
  rw [conj_dnm] at hd ⊢
  have hd2 : ((γ 1 1 : ℝ) : ℂ) + conj z * ((γ 1 0 : ℝ) : ℂ) ≠ 0 := by
    intro h; apply hd; linear_combination h
  have hdet' : ((γ 0 0 : ℝ) : ℂ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) = 1 := by
    have := det_eq_one γ hdet
    exact_mod_cast this
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · show ((γ 1 1 : ℝ) : ℂ) * ((conj (mob γ z))) - ((γ 0 1 : ℝ) : ℂ) * 1 = _
    rw [conj_mob]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    rw [← mul_div_assoc, div_sub' hd, ← div_eq_inv_mul]
    congr 1
    linear_combination (conj z) * hdet'
  · show -((γ 1 0 : ℝ) : ℂ) * ((conj (mob γ z))) + ((γ 0 0 : ℝ) : ℂ) * 1 = _
    rw [conj_mob]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have h : -((γ 1 0 : ℝ) : ℂ) * ((((γ 0 0 : ℝ) : ℂ) * conj z + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * conj z + ((γ 1 1 : ℝ) : ℂ))) + ((γ 0 0 : ℝ) : ℂ) * 1 =
        (-((γ 1 0 : ℝ) : ℂ) * (((γ 0 0 : ℝ) : ℂ) * conj z + ((γ 0 1 : ℝ) : ℂ)) +
          ((γ 0 0 : ℝ) : ℂ) * (((γ 1 0 : ℝ) : ℂ) * conj z + ((γ 1 1 : ℝ) : ℂ))) /
          (((γ 1 0 : ℝ) : ℂ) * conj z + ((γ 1 1 : ℝ) : ℂ)) := by
      field_simp
    rw [h, mul_one, ← one_div]
    congr 1
    linear_combination hdet'

theorem Aval_cov (n : ℕ) (f g : ℂ → ℂ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ)
    (hvh : v.IsHomogeneous (n + 1))
    (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1)
    (hGf : ∀ j z, 0 < z.im → HasDerivAt (Gf j) (f z * z ^ j) z)
    (hGg : ∀ j z, 0 < z.im → HasDerivAt (Gg j) (g z * z ^ j) z)
    (hmf : ∀ z : ℂ, 0 < z.im → f (mob γ z) = dnm γ z ^ (n + 3) * f z)
    (hmg : ∀ z : ℂ, 0 < z.im → g (mob γ z) = dnm γ z ^ (n + 3) * g z)
    (hGf0 : ∀ j, Gf j Complex.I = 0) (hGg0 : ∀ j, Gg j Complex.I = 0)
    (hv : eichlerCocycle n Gf γ + MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n Gg γ) =
      MvPolynomial.bind₁ (invCoordPoly γ) v - v)
    {z : ℂ} (hz : 0 < z.im) :
    Aval n f Gf Gg v (mob γ z) = conj (dnm γ z) ^ 2 * Aval n f Gf Gg v z := by
  unfold Aval
  have hd : conj (dnm γ z) ≠ 0 := by
    rw [map_ne_zero]; exact dnm_ne_zero γ hz
  rw [Phi_cov n f g Gf Gg v γ hdet hGf hGg hmf hmg hGf0 hGg0 hv _ hz, invCoord_conj_mob γ hdet hz,
    Phi_smul n Gf Gg v hvh, hmf z hz, map_mul, map_pow]
  have key : conj (dnm γ z) ^ (n + 3) * ((conj (dnm γ z))⁻¹) ^ (n + 1) = conj (dnm γ z) ^ 2 := by
    rw [inv_pow]
    have : conj (dnm γ z) ^ (n + 3) = conj (dnm γ z) ^ 2 * conj (dnm γ z) ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hd), mul_one]
  calc conj (dnm γ z) ^ (n + 3) * conj (f z) * ((conj (dnm γ z))⁻¹ ^ (n + 1) * Phi n Gf Gg v ![conj z, 1] z)
      = (conj (dnm γ z) ^ (n + 3) * ((conj (dnm γ z))⁻¹) ^ (n + 1)) * (conj (f z) * Phi n Gf Gg v ![conj z, 1] z) := by ring
    _ = _ := by rw [key]

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
