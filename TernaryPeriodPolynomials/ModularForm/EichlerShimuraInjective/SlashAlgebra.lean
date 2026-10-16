module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.VanishingFromDecay
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.AnalyticBounds
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.PrimitiveBound

@[expose] public section


/-!
# Algebraic identity for the translates of `A`

`Ag_eq`: `A_σ(z) = conj(f|σ (z)) · (Φ₀^{σ}(z; (z̄,1)) + R_σ(z))` with a polynomial remainder `R_σ`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral Filter Topology
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

section Decay

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ}
  {v : MvPolynomial (Fin 2) ℂ}

/-- The slash `(f | σ)(z) = f(σ z) (cz+d)^{-(n+3)}`. -/
def fs (n : ℕ) (f : ℂ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := f (mob (toR σ) z) * ((dnm (toR σ) z) ^ (n + 3))⁻¹

theorem fs_mod (n : ℕ) (f : ℂ → ℂ) (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    f (mob (toR σ) z) = dnm (toR σ) z ^ (n + 3) * fs n f σ z := by
  unfold fs
  have := pow_ne_zero (n + 3) (dnm_ne_zero (toR σ) hz)
  field_simp

theorem fs_diff (n : ℕ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Uset) (σ : SL(2, ℤ)) :
    DifferentiableOn ℂ (fs n f σ) Uset := by
  unfold fs
  have hd : Differentiable ℂ (fun z : ℂ => dnm (toR σ) z) := by unfold dnm; fun_prop
  exact (hf.comp (differentiableOn_mob σ) (fun z hz => mob_mem_Uset σ hz)).mul
    (((hd.pow (n + 3)).differentiableOn).inv (fun z hz => pow_ne_zero _ (dnm_ne_zero _ hz)))

omit [Γ.FiniteIndex] in
theorem Ag_eq (S : Setup Γ n f g Gf Gg v) (σ : SL(2, ℤ)) (G2 H2 : ℕ → ℂ → ℂ)
    (hG2 : ∀ j z, 0 < z.im → HasDerivAt (G2 j) (fs n f σ z * z ^ j) z)
    (hH2 : ∀ j z, 0 < z.im → HasDerivAt (H2 j) (fs n g σ z * z ^ j) z)
    (hG2I : ∀ j, G2 j Complex.I = 0) (hH2I : ∀ j, H2 j Complex.I = 0) {z : ℂ} (hz : 0 < z.im) :
    Ag (Aval n f Gf Gg v) σ z = conj (fs n f σ z) * (Phi0 n G2 H2 ![conj z, 1] z +
      Phi n Gf Gg v (conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1]) (mob (toR σ) Complex.I)) := by
  have hJ : dnm (toR σ) z ≠ 0 := dnm_ne_zero _ hz
  have hJc : conj (dnm (toR σ) z) ≠ 0 := by rwa [map_ne_zero]
  have h0 := Phi0_transform n f (fs n f σ) g (fs n g σ) Gf G2 Gg H2 (toR σ) (toR_det σ) S.dGf hG2 S.dGg hH2
    (fun w hw => fs_mod n f σ hw) (fun w hw => fs_mod n g σ hw) hG2I hH2I ![conj (mob (toR σ) z), 1] hz
  rw [invCoord_conj_mob (toR σ) (toR_det σ) hz, Phi0_smul] at h0
  have hs := Phi_smul n Gf Gg v S.vh ![conj (mob (toR σ) z), 1] (mob (toR σ) Complex.I) (conj (dnm (toR σ) z))
  have hP : Phi n Gf Gg v ![conj (mob (toR σ) z), 1] (mob (toR σ) z) =
      (conj (dnm (toR σ) z))⁻¹ ^ (n + 1) * Phi0 n G2 H2 ![conj z, 1] z +
        Phi n Gf Gg v ![conj (mob (toR σ) z), 1] (mob (toR σ) Complex.I) := by
    unfold Phi
    rw [h0]
    ring
  unfold Ag Aval
  rw [hP, hs, fs_mod n f σ hz, map_mul, map_pow]
  have hpow2 : conj (dnm (toR σ) z) ^ (n + 3) = conj (dnm (toR σ) z) ^ 2 * conj (dnm (toR σ) z) ^ (n + 1) := by
    rw [← pow_add]; congr 1; omega
  generalize conj (dnm (toR σ) z) = X at *
  generalize Phi0 n G2 H2 ![conj z, 1] z = M0
  generalize Phi n Gf Gg v ![conj (mob (toR σ) z), 1] (mob (toR σ) Complex.I) = R0
  rw [hpow2, inv_pow]
  have hXn : X ^ (n + 1) ≠ 0 := pow_ne_zero _ hJc
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero _ hJc
  field_simp

end Decay

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
