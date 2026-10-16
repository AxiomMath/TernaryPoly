module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.RemainderBound

@[expose] public section


/-!
# Decay of the coset sum

`Ag_decay`, `Atil_integral_tendsto`: `∫_{-1/2}^{1/2} Ã(x + iT) dx → 0` as `T → ∞`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral Filter Topology
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

/-- Exponential decay of all slashes of `f` at `i∞`. -/
def Decays (n : ℕ) (f : ℂ → ℂ) : Prop :=
  ∀ σ : SL(2, ℤ), ∃ C c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ z : ℂ, A ≤ z.im → ‖fs n f σ z‖ ≤ C * Real.exp (-c * z.im)

section Decay

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ}
  {v : MvPolynomial (Fin 2) ℂ}

omit [Γ.FiniteIndex] in
theorem Ag_decay (S : Setup Γ n f g Gf Gg v) (hdf : Decays n f) (hdg : Decays n g) (σ : SL(2, ℤ)) :
    ∃ (K : ℝ) (D : ℕ) (c : ℝ), 0 < c ∧ ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, |x| ≤ 1 / 2 →
      ‖Ag (Aval n f Gf Gg v) σ ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ K * (1 + T) ^ D * Real.exp (-c * T) := by
  obtain ⟨Cf, cf, Af, hcf, hAf, hf⟩ := hdf σ
  obtain ⟨Cg, cg, Ag', hcg, hAg, hg'⟩ := hdg σ
  obtain ⟨G2, hG2I, hG2⟩ := exists_moment_primitives (fs n f σ) (fs_diff n S.hf σ)
  obtain ⟨H2, hH2I, hH2⟩ := exists_moment_primitives (fs n g σ) (fs_diff n S.hg σ)
  choose KG hKG using fun j : ℕ => prim_bound (fs_diff n S.hf σ) j (hG2 j) hcf hAf hf
  choose KH hKH using fun j : ℕ => prim_bound (fs_diff n S.hg σ) j (hH2 j) hcg hAg hg'
  set KM : ℝ := ∑ j ∈ Finset.range (n + 2), (|KG j| + |KH j|) with hKM
  have hKM0 : 0 ≤ KM := Finset.sum_nonneg (fun j _ => by positivity)
  have hKGM : ∀ j : ℕ, j < n + 2 → |KG j| ≤ KM := fun j hj => by
    have := Finset.single_le_sum (f := fun j => |KG j| + |KH j|) (fun j _ => by positivity)
      (Finset.mem_range.mpr hj)
    linarith [abs_nonneg (KH j)]
  have hKHM : ∀ j : ℕ, j < n + 2 → |KH j| ≤ KM := fun j hj => by
    have := Finset.single_le_sum (f := fun j => |KG j| + |KH j|) (fun j _ => by positivity)
      (Finset.mem_range.mpr hj)
    linarith [abs_nonneg (KG j)]
  obtain ⟨K1, hK10, hK1⟩ := Phi0_bound n G2 H2 (KG := KM) (T0 := max Af Ag') hKM0
    (fun j hj x T hx hT => (hKG j x hx T (le_trans (le_max_left _ _) hT)).trans ((le_abs_self _).trans (hKGM j hj)))
    (fun j hj x T hx hT => (hKH j x hx T (le_trans (le_max_right _ _) hT)).trans ((le_abs_self _).trans (hKHM j hj)))
  obtain ⟨K2, D2, hK20, hK2⟩ := R_bound n Gf Gg v σ
  have hCf : 0 ≤ Cf := by
    have h1 := hf (Complex.I * (Af : ℂ)) (by simp)
    by_contra hneg
    push Not at hneg
    have : Cf * Real.exp (-cf * (Complex.I * (Af : ℂ)).im) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith [norm_nonneg (fs n f σ (Complex.I * (Af : ℂ)))]
  refine ⟨Cf * (K1 + K2 * 2 ^ D2), max (n + 1) D2, cf, hcf, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max Af Ag') 1)] with T hT x hx
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : max Af Ag' ≤ T := le_trans (le_max_left _ _) hT
  have hTA : Af ≤ T := le_trans (le_max_left _ _) hT0
  set z : ℂ := (x : ℂ) + (T : ℂ) * Complex.I with hz
  have hzim : z.im = T := by simp [hz]
  have hzpos : 0 < z.im := by rw [hzim]; linarith
  have hzn : ‖z‖ ≤ 1 + T := by
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T)]
    linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  rw [Ag_eq S σ G2 H2 hG2 hH2 hG2I hH2I hzpos, norm_mul, Complex.norm_conj]
  have hf2 : ‖fs n f σ z‖ ≤ Cf * Real.exp (-cf * T) := by
    have := hf z (by rw [hzim]; exact hTA)
    rwa [hzim] at this
  have hM : ‖Phi0 n G2 H2 ![conj z, 1] z‖ ≤ K1 * (1 + T) ^ (n + 1) := hK1 x T hx hT0 (by linarith)
  have hR := hK2 z hzpos
  have hMR : ‖Phi0 n G2 H2 ![conj z, 1] z +
      Phi n Gf Gg v (conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1]) (mob (toR σ) Complex.I)‖ ≤
      (K1 + K2 * 2 ^ D2) * (1 + T) ^ (max (n + 1) D2) := by
    refine (norm_add_le _ _).trans ?_
    have h1 : K1 * (1 + T) ^ (n + 1) ≤ K1 * (1 + T) ^ (max (n + 1) D2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (le_max_left _ _)) hK10
    have h2 : K2 * (1 + ‖z‖) ^ D2 ≤ K2 * 2 ^ D2 * (1 + T) ^ (max (n + 1) D2) := by
      have : (1 + ‖z‖) ^ D2 ≤ (2 * (1 + T)) ^ D2 := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc K2 * (1 + ‖z‖) ^ D2 ≤ K2 * (2 * (1 + T)) ^ D2 := mul_le_mul_of_nonneg_left this hK20
        _ = K2 * 2 ^ D2 * (1 + T) ^ D2 := by rw [mul_pow]; ring
        _ ≤ K2 * 2 ^ D2 * (1 + T) ^ (max (n + 1) D2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (le_max_right _ _)) (by positivity)
    nlinarith
  calc ‖fs n f σ z‖ * ‖Phi0 n G2 H2 ![conj z, 1] z +
        Phi n Gf Gg v (conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1]) (mob (toR σ) Complex.I)‖
      ≤ (Cf * Real.exp (-cf * T)) * ((K1 + K2 * 2 ^ D2) * (1 + T) ^ (max (n + 1) D2)) := by
        apply mul_le_mul hf2 hMR (norm_nonneg _) (by positivity)
    _ = _ := by ring


theorem Atil_integral_tendsto (S : Setup Γ n f g Gf Gg v) (hdf : Decays n f) (hdg : Decays n g) :
    Tendsto (fun T : ℝ => ∫ x in (-1 / 2 : ℝ)..(1 / 2),
      Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
  choose K D c hc hev using fun q : SL(2, ℤ) ⧸ Γ => Ag_decay S hdf hdg (gq Γ q)
  have hb : Tendsto (fun T : ℝ => ∑ q : SL(2, ℤ) ⧸ Γ, K q * ((1 + T) ^ (D q) * Real.exp (-c q * T))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (SL(2, ℤ) ⧸ Γ))
      (fun q _ => (tendsto_poly_exp (D q) (hc q)).const_mul (K q))
    simpa using this
  refine squeeze_zero_norm' ?_ hb
  have hall : ∀ᶠ T : ℝ in atTop, ∀ q : SL(2, ℤ) ⧸ Γ, ∀ x : ℝ, |x| ≤ 1 / 2 →
      ‖Ag (Aval n f Gf Gg v) (gq Γ q) ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ K q * (1 + T) ^ (D q) * Real.exp (-c q * T) :=
    Filter.eventually_all.2 hev
  filter_upwards [hall] with T hT
  have h1 : ∀ x ∈ Set.uIoc (-1 / 2 : ℝ) (1 / 2), ‖Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      ∑ q : SL(2, ℤ) ⧸ Γ, K q * ((1 + T) ^ (D q) * Real.exp (-c q * T)) := by
    intro x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hx' : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    unfold Atil
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => ?_))
    have := hT q x hx'
    unfold Ahat
    unfold gq at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const h1
  have e : |(1 / 2 : ℝ) - (-1 / 2)| = 1 := by norm_num
  rw [e, mul_one] at this
  exact this

end Decay

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
