module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgePair

@[expose] public section


/-!
# Calculus of the Wirtinger derivatives

Foundation file of the unconditional Eichler--Shimura route.  Sum and product rules for `dz`, `dbar` (defined in `HodgePair`), their behaviour on
holomorphic and antiholomorphic functions, conjugation duality `dz (conj f) = conj (dbar f)`, and
the derivatives of the linear pencils `(zt - 1)^j (z̄t - 1)^k` that occur in the Hodge frame.

Formalized by Claude Sonnet 5.5.
-/

open Complex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair

theorem dz_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w * g w) z = dz f z * g z + f z * dz g z := by
  unfold dz
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem dz_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w + g w) z = dz f z + dz g z := by
  unfold dz
  rw [fderiv_fun_add hf hg]
  simp only [add_apply]
  ring

theorem dbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  unfold dbar
  rw [fderiv_fun_add hf hg]
  simp only [add_apply]
  ring

theorem dz_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {z : ℂ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dz (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dz (f i) z := by
  unfold dz
  rw [fderiv_fun_sum h]
  simp [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]

theorem dbar_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {z : ℂ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbar (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dbar (f i) z := by
  unfold dbar
  rw [fderiv_fun_sum h]
  simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem dz_const (c : ℂ) (z : ℂ) : dz (fun _ => c) z = 0 := by
  simp [dz]

theorem dbar_const (c : ℂ) (z : ℂ) : dbar (fun _ => c) z = 0 := by
  simp [dbar]

theorem dz_of_hasDerivAt {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z) : dz f z = f' := by
  have h2 := h.hasFDerivAt.restrictScalars ℝ
  unfold dz
  rw [h2.fderiv]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem dbar_of_hasDerivAt {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z) : dbar f z = 0 := by
  have h2 := h.hasFDerivAt.restrictScalars ℝ
  unfold dbar
  rw [h2.fderiv]
  simp
  ring_nf
  simp [Complex.I_sq]

theorem dz_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w => starRingEnd ℂ (f w)) z = starRingEnd ℂ (dbar f z) := by
  unfold dbar dz
  have h : fderiv ℝ (fun w => starRingEnd ℂ (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) :=
    (Complex.conjCLE.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  rw [h]
  have e : ∀ x, (Complex.conjCLE : ℂ →L[ℝ] ℂ) x = starRingEnd ℂ x := fun x => rfl
  simp only [ContinuousLinearMap.comp_apply, e, map_mul, map_add,
    map_div₀, map_one, map_ofNat, Complex.conj_I]
  ring

theorem hasDerivAt_lin_pow (c d : ℂ) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (c * w - d) ^ k) (k * (c * z - d) ^ (k - 1) * c) z := by
  have h := (((hasDerivAt_id z).const_mul c).sub_const d).fun_pow k
  simpa using h

theorem differentiableAt_lin_pow (c d : ℂ) (k : ℕ) (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => (c * w - d) ^ k) z :=
  (hasDerivAt_lin_pow c d k z).differentiableAt.restrictScalars ℝ

/-- The conjugate-linear factor as the conjugate of a holomorphic one. -/
theorem conj_lin_pow (t : ℂ) (k : ℕ) (w : ℂ) :
    (starRingEnd ℂ w * t - 1) ^ k = starRingEnd ℂ ((starRingEnd ℂ t * w - 1) ^ k) := by
  simp [map_pow, mul_comm]

theorem dz_antiholo_pow (t : ℂ) (k : ℕ) (z : ℂ) :
    dz (fun w => (starRingEnd ℂ w * t - 1) ^ k) z = 0 := by
  simp_rw [conj_lin_pow t k]
  rw [dz_conj (differentiableAt_lin_pow (starRingEnd ℂ t) 1 k z),
    dbar_of_hasDerivAt (hasDerivAt_lin_pow (starRingEnd ℂ t) 1 k z)]
  simp

theorem dbar_antiholo_pow (t : ℂ) (k : ℕ) (z : ℂ) :
    dbar (fun w => (starRingEnd ℂ w * t - 1) ^ k) z =
      k * t * (starRingEnd ℂ z * t - 1) ^ (k - 1) := by
  simp_rw [conj_lin_pow t k]
  rw [dbar_conj (differentiableAt_lin_pow (starRingEnd ℂ t) 1 k z),
    dz_of_hasDerivAt (hasDerivAt_lin_pow (starRingEnd ℂ t) 1 k z)]
  simp [map_pow, mul_comm]
  ring

theorem dz_G (m j : ℕ) (t z : ℂ) :
    dz (fun w => (w * t - 1) ^ j * (starRingEnd ℂ w * t - 1) ^ (m - j)) z =
      j * t * (z * t - 1) ^ (j - 1) * (starRingEnd ℂ z * t - 1) ^ (m - j) := by
  have h1 : DifferentiableAt ℝ (fun w : ℂ => (w * t - 1) ^ j) z := by
    simpa [mul_comm] using differentiableAt_lin_pow t 1 j z
  have h2 : DifferentiableAt ℝ (fun w : ℂ => (starRingEnd ℂ w * t - 1) ^ (m - j)) z := by
    simp_rw [conj_lin_pow t (m - j)]
    exact (Complex.conjCLE.differentiableAt).comp z
      (differentiableAt_lin_pow (starRingEnd ℂ t) 1 (m - j) z)
  rw [dz_mul h1 h2, dz_antiholo_pow]
  have : dz (fun w : ℂ => (w * t - 1) ^ j) z = j * (z * t - 1) ^ (j - 1) * t := by
    have := dz_of_hasDerivAt (hasDerivAt_lin_pow t 1 j z)
    simpa [mul_comm] using this
  rw [this]
  ring

theorem dbar_G (m j : ℕ) (t z : ℂ) :
    dbar (fun w => (w * t - 1) ^ j * (starRingEnd ℂ w * t - 1) ^ (m - j)) z =
      (z * t - 1) ^ j * (((m - j : ℕ) : ℂ) * t * (starRingEnd ℂ z * t - 1) ^ (m - j - 1)) := by
  have h1 : DifferentiableAt ℝ (fun w : ℂ => (w * t - 1) ^ j) z := by
    simpa [mul_comm] using differentiableAt_lin_pow t 1 j z
  have h2 : DifferentiableAt ℝ (fun w : ℂ => (starRingEnd ℂ w * t - 1) ^ (m - j)) z := by
    simp_rw [conj_lin_pow t (m - j)]
    exact (Complex.conjCLE.differentiableAt).comp z
      (differentiableAt_lin_pow (starRingEnd ℂ t) 1 (m - j) z)
  rw [dbar_mul h1 h2, dbar_antiholo_pow]
  have : dbar (fun w : ℂ => (w * t - 1) ^ j) z = 0 := by
    have := dbar_of_hasDerivAt (hasDerivAt_lin_pow t 1 j z)
    simpa [mul_comm] using this
  rw [this]
  ring

end TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair
