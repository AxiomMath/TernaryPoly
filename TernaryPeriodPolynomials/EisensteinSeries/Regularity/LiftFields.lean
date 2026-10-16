module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Moebius
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.FiniteModel
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Lift
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Space
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Petersson
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

@[expose] public section


/-!
# The analytic fields of `FiniteModel` for adelic lifts

For a weight-`k` cusp form `f` of `Γ₁(3)` the adelic lift `adelicLift f` is continuous, has weight
`k` under the stabiliser `stab a b = !![a, b; -b, a]` of `i`, and is holomorphic along the
maps `z ↦ x · gUp z`.  The predicate `IsHolomorphicWeight k` bundles these three fields, is
stable under linear combinations and under right translation by `GL₂(𝔸_f)` (which commutes with
the archimedean component), and `holomorphicWeightSubmodule k` is the corresponding submodule of
`GL₂(𝔸) → ℂ`.  Continuity is `Petersson.continuous_adelicLift`; the main results proved here are
`adelicLift_mul_stab`, `differentiableOn_adelicLift_gUp` and
`span_translates_le_holomorphicWeight`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.CuspIntegral
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree)

namespace TernaryPeriodPolynomials.Regularity

namespace LiftFields

/-- Finite-adelic and archimedean right translations commute. -/
theorem mul_atInfinity_mul_atFinite (x : BinaryAdelicGL) (s : BinaryRealGL) (u : BinaryFiniteGL) :
    x * atInfinity s * atFinite u = x * atFinite u * atInfinity s := by
  rw [mul_assoc, mul_assoc, ← infGL_apply, ← finGL_apply, infGL_finGL_comm]

/-! ### Elementary real-number facts -/

theorem sumSq_pos {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : 0 < a ^ 2 + b ^ 2 :=
  lt_of_le_of_ne (add_nonneg (sq_nonneg a) (sq_nonneg b)) (Ne.symm h)

theorem I_im_ne_zero : Complex.I.im ≠ 0 := by
  rw [Complex.I_im]
  exact one_ne_zero

theorem sqrt_pow_eq_rpow {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    Real.sqrt y ^ k = y ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  congr 1
  ring

theorem inv_mul_mul_mul_cancel_aux {Y A B : ℂ} (hY : Y ≠ 0) : Y⁻¹ * (A * Y * B) = A * B := by
  calc Y⁻¹ * (A * Y * B) = Y⁻¹ * (Y * (A * B)) := by ring
    _ = A * B := inv_mul_cancel_left₀ hY _

/-! ### The classical lift `liftReal` -/

theorem liftReal_eq_denom {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (r : BinaryRealGL) :
    liftReal f r = ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
      denom r Complex.I ^ (-k) * f (r • UpperHalfPlane.I) :=
  rfl

theorem coe_smul_eq_moeb {g : BinaryRealGL} (hg : 0 < (GeneralLinearGroup.det g : ℝˣ).val)
    (τ : UpperHalfPlane) : ((g • τ : UpperHalfPlane) : ℂ) = moeb g τ :=
  UpperHalfPlane.coe_smul_of_det_pos hg τ

/-! ### Right translation by the real group -/

theorem isDecomp_mul_infGL {g : BinaryAdelicGL} {γ : BinaryRationalGL} {r : BinaryRealGL}
    {κ : BinaryFiniteGL} (h : IsDecomp g γ r κ) {s : BinaryRealGL}
    (hs : 0 < (GeneralLinearGroup.det s : ℝˣ).val) : IsDecomp (g * infGL s) γ (r * s) κ := by
  refine ⟨?_, h.2.1, ?_⟩
  · rw [map_mul, Units.val_mul]
    exact mul_pos h.1 hs
  · rw [h.2.2, mul_assoc, mul_assoc, ← infGL_finGL_comm s κ, ← mul_assoc (infGL r) (infGL s),
      ← map_mul infGL r s]

theorem adelicLift_mul_infGL {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) {g : BinaryAdelicGL}
    {γ : BinaryRationalGL} {r : BinaryRealGL} {κ : BinaryFiniteGL} (h : IsDecomp g γ r κ)
    {s : BinaryRealGL} (hs : 0 < (GeneralLinearGroup.det s : ℝˣ).val) :
    adelicLift f (g * infGL s) = liftReal f (r * s) :=
  adelicLift_eq_of_isDecomp f (isDecomp_mul_infGL h hs)

/-! ### The weight law -/

theorem det_stab {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    (GeneralLinearGroup.det (stab a b) : ℝˣ).val = a ^ 2 + b ^ 2 := by
  rw [GeneralLinearGroup.val_det_apply, gl_det_eq, stab_00 h, stab_01 h, stab_10 h, stab_11 h]
  ring

theorem det_stab_pos {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    0 < (GeneralLinearGroup.det (stab a b) : ℝˣ).val := by
  rw [det_stab h]
  exact sumSq_pos h

theorem denom_stab_I {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    denom (stab a b) Complex.I = (a : ℂ) - b * Complex.I := by
  rw [denom_def, stab_10 h, stab_11 h]
  push_cast
  ring

theorem moeb_stab_I {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    moeb (stab a b) Complex.I = Complex.I := by
  have hD := denom_ne_zero (stab a b) I_im_ne_zero
  rw [moeb_def, div_eq_iff hD, denom_stab_I h, stab_00 h, stab_01 h]
  linear_combination (b : ℂ) * Complex.I_sq

theorem stab_smul_I {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    stab a b • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_smul_eq_moeb (det_stab_pos h)]
  exact moeb_stab_I h

theorem denom_mul_stab_I (r : BinaryRealGL) {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    denom (r * stab a b) Complex.I = denom r Complex.I * ((a : ℂ) - b * Complex.I) := by
  rw [denom_mul r (stab a b) I_im_ne_zero, moeb_stab_I h, denom_stab_I h]

/-- The classical lift has weight `k` under the stabiliser of `i`. -/
theorem liftReal_mul_stab {k : ℕ} (f : CuspForm binaryRealGammaOneThree (k : ℤ))
    (r : BinaryRealGL) {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    liftReal f (r * stab a b) =
      ((⟨a, b⟩ : ℂ) / ((‖(⟨a, b⟩ : ℂ)‖ : ℝ) : ℂ)) ^ k * liftReal f r := by
  have hS := sumSq_pos h
  have hdet : (GeneralLinearGroup.det (r * stab a b) : ℝˣ).val =
      (GeneralLinearGroup.det r : ℝˣ).val * (a ^ 2 + b ^ 2) := by
    rw [map_mul, Units.val_mul, det_stab h]
  have hsqrt : Real.sqrt |(GeneralLinearGroup.det (r * stab a b) : ℝˣ).val| =
      Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| * Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [hdet, abs_mul, abs_of_pos hS, Real.sqrt_mul (abs_nonneg _)]
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = Real.sqrt (a ^ 2 + b ^ 2) := Complex.norm_eq_sqrt_sq_add_sq _
  have hD : (a : ℂ) - b * Complex.I ≠ 0 := by
    have h0 := denom_ne_zero (stab a b) I_im_ne_zero
    rwa [denom_stab_I h] at h0
  have hw : ((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hS).ne'
  have hkey : ((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) / ((a : ℂ) - b * Complex.I) =
      (⟨a, b⟩ : ℂ) / ((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
    rw [div_eq_iff hD, div_mul_eq_mul_div, eq_div_iff hw, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hS.le, Complex.mk_eq_add_mul_I]
    push_cast
    linear_combination (b : ℂ) ^ 2 * Complex.I_sq
  rw [liftReal_eq_denom, liftReal_eq_denom, mul_smul, stab_smul_I h, denom_mul_stab_I r h, hsqrt,
    hn, ← hkey, Complex.ofReal_mul]
  simp only [_root_.zpow_neg, zpow_natCast, div_pow, mul_pow, mul_inv]
  ring

/-! ### Holomorphy -/

theorem det_gUp {z : ℂ} (hz : z.im ≠ 0) :
    (GeneralLinearGroup.det (gUp z) : ℝˣ).val = z.im := by
  rw [GeneralLinearGroup.val_det_apply, gl_det_eq, gUp_00 hz, gUp_01 hz, gUp_10 hz, gUp_11 hz]
  ring

theorem det_gUp_pos {z : ℂ} (hz : 0 < z.im) : 0 < (GeneralLinearGroup.det (gUp z) : ℝˣ).val := by
  rw [det_gUp hz.ne']
  exact hz

theorem gUp_smul_I {z : ℂ} (hz : 0 < z.im) :
    gUp z • UpperHalfPlane.I = (⟨z, hz⟩ : UpperHalfPlane) := by
  apply UpperHalfPlane.ext
  rw [coe_smul_eq_moeb (det_gUp_pos hz)]
  exact moeb_gUp_I hz.ne'

/-- The classical lift along `z ↦ r · gUp z`. -/
theorem liftReal_mul_gUp {k : ℕ} (f : CuspForm binaryRealGammaOneThree (k : ℤ))
    (r : BinaryRealGL) {z : ℂ} (hz : 0 < z.im) :
    liftReal f (r * gUp z) =
      ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
        ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((denom r z ^ k)⁻¹ * f (r • (⟨z, hz⟩ : UpperHalfPlane))) := by
  have hdet : (GeneralLinearGroup.det (r * gUp z) : ℝˣ).val =
      (GeneralLinearGroup.det r : ℝˣ).val * z.im := by
    rw [map_mul, Units.val_mul, det_gUp hz.ne']
  have hsqrt : Real.sqrt |(GeneralLinearGroup.det (r * gUp z) : ℝˣ).val| =
      Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| * Real.sqrt z.im := by
    rw [hdet, abs_mul, abs_of_pos hz, Real.sqrt_mul (abs_nonneg _)]
  have hpow : ((Real.sqrt z.im : ℝ) : ℂ) ^ k = ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, sqrt_pow_eq_rpow hz.le]
  rw [liftReal_eq_denom, mul_smul, gUp_smul_I hz, denom_mul r (gUp z) I_im_ne_zero,
    moeb_gUp_I hz.ne', denom_gUp hz.ne', mul_one, hsqrt, Complex.ofReal_mul]
  simp only [_root_.zpow_neg, zpow_natCast, mul_pow, hpow]
  ring

end LiftFields

open LiftFields

/-- The weight law of the adelic lift under the archimedean stabiliser of `i`. -/
theorem adelicLift_mul_stab {k : ℕ} (f : CuspForm binaryRealGammaOneThree (k : ℤ))
    (x : BinaryAdelicGL) {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    adelicLift f (x * atInfinity (stab a b)) =
      ((⟨a, b⟩ : ℂ) / ((‖(⟨a, b⟩ : ℂ)‖ : ℝ) : ℂ)) ^ k * adelicLift f x := by
  obtain ⟨_, r, _, hx⟩ := exists_isDecomp x
  rw [← infGL_apply, adelicLift_mul_infGL f hx (det_stab_pos h), adelicLift_eq_of_isDecomp f hx,
    liftReal_mul_stab f r h]

/-- Holomorphy of the adelic lift along `z ↦ x · gUp z`. -/
theorem differentiableOn_adelicLift_gUp {k : ℕ} (f : CuspForm binaryRealGammaOneThree (k : ℤ))
    (x : BinaryAdelicGL) :
    DifferentiableOn ℂ
      (fun z : ℂ => (((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
        adelicLift f (x * atInfinity (gUp z))) upper := by
  obtain ⟨_, r, _, hx⟩ := exists_isDecomp x
  have hr := hx.1
  have hF : DifferentiableOn ℂ (fun z : ℂ => f (r • UpperHalfPlane.ofComplex z)) upper := by
    have hmd := (CuspFormClass.holo f).comp (UpperHalfPlane.mdifferentiable_smul hr)
    exact UpperHalfPlane.mdifferentiable_iff.mp hmd
  have hD : DifferentiableOn ℂ (fun z : ℂ => (denom r z ^ k)⁻¹) upper := by
    intro w hw
    have hne : denom r w ≠ 0 := denom_ne_zero r (mem_upper_iff.1 hw).ne'
    exact ((((differentiable_denom r) w).pow k).inv (pow_ne_zero k hne)).differentiableWithinAt
  have hH : DifferentiableOn ℂ (fun z : ℂ =>
      ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
        ((denom r z ^ k)⁻¹ * f (r • UpperHalfPlane.ofComplex z))) upper :=
    (hD.mul hF).const_mul (((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k)
  refine hH.congr fun z hz => ?_
  have hz' := mem_upper_iff.1 hz
  rw [← infGL_apply, adelicLift_mul_infGL f hx (det_gUp_pos hz'), liftReal_mul_gUp f r hz',
    UpperHalfPlane.ofComplex_apply_of_im_pos hz', Complex.ofReal_inv]
  exact inv_mul_mul_mul_cancel_aux
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hz' _).ne')

/-! ### The submodule of holomorphic functions of weight `k` -/

/-- The analytic fields of `FiniteModel k` for a function on `GL₂(𝔸)`: continuity, weight `k`
under `stab a b`, and holomorphy of `z ↦ (Im z)^(-k/2) φ (x · gUp z)` on the upper half plane. -/
structure IsHolomorphicWeight (k : ℕ) (φ : BinaryAdelicGL → ℂ) : Prop where
  continuous : Continuous φ
  weight : ∀ (x : BinaryAdelicGL) (a b : ℝ), a ^ 2 + b ^ 2 ≠ 0 →
    φ (x * atInfinity (stab a b)) = ((⟨a, b⟩ : ℂ) / ((‖(⟨a, b⟩ : ℂ)‖ : ℝ) : ℂ)) ^ k * φ x
  holomorphic : ∀ x : BinaryAdelicGL, DifferentiableOn ℂ
    (fun z : ℂ => (((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * φ (x * atInfinity (gUp z))) upper

namespace IsHolomorphicWeight

variable {k : ℕ} {φ ψ : BinaryAdelicGL → ℂ}

theorem add (h : IsHolomorphicWeight k φ) (h' : IsHolomorphicWeight k ψ) :
    IsHolomorphicWeight k (φ + ψ) where
  continuous := h.continuous.add h'.continuous
  weight x a b hab := by
    simp only [Pi.add_apply, h.weight x a b hab, h'.weight x a b hab, mul_add]
  holomorphic x := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ =>
        (((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * φ (x * atInfinity (gUp z)) +
          (((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * ψ (x * atInfinity (gUp z))) upper :=
      (h.holomorphic x).add (h'.holomorphic x)
    refine h1.congr fun z _ => ?_
    simp only [Pi.add_apply, mul_add]

theorem smul (c : ℂ) (h : IsHolomorphicWeight k φ) : IsHolomorphicWeight k (c • φ) where
  continuous := h.continuous.const_smul c
  weight x a b hab := by
    simp only [Pi.smul_apply, smul_eq_mul, h.weight x a b hab]
    ring
  holomorphic x := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ =>
        c * ((((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * φ (x * atInfinity (gUp z)))) upper :=
      (h.holomorphic x).const_mul c
    refine h1.congr fun z _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem zero : IsHolomorphicWeight k (0 : BinaryAdelicGL → ℂ) where
  continuous := continuous_const
  weight _ _ _ _ := by simp
  holomorphic _ := by
    simp only [Pi.zero_apply, mul_zero]
    exact differentiableOn_const 0

/-- Right translation by `GL₂(𝔸_f)` preserves the three fields: it commutes with the
archimedean component. -/
theorem translate_finite (h : IsHolomorphicWeight k φ) (u : BinaryFiniteGL) :
    IsHolomorphicWeight k (fun x => φ (x * atFinite u)) where
  continuous := h.continuous.comp (continuous_id.mul continuous_const)
  weight x a b hab := by
    simp only [LiftFields.mul_atInfinity_mul_atFinite]
    exact h.weight (x * atFinite u) a b hab
  holomorphic x := by
    simpa only [LiftFields.mul_atInfinity_mul_atFinite] using h.holomorphic (x * atFinite u)

end IsHolomorphicWeight

/-- The functions on `GL₂(𝔸)` satisfying the analytic fields of `FiniteModel k`. -/
def holomorphicWeightSubmodule (k : ℕ) : Submodule ℂ (BinaryAdelicGL → ℂ) where
  carrier := {φ | IsHolomorphicWeight k φ}
  add_mem' h h' := h.add h'
  zero_mem' := IsHolomorphicWeight.zero
  smul_mem' c _ h := h.smul c

/-- Every adelic lift of a weight-`k` cusp form of `Γ₁(3)` has the analytic fields. -/
theorem adelicLift_isHolomorphicWeight {k : ℕ} (f : CuspForm binaryRealGammaOneThree (k : ℤ)) :
    IsHolomorphicWeight k (adelicLift f) where
  continuous := Automorphic.Petersson.continuous_adelicLift f
  weight x _ _ hab := adelicLift_mul_stab f x hab
  holomorphic x := differentiableOn_adelicLift_gUp f x

/-- The right translate of a lift by `GL₂(𝔸_f)` has the analytic fields. -/
theorem adelicLift_translate_isHolomorphicWeight {k : ℕ}
    (f : CuspForm binaryRealGammaOneThree (k : ℤ)) (u : BinaryFiniteGL) :
    IsHolomorphicWeight k (fun x => adelicLift f (x * atFinite u)) :=
  (adelicLift_isHolomorphicWeight f).translate_finite u

/-- Continuity of the right translates of a lift by `GL₂(𝔸_f)`. -/
theorem continuous_adelicLift_translate {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (u : BinaryFiniteGL) : Continuous fun x => adelicLift f (x * atFinite u) :=
  (Automorphic.Petersson.continuous_adelicLift f).comp (continuous_id.mul continuous_const)

/-- The weight law for the right translates of a lift by `GL₂(𝔸_f)`. -/
theorem adelicLift_translate_mul_stab {k : ℕ} (f : CuspForm binaryRealGammaOneThree (k : ℤ))
    (u : BinaryFiniteGL) (x : BinaryAdelicGL) {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    adelicLift f (x * atInfinity (stab a b) * atFinite u) =
      ((⟨a, b⟩ : ℂ) / ((‖(⟨a, b⟩ : ℂ)‖ : ℝ) : ℂ)) ^ k * adelicLift f (x * atFinite u) :=
  (adelicLift_translate_isHolomorphicWeight f u).weight x a b h

/-- Holomorphy of the right translates of a lift by `GL₂(𝔸_f)`. -/
theorem differentiableOn_adelicLift_translate_gUp {k : ℕ}
    (f : CuspForm binaryRealGammaOneThree (k : ℤ)) (u : BinaryFiniteGL) (x : BinaryAdelicGL) :
    DifferentiableOn ℂ
      (fun z : ℂ => (((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
        adelicLift f (x * atInfinity (gUp z) * atFinite u)) upper :=
  (adelicLift_translate_isHolomorphicWeight f u).holomorphic x

/-- The span of the right translates of lifts by `GL₂(𝔸_f)` lies in the analytic submodule. -/
theorem span_translates_le_holomorphicWeight {k : ℕ}
    (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ))) :
    Submodule.span ℂ {φ | ∃ f ∈ S, ∃ u : BinaryFiniteGL,
        φ = fun x => adelicLift f (x * atFinite u)} ≤ holomorphicWeightSubmodule k := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨f, -, u, rfl⟩
  exact adelicLift_translate_isHolomorphicWeight f u

/-- The span of the right translates of lifts by `GL₂(𝔸_f)` has both the four scalar cuspidal
fields and the analytic fields. -/
theorem span_translates_le_cuspidalLike_inf {k : ℕ}
    (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ))) :
    Submodule.span ℂ {φ | ∃ f ∈ S, ∃ u : BinaryFiniteGL,
        φ = fun x => adelicLift f (x * atFinite u)} ≤
      cuspidalLikeSubmodule (centralChar (k : ℤ)) ⊓ holomorphicWeightSubmodule k := by
  have hsub : {φ | ∃ f ∈ S, ∃ u : BinaryFiniteGL, φ = fun x => adelicLift f (x * atFinite u)} ⊆
      {φ | ∃ f ∈ S, ∃ g₀ : BinaryAdelicGL, φ = fun x => adelicLift f (x * g₀)} := by
    rintro φ ⟨f, hf, u, hφ⟩
    exact ⟨f, hf, atFinite u, hφ⟩
  exact le_inf ((Submodule.span_mono hsub).trans (span_translates_le S))
    (span_translates_le_holomorphicWeight S)

end TernaryPeriodPolynomials.Regularity

end
