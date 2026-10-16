module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.EllipticUnit
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.RotationRigidity
public import Mathlib.NumberTheory.ModularForms.Identities

@[expose] public section


/-!
# A level-one cusp form supported on multiples of three vanishes

If `f ∈ S_k(SL₂(ℤ))`, `k > 0`, has `a_n(f) = 0` for every `n` prime to `3`, then `f(z + 1/3) = f(z)`, so `f` is
invariant (in weight `k`) under the elliptic element `g = S T^{1/3} : z ↦ -1/(z + 1/3)` of trace `1/3`.
In the Cayley coordinate at the fixed point `τ₀ = (-1 + i√35)/6` the element `g` is the rotation by
`κ = ellipticConj²`, and `h(w) = f(z(w)) (z(w) - τ̄₀)^k` satisfies `h(κ w) = ellipticRoot^k h(w)`. Since
`ellipticRoot` is not a root of unity (`EllipticUnit`), `RotationRigidity` gives `h = 0`, hence `f = 0`
(`eq_zero_of_coeff_coprime_three`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane Complex Metric
open TernaryPeriodPolynomials.Spectral.EllipticUnit

namespace TernaryPeriodPolynomials.Spectral.LevelOneThreeVanishing

open LevelOneHecke

theorem sum_roots : ellipticRoot + ellipticConj = 1 / 3 := by unfold ellipticConj; ring

theorem root_re : ellipticRoot.re = 1 / 6 := by simp [ellipticRoot]
theorem root_im : ellipticRoot.im = Real.sqrt 35 / 6 := by simp [ellipticRoot]
theorem conj_re : ellipticConj.re = 1 / 6 := by
  simp only [ellipticConj, sub_re, root_re]; norm_num
theorem conj_im : ellipticConj.im = -(Real.sqrt 35 / 6) := by
  simp only [ellipticConj, sub_im, root_im]; norm_num

theorem sqrt35_pos : 0 < Real.sqrt 35 := Real.sqrt_pos.mpr (by norm_num)

theorem normSq_root : normSq ellipticRoot = 1 := by
  rw [normSq_apply, root_re, root_im]
  have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 35 by norm_num)
  nlinarith

theorem normSq_conj : normSq ellipticConj = 1 := by
  rw [normSq_apply, conj_re, conj_im]
  have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 35 by norm_num)
  nlinarith

theorem norm_eq_one_of_normSq {x : ℂ} (h : normSq x = 1) : ‖x‖ = 1 := by
  have h2 := Complex.normSq_eq_norm_sq x
  rw [h] at h2
  nlinarith [norm_nonneg x]

theorem norm_root : ‖ellipticRoot‖ = 1 := norm_eq_one_of_normSq normSq_root
theorem norm_conj : ‖ellipticConj‖ = 1 := norm_eq_one_of_normSq normSq_conj

theorem root_sub_conj_ne_zero : ellipticRoot - ellipticConj ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [sub_im, root_im, conj_im, zero_im] at this
  linarith [sqrt35_pos]

theorem conj_ne_zero : ellipticConj ≠ 0 := by
  intro h
  have := normSq_conj
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem conj_inv : ellipticConj⁻¹ = ellipticRoot := by
  rw [ellipticConj_eq_inv, inv_inv]

/-- `normSq (z + j') - normSq (z + j) = -4 b Im z` with `b = √35/6`. -/
theorem normSq_sub (z : ℂ) :
    normSq (z + ellipticConj) - normSq (z + ellipticRoot) = -4 * (Real.sqrt 35 / 6) * z.im := by
  simp only [normSq_apply, add_re, add_im, root_re, root_im, conj_re, conj_im]
  ring

theorem normSq_lt_iff (z : ℂ) :
    normSq (z + ellipticConj) < normSq (z + ellipticRoot) ↔ 0 < z.im := by
  have h := normSq_sub z
  have hb : 0 < Real.sqrt 35 / 6 := by linarith [sqrt35_pos]
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    nlinarith
  · intro hpos
    nlinarith

/-- The inverse Cayley map `w ↦ (τ₀ - τ̄₀ w)/(1 - w)` with `τ₀ = -j'`, `τ̄₀ = -j`. -/
def zOf (w : ℂ) : ℂ := (-ellipticConj + ellipticRoot * w) / (1 - w)

theorem one_sub_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this, mem_ball_zero_iff, norm_one] at hw
  exact lt_irrefl _ hw

theorem zOf_add_root {w : ℂ} (hw : 1 - w ≠ 0) :
    zOf w + ellipticRoot = (ellipticRoot - ellipticConj) / (1 - w) := by
  unfold zOf
  field_simp
  ring

theorem zOf_add_conj {w : ℂ} (hw : 1 - w ≠ 0) :
    zOf w + ellipticConj = w * (zOf w + ellipticRoot) := by
  rw [zOf_add_root hw]
  unfold zOf
  field_simp
  ring

theorem zOf_add_root_ne_zero {w : ℂ} (hw : 1 - w ≠ 0) : zOf w + ellipticRoot ≠ 0 := by
  rw [zOf_add_root hw]
  exact div_ne_zero root_sub_conj_ne_zero hw

theorem zOf_im_pos {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 0 < (zOf w).im := by
  have h1 := one_sub_ne_zero hw
  apply (normSq_lt_iff (zOf w)).mp
  rw [zOf_add_conj h1, map_mul]
  have hw' : normSq w < 1 := by
    rw [mem_ball_zero_iff] at hw
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hpos : 0 < normSq (zOf w + ellipticRoot) := normSq_pos.mpr (zOf_add_root_ne_zero h1)
  nlinarith

/-- `zOf (j'² w) = -1/(zOf w + 1/3)`: the elliptic element `S T^{1/3}` is the rotation by `j'²`. -/
theorem zOf_rotate {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    zOf (ellipticConj ^ 2 * w) = -1 / (zOf w + 1 / 3) := by
  have h1 := one_sub_ne_zero hw
  have hjj := ellipticRoot_mul_conj
  have hsum := sum_roots
  have hnorm : ‖ellipticConj * w‖ < 1 := by
    rw [norm_mul, norm_conj, one_mul]; rwa [mem_ball_zero_iff] at hw
  have h2 : ellipticRoot - ellipticConj * w ≠ 0 := by
    intro h
    have : ellipticRoot = ellipticConj * w := by linear_combination h
    have hn := congrArg norm this
    rw [norm_root] at hn
    linarith
  have h3 : 1 - ellipticConj ^ 2 * w ≠ 0 := by
    intro h
    have : 1 = ellipticConj ^ 2 * w := by linear_combination h
    have hn := congrArg norm this
    rw [norm_one, norm_mul, norm_pow, norm_conj, one_pow, one_mul] at hn
    rw [mem_ball_zero_iff] at hw
    linarith
  have h4 : zOf w + 1 / 3 = (ellipticRoot - ellipticConj * w) / (1 - w) := by
    unfold zOf
    field_simp
    linear_combination (-(1 : ℂ) + w) * hsum * 3
  rw [h4]
  unfold zOf
  have hR : -1 / ((ellipticRoot - ellipticConj * w) / (1 - w)) =
      -(1 - w) / (ellipticRoot - ellipticConj * w) := by
    field_simp
  rw [hR, div_eq_div_iff h3 h2]
  linear_combination (-(1 - (ellipticRoot * ellipticConj + 1) * w + ellipticConj ^ 2 * w ^ 2)) * hjj

section Modular

variable {k : ℤ} (f : CuspForm levelOne k)

/-- Coefficients supported on multiples of three give invariance under `z ↦ z + 1/3`. -/
theorem translate_third (hcoeff : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0) (τ : ℍ) :
    f ((1 / 3 : ℝ) +ᵥ τ) = f τ := by
  have hτ := ModularForm.hasSum_qExpansion f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods τ
  have hτ' := ModularForm.hasSum_qExpansion f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods
    ((1 / 3 : ℝ) +ᵥ τ)
  have hterm : ∀ n, (qExpansion 1 f).coeff n * Function.Periodic.qParam 1 ↑((1 / 3 : ℝ) +ᵥ τ) ^ n =
      (qExpansion 1 f).coeff n * Function.Periodic.qParam 1 ↑τ ^ n := by
    intro n
    by_cases hn : 3 ∣ n
    · obtain ⟨m, rfl⟩ := hn
      congr 1
      rw [UpperHalfPlane.coe_vadd, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
        ← Complex.exp_nat_mul]
      have : (↑(3 * m) : ℂ) * (2 * ↑Real.pi * Complex.I * (↑(1 / 3 : ℝ) + ↑τ) / ↑(1 : ℝ)) =
          ↑(3 * m) * (2 * ↑Real.pi * Complex.I * ↑τ / ↑(1 : ℝ)) + (m : ℤ) * (2 * ↑Real.pi * Complex.I) := by
        push_cast
        ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · rw [hcoeff n hn, zero_mul, zero_mul]
  simp only [hterm] at hτ'
  exact hτ'.unique hτ

/-- The `S`-transformation `f(-1/τ) = τ^k f(τ)`. -/
theorem S_transform (τ : ℍ) :
    f (UpperHalfPlane.mk (-(τ : ℂ))⁻¹ τ.im_inv_neg_coe_pos) = (τ : ℂ) ^ k * f τ := by
  have hinv : (⇑f ∣[k] ModularGroup.S) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ ⟨ModularGroup.S, rfl⟩
  have h := congrFun hinv τ
  rw [SlashInvariantForm.slash_S_apply] at h
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [← h, mul_comm, mul_assoc, ← zpow_add₀ hτ0, neg_add_cancel, zpow_zero, mul_one]

/-- The complexified form. -/
def Fc (z : ℂ) : ℂ := f (UpperHalfPlane.ofComplex z)

theorem Fc_of_im_pos {z : ℂ} (hz : 0 < z.im) : Fc f z = f ⟨z, hz⟩ := by
  unfold Fc
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem Fc_differentiableOn : DifferentiableOn ℂ (Fc f) {z | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp f.holo'

/-- **The elliptic functional equation** `F(-1/(z + 1/3)) = (z + 1/3)^k F(z)` on the upper half plane. -/
theorem Fc_elliptic (hcoeff : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0) {z : ℂ} (hz : 0 < z.im) :
    Fc f (-1 / (z + 1 / 3)) = (z + 1 / 3) ^ k * Fc f z := by
  set τ : ℍ := ⟨z, hz⟩
  set τ' : ℍ := (1 / 3 : ℝ) +ᵥ τ
  have hτ' : (τ' : ℂ) = z + 1 / 3 := by
    simp only [τ', τ, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have him : 0 < (-1 / (z + 1 / 3)).im := by
    have := τ'.im_inv_neg_coe_pos
    rw [hτ'] at this
    convert this using 2
    field_simp
  rw [Fc_of_im_pos f him, Fc_of_im_pos f hz]
  have hS := S_transform f τ'
  have hpt : (⟨-1 / (z + 1 / 3), him⟩ : ℍ) = UpperHalfPlane.mk (-(τ' : ℂ))⁻¹ τ'.im_inv_neg_coe_pos := by
    apply UpperHalfPlane.ext
    simp only [hτ']
    field_simp
  rw [hpt, hS, hτ', translate_third f hcoeff τ]

end Modular

section Vanishing

variable {k : ℤ} (f : CuspForm levelOne k)

/-- `h(w) = F(z(w)) (z(w) - τ̄₀)^k` on the unit disc. -/
def discFun (w : ℂ) : ℂ := Fc f (zOf w) * (zOf w + ellipticRoot) ^ k

theorem zOf_differentiableOn : DifferentiableOn ℂ zOf (ball 0 1) := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  unfold zOf
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact one_sub_ne_zero hw

theorem discFun_differentiableOn : DifferentiableOn ℂ (discFun f) (ball 0 1) := by
  apply DifferentiableOn.mul
  · exact (Fc_differentiableOn f).comp zOf_differentiableOn (fun w hw => zOf_im_pos hw)
  · intro w hw
    apply DifferentiableWithinAt.zpow
    · exact (zOf_differentiableOn w hw).add_const _
    · left; exact zOf_add_root_ne_zero (one_sub_ne_zero hw)

theorem elliptic_add_root {z : ℂ} (hz : z + 1 / 3 ≠ 0) :
    -1 / (z + 1 / 3) + ellipticRoot = (z + ellipticRoot) / ((z + 1 / 3) * ellipticConj) := by
  have hjj := ellipticRoot_mul_conj
  have hsum := sum_roots
  rw [div_add' _ _ _ hz, div_eq_div_iff hz (mul_ne_zero hz conj_ne_zero)]
  linear_combination (z + 1 / 3) ^ 2 * hjj - (z + 1 / 3) * hsum

theorem discFun_rotate (hcoeff : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    discFun f (ellipticConj ^ 2 * w) = ellipticRoot ^ k * discFun f w := by
  have him := zOf_im_pos hw
  have hz3 : zOf w + 1 / 3 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, zero_im] at this
    have h3 : ((1 : ℂ) / 3).im = 0 := by norm_num
    linarith
  have hk3 : (zOf w + 1 / 3) ^ k ≠ 0 := zpow_ne_zero _ hz3
  have hjk : (ellipticConj ^ k)⁻¹ = ellipticRoot ^ k := by
    rw [← _root_.inv_zpow, conj_inv]
  unfold discFun
  have hjk0 : ellipticConj ^ k ≠ 0 := zpow_ne_zero _ conj_ne_zero
  rw [zOf_rotate hw, Fc_elliptic f hcoeff him, elliptic_add_root hz3, div_zpow, mul_zpow, ← hjk,
    div_eq_mul_inv ((zOf w + ellipticRoot) ^ k), mul_inv]
  have hcancel : (zOf w + 1 / 3) ^ k * ((zOf w + 1 / 3) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hk3
  linear_combination (Fc f (zOf w) * (zOf w + ellipticRoot) ^ k * (ellipticConj ^ k)⁻¹) * hcancel

theorem norm_lt_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    ‖(τ + ellipticConj) / (τ + ellipticRoot)‖ < 1 := by
  have hne : τ + ellipticRoot ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [add_im, root_im, zero_im] at this
    linarith [sqrt35_pos]
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  have h := (normSq_lt_iff τ).mpr hτ
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

theorem zOf_cayley {τ : ℂ} (hne : τ + ellipticRoot ≠ 0) :
    zOf ((τ + ellipticConj) / (τ + ellipticRoot)) = τ := by
  have hdiff := root_sub_conj_ne_zero
  have hden : 1 - (τ + ellipticConj) / (τ + ellipticRoot) ≠ 0 := by
    rw [one_sub_div hne]
    apply div_ne_zero _ hne
    intro h
    apply hdiff
    linear_combination h
  unfold zOf
  rw [div_eq_iff hden]
  field_simp
  ring

/-- **A level-one cusp form whose `q`-expansion is supported on multiples of three vanishes.** -/
theorem eq_zero_of_coeff_coprime_three (hk : 0 < k)
    (hcoeff : ∀ n, ¬ 3 ∣ n → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  have hc : ∀ N : ℕ, (ellipticConj ^ 2) ^ N ≠ ellipticRoot ^ k := by
    intro N h
    obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = K := ⟨k.toNat, (Int.toNat_of_nonneg hk.le).symm⟩
    have hK : 1 ≤ K := by exact_mod_cast hk
    rw [zpow_natCast] at h
    apply ellipticRoot_pow_ne_one (K + 2 * N) (by omega)
    have h1 : ellipticRoot ^ (2 * N) * (ellipticConj ^ 2) ^ N = 1 := by
      rw [← pow_mul, ← mul_pow, ellipticRoot_mul_conj, one_pow]
    rw [h] at h1
    rw [pow_add, mul_comm]
    exact h1
  have hzero := RotationRigidity.eq_zero_of_rotation (discFun_differentiableOn f) hc
    (fun w hw => discFun_rotate f hcoeff hw)
  ext τ
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have hne : (τ : ℂ) + ellipticRoot ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [add_im, root_im, zero_im] at this
    linarith [sqrt35_pos]
  have hw := hzero _ (mem_ball_zero_iff.mpr (norm_lt_of_im_pos hτ))
  unfold discFun at hw
  rw [zOf_cayley hne] at hw
  have hpow : ((τ : ℂ) + ellipticRoot) ^ k ≠ 0 := zpow_ne_zero _ hne
  have hF := (mul_eq_zero.mp hw).resolve_right hpow
  rw [Fc_of_im_pos f hτ] at hF
  simpa using hF

end Vanishing

end TernaryPeriodPolynomials.Spectral.LevelOneThreeVanishing
