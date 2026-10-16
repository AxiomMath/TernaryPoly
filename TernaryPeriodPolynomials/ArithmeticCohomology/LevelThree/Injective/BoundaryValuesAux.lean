module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Eval

@[expose] public section


/-!
# Decay and boundedness near the cusp `0` of cusp forms for `Γ₁(3)`

For a cusp form `f` on `Γ₁(3)` of any integral weight `k`, `f` and `f ∣[k] S` decay exponentially
at `i∞` (`decay_of_isBigO`). The identity `f(i t) = (f ∣[k] S)(i / t) (i / t)^k`
(`eq_slashS_mul`) converts the decay of `f ∣[k] S` into the boundedness of `t ↦ f(i t)` on
`(0, 1]` (`exists_bound_near_zero`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane Filter Asymptotics
open scoped Manifold ModularForm MatrixGroups Topology
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodWidth
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodEval (sG_denom)

namespace TernaryPeriodPolynomials.LevelThreeInjective.BoundaryValuesAux

/-! ### Exponential decay at `i∞` -/

/-- A big-O bound at `i∞` is an explicit bound on all points of large imaginary part. -/
theorem decay_of_isBigO {g : ℍ → ℂ} {κ : ℝ} (hκ : 0 < κ)
    (h : g =O[UpperHalfPlane.atImInfty] fun z : ℍ => Real.exp (-κ * z.im)) :
    ∃ C κ' A : ℝ, 0 < κ' ∧ ∀ z : ℂ, A ≤ z.im →
      ‖g (ofComplex z)‖ ≤ C * Real.exp (-κ' * z.im) := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hC
  refine ⟨C, κ, max A 1, hκ, fun z hz => ?_⟩
  have hpos : 0 < z.im := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hz)
  have hz' : A ≤ (⟨z, hpos⟩ : ℍ).im := le_trans (le_max_left _ _) hz
  have h1 := hA ⟨z, hpos⟩ hz'
  rw [ofComplex_apply_of_im_pos hpos]
  simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using h1

/-- Exponential decay of a cusp form for `Γ₁(3)` at `i∞`. -/
theorem decay_form {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    ∃ C κ A : ℝ, 0 < κ ∧ ∀ z : ℂ, A ≤ z.im →
      ‖f (ofComplex z)‖ ≤ C * Real.exp (-κ * z.im) :=
  decay_of_isBigO (κ := 2 * Real.pi) (by positivity)
    ((gammaOneThree_exp_decay f).congr_right (fun z => by congr 1; ring))

/-- Exponential decay at `i∞` of the slash of a cusp form for `Γ₁(3)` by `S`. -/
theorem decay_slashS {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    ∃ C κ A : ℝ, 0 < κ ∧ ∀ z : ℂ, A ≤ z.im →
      ‖((⇑f) ∣[k] ModularGroup.S) (ofComplex z)‖ ≤ C * Real.exp (-κ * z.im) := by
  have h := gammaOneThree_ST_exp_decay f 0
  rw [pow_zero, mul_one] at h
  exact decay_of_isBigO (κ := 2 * Real.pi / 3) (by positivity)
    (h.congr_right (fun z => by congr 1; ring))

/-! ### The points `i t` and the slash by `S` -/

/-- The point `i t` of the upper half-plane. -/
def iPt (t : ℝ) (ht : 0 < t) : ℍ := ⟨Complex.I * (t : ℂ), by simpa using ht⟩

theorem iPt_coe (t : ℝ) (ht : 0 < t) : (iPt t ht : ℂ) = Complex.I * (t : ℂ) := rfl

theorem ofComplex_iPt (t : ℝ) (ht : 0 < t) : ofComplex (Complex.I * (t : ℂ)) = iPt t ht := by
  have h : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  exact (ofComplex_apply_of_im_pos h).trans rfl

/-- `(g ∣[k] S) z = g (S z) z^{-k}`. -/
theorem slashS_apply (k : ℤ) (g : ℍ → ℂ) (z : ℍ) :
    (g ∣[k] ModularGroup.S) z = g (sG • z) * (z : ℂ) ^ (-k) := by
  have h := slash_apply_of_det_pos k g sG (by rw [sG_det]; exact one_pos) z
  rw [sG_det, Complex.ofReal_one, _root_.one_zpow, mul_one, sG_denom] at h
  exact h

/-- `S (i / t) = i t`. -/
theorem sG_smul_iPt_inv (t : ℝ) (ht : 0 < t) :
    sG • iPt t⁻¹ (inv_pos.mpr ht) = iPt t ht := by
  apply UpperHalfPlane.ext
  rw [sG_coe, iPt_coe, iPt_coe, Complex.ofReal_inv]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hI : Complex.I * (t : ℂ)⁻¹ ≠ 0 := mul_ne_zero Complex.I_ne_zero (inv_ne_zero ht')
  rw [div_eq_iff hI]
  have h1 : (t : ℂ) * (t : ℂ)⁻¹ = 1 := mul_inv_cancel₀ ht'
  linear_combination (-(t : ℂ) * (t : ℂ)⁻¹) * Complex.I_mul_I + h1

/-- `g(i t) = (g ∣[k] S)(i / t) (i / t)^k`. -/
theorem eq_slashS_mul (k : ℤ) (g : ℍ → ℂ) (t : ℝ) (ht : 0 < t) :
    g (iPt t ht) = (g ∣[k] ModularGroup.S) (iPt t⁻¹ (inv_pos.mpr ht)) *
      (Complex.I * ((t⁻¹ : ℝ) : ℂ)) ^ k := by
  have hne : Complex.I * ((t⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr ht).ne')
  rw [slashS_apply, sG_smul_iPt_inv, iPt_coe, mul_assoc, ← zpow_add₀ hne, neg_add_cancel,
    zpow_zero, mul_one]

theorem norm_eq_slashS (k : ℤ) (g : ℍ → ℂ) (t : ℝ) (ht : 0 < t) :
    ‖g (ofComplex (Complex.I * (t : ℂ)))‖ =
      ‖(g ∣[k] ModularGroup.S) (ofComplex (Complex.I * ((t⁻¹ : ℝ) : ℂ)))‖ * t⁻¹ ^ k := by
  rw [ofComplex_iPt t ht, ofComplex_iPt t⁻¹ (inv_pos.mpr ht), eq_slashS_mul k g t ht, norm_mul,
    norm_zpow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_pos.mpr ht).le]

/-! ### Boundedness on `(0, 1]` -/

theorem exists_bound_pow_exp (k : ℤ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C B : ℝ, 1 ≤ B ∧ ∀ s : ℝ, B ≤ s → s ^ k * Real.exp (-κ * s) ≤ C := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (isLittleO_pow_exp_pos_mul_atTop k.toNat hκ).isBigO
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hC
  refine ⟨C, max B 1, le_max_right _ _, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hpos : 0 < s := lt_of_lt_of_le one_pos hs1
  have h1 := hB s (le_trans (le_max_left _ _) hs)
  have h2 : s ^ k.toNat ≤ C * Real.exp (κ * s) := by
    simpa [Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (Real.exp_pos _).le] using h1
  have h3 : s ^ k ≤ s ^ k.toNat := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ hs1 (by omega)
  have h4 : κ * s + -κ * s = 0 := by ring
  calc s ^ k * Real.exp (-κ * s) ≤ s ^ k.toNat * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ ≤ C * Real.exp (κ * s) * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = C := by rw [mul_assoc, ← Real.exp_add, h4, Real.exp_zero, mul_one]

/-- A cusp form for `Γ₁(3)` is bounded along `t ↦ i t` for `t ∈ (0, 1]`. -/
theorem exists_bound_near_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f (ofComplex (Complex.I * (t : ℂ)))‖ ≤ C := by
  obtain ⟨C0, κ, A, hκ, hdecay⟩ := decay_slashS f
  obtain ⟨C1, B, hB1, hC1⟩ := exists_bound_pow_exp k hκ
  have hB'1 : 1 ≤ max B (max A 1) := le_trans hB1 (le_max_left _ _)
  have hB'pos : 0 < max B (max A 1) := lt_of_lt_of_le one_pos hB'1
  have hsub : Set.Icc (max B (max A 1))⁻¹ 1 ⊆ Set.Ioi 0 :=
    fun t ht => lt_of_lt_of_le (inv_pos.mpr hB'pos) ht.1
  have hcont : ContinuousOn (fun t : ℝ => f (ofComplex (Complex.I * (t : ℂ))))
      (Set.Icc (max B (max A 1))⁻¹ 1) :=
    (CuspFormClass.holo f).continuous.comp_continuousOn
      (continuousOn_ofComplex_I_mul.mono hsub)
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C2 (|C0| * C1), fun t ht ht1 => ?_⟩
  by_cases hts : t ≤ (max B (max A 1))⁻¹
  · have hs : max B (max A 1) ≤ t⁻¹ := (le_inv_comm₀ ht hB'pos).mp hts
    have hsB : B ≤ t⁻¹ := le_trans (le_max_left _ _) hs
    have hsA : A ≤ t⁻¹ := le_trans (le_trans (le_max_left A 1) (le_max_right _ _)) hs
    have him : (Complex.I * ((t⁻¹ : ℝ) : ℂ)).im = t⁻¹ := by simp
    have h1 := hdecay (Complex.I * ((t⁻¹ : ℝ) : ℂ)) (by rw [him]; exact hsA)
    rw [him] at h1
    have hP : 0 ≤ t⁻¹ ^ k := zpow_nonneg (inv_nonneg.mpr ht.le) k
    rw [norm_eq_slashS k (⇑f) t ht]
    refine le_trans ?_ (le_max_right _ _)
    calc ‖((⇑f) ∣[k] ModularGroup.S) (ofComplex (Complex.I * ((t⁻¹ : ℝ) : ℂ)))‖ * t⁻¹ ^ k
        ≤ (C0 * Real.exp (-κ * t⁻¹)) * t⁻¹ ^ k := mul_le_mul_of_nonneg_right h1 hP
      _ ≤ (|C0| * Real.exp (-κ * t⁻¹)) * t⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.exp_pos _).le) hP
      _ = |C0| * (t⁻¹ ^ k * Real.exp (-κ * t⁻¹)) := by ring
      _ ≤ |C0| * C1 := mul_le_mul_of_nonneg_left (hC1 _ hsB) (abs_nonneg _)
  · exact le_trans (hC2 t ⟨(not_le.mp hts).le, ht1⟩) (le_max_left _ _)

end TernaryPeriodPolynomials.LevelThreeInjective.BoundaryValuesAux
