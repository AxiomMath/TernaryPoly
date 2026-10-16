module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Summand
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


/-!
# The uniform value bound of the summands (Appendix C.3, Proposition C.4)

On a compact set `K ⊂ Ω` every coefficient of every summand is bounded by a constant multiple of
`t(g q)^{-(n+3)/2}` where `t(g q) = (planeAct g q) 4` is the normal height, for any `h` with
`‖h(τ)‖ (Im τ)^{(n+3)/2}` bounded (for example a cusp form of weight `n + 3`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The uniform value bound of the summand -/

theorem fderiv_decompR_eq {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) :
    fderiv ℝ (decompR g q) q =
      (fderiv ℝ (planeAct (kFactor g q)) basePt).comp (fderiv ℝ (planeAct (planePinv q)) q) := by
  have h1 : DifferentiableAt ℝ (planeAct (planePinv q)) q :=
    differentiableAt_planeAct (det_planePinv hq) hq
  have h2 : DifferentiableAt ℝ (planeAct (kFactor g q)) (planeAct (planePinv q) q) := by
    rw [planeAct_planePinv_self hq]
    exact differentiableAt_planeAct (det_kFactor hg hq) basePt_mem
  have := fderiv_comp q h2 h1
  rw [planeAct_planePinv_self hq] at this
  exact this

theorem kFactor_mem_SOrth {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) : matToFun (kFactor g q) ∈ SOrth :=
  ⟨kFactor_orth hg hq, det_kFactor hg hq⟩

theorem decompR_component_bound {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) (N1 N2 : ℝ)
    (h1 : ∀ k ∈ SOrth, ‖fderiv ℝ (planeAct (matOfFun k)) basePt‖ ≤ N1)
    (h2 : ‖fderiv ℝ (planeAct (planePinv q)) q‖ ≤ N2) (i c : Fin 5) :
    |fderiv ℝ (decompR g q) q (Pi.single i 1) c| ≤ max N1 0 * max N2 0 := by
  have hk := h1 _ (kFactor_mem_SOrth hg hq)
  have hk' : ‖fderiv ℝ (planeAct (kFactor g q)) basePt‖ ≤ max N1 0 :=
    hk.trans (le_max_left _ _)
  have h2' : ‖fderiv ℝ (planeAct (planePinv q)) q‖ ≤ max N2 0 := h2.trans (le_max_left _ _)
  rw [fderiv_decompR_eq hg hq]
  calc |((fderiv ℝ (planeAct (kFactor g q)) basePt).comp
          (fderiv ℝ (planeAct (planePinv q)) q)) (Pi.single i 1) c|
      ≤ ‖((fderiv ℝ (planeAct (kFactor g q)) basePt).comp
          (fderiv ℝ (planeAct (planePinv q)) q)) (Pi.single i 1)‖ := abs_apply_le_norm _ c
    _ ≤ ‖(fderiv ℝ (planeAct (kFactor g q)) basePt).comp
          (fderiv ℝ (planeAct (planePinv q)) q)‖ * ‖(Pi.single i (1 : ℝ) : Fin 5 → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(fderiv ℝ (planeAct (kFactor g q)) basePt).comp
          (fderiv ℝ (planeAct (planePinv q)) q)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_single_le_one i) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ (planeAct (kFactor g q)) basePt‖ * ‖fderiv ℝ (planeAct (planePinv q)) q‖ := by
        rw [mul_one]; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max N1 0 * max N2 0 :=
        mul_le_mul hk' h2' (norm_nonneg _) (le_max_right _ _)

theorem sqrt_two_mul_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (2 * a ^ 2 / b ^ 2) = Real.sqrt 2 * (a / b) := by
  rw [show 2 * a ^ 2 / b ^ 2 = 2 * (a / b) ^ 2 by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (div_pos ha hb).le]

theorem rpow_half_eq (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (a ^ 2) ^ (((n : ℝ) + 3) / 2) = a ^ (n + 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast a, ← Real.rpow_mul ha.le]
  congr 1
  push_cast
  ring

/-- **Value bound.** On a compact `K ⊂ Ω`, the coefficients of every summand are bounded by a
constant multiple of `t(g q)^{-(n+3)/2}`, where `t(g q) = (planeAct g q) 4` is the normal height. -/
theorem summand_value_bound (n : ℕ) (h : ℂ → ℂ) (Ch : ℝ)
    (hh : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ * τ.im ^ (((n : ℝ) + 3) / 2) ≤ Ch)
    {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ C : ℝ, ∀ (g : Matrix (Fin 3) (Fin 3) ℝ), g.det = 1 → ∀ q ∈ K, ∀ (i j : Fin 5)
      (m : Fin 3 →₀ ℕ), ‖(summandPoly n h g q i j).coeff m‖ ≤
        C / (Real.sqrt (planeAct g q 4)) ^ (n + 3) := by
  obtain ⟨Λ, hΛ⟩ := exists_bound_planePinv hK hKΩ
  obtain ⟨N1, hN1⟩ := exists_bound_fderiv_SOrth
  obtain ⟨N2, hN2⟩ := exists_bound_fderiv_pinv hK hKΩ
  have hCh : 0 ≤ Ch := by
    have := hh Complex.I (by simp)
    rw [Complex.I_im, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  set N := max N1 0 * max N2 0 with hNdef
  have hN0 : 0 ≤ N := by positivity
  set L := max Λ 0 with hL
  refine ⟨50 * N ^ 2 * (9 * L * Real.sqrt 2) ^ n * Ch, fun g hg q hq i j m => ?_⟩
  have hqΩ := hKΩ hq
  have hq'' := planeAct_mem hg hqΩ
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hq''
  have hsa : Real.sqrt (planeAct g q 3) = a := by rw [e3]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt (planeAct g q 4) = b := by rw [e4]; exact Real.sqrt_sq hb.le
  have hcoef := coeff_summand_le n h hg q i j m
  have hs := norm_scalar_summand_le h hg hqΩ i j N (fun c =>
    ⟨decompR_component_bound hg hqΩ N1 N2 hN1 (hN2 q hq) i c,
     decompR_component_bound hg hqΩ N1 N2 hN1 (hN2 q hq) j c⟩)
  have hr : ∀ l, ‖∑ k : Fin 3, seedRow (planeAct g q) k * (g k l : ℂ)‖ ≤
      3 * L * (Real.sqrt 2 * (a / b)) := by
    intro l
    have := rowForm_bound hg hqΩ L (fun l' j' => (hΛ q hq l' j').trans (le_max_left _ _)) l
    rw [e3, e4, sqrt_two_mul_div a b ha hb] at this
    exact this
  have hR : ∑ l : Fin 3, ‖∑ k : Fin 3, seedRow (planeAct g q) k * (g k l : ℂ)‖ ≤
      9 * L * Real.sqrt 2 * (a / b) := by
    calc _ ≤ ∑ _l : Fin 3, 3 * L * (Real.sqrt 2 * (a / b)) := Finset.sum_le_sum fun l _ => hr l
      _ = 9 * L * Real.sqrt 2 * (a / b) := by simp; ring
  have hhτ : ‖h (seedTau (planeAct g q))‖ * a ^ (n + 3) ≤ Ch := by
    have := hh (seedTau (planeAct g q)) (by simpa [seedTau] using hq''.1)
    have him : (seedTau (planeAct g q)).im = planeAct g q 3 := by simp [seedTau]
    rw [him, e3, rpow_half_eq a ha n] at this
    exact this
  rw [hsa, hsb] at hs
  have hu : 0 < a / b := div_pos ha hb
  have hL0 : 0 ≤ L := le_max_right _ _
  set u := a / b with hudef
  have hmain : ‖(summandPoly n h g q i j).coeff m‖ ≤
      25 * (N * N * (2 * (u ^ 3 * ‖h (seedTau (planeAct g q))‖))) *
        (9 * L * Real.sqrt 2 * u) ^ n := by
    refine hcoef.trans ?_
    refine mul_le_mul hs (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hR n)
      (pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) n) ?_
    positivity
  refine hmain.trans ?_
  rw [hsb]
  have hbn : 0 < b ^ (n + 3) := pow_pos hb _
  rw [le_div_iff₀ hbn]
  have e : 25 * (N * N * (2 * (u ^ 3 * ‖h (seedTau (planeAct g q))‖))) *
        (9 * L * Real.sqrt 2 * u) ^ n * b ^ (n + 3) =
      50 * N ^ 2 * (9 * L * Real.sqrt 2) ^ n * (‖h (seedTau (planeAct g q))‖ * a ^ (n + 3)) := by
    rw [mul_pow, hudef, div_pow, div_pow]
    field_simp
    ring
  rw [e]
  have h50 : 0 ≤ 50 * N ^ 2 * (9 * L * Real.sqrt 2) ^ n := by positivity
  exact mul_le_mul_of_nonneg_left hhτ h50

end TernaryPeriodPolynomials.Argument.ConvergenceC4
