module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Rotation

@[expose] public section


/-!
# Binomial expansion of translated lowest weight vectors

For complex numbers `u`, `v` with `‖v - i u‖ < ‖v + i u‖` the function `z ↦ ((u z + v)^k)⁻¹` on
the upper half plane has the Cayley coefficients
`(2 i)^k ((v + i u)^k)⁻¹ * C(n + k - 1, n) * q^n` with `q = (v - i u) / (v + i u)`
(`kernel_eq_upperSeries`, from the binomial series `(1 - x)^(-k) = ∑ C(n + k - 1, n) x^n`).
Writing the scaled coefficients of a Bergman vector in `ℓ²(ℕ ⊕ ℕ; E)` as `q ↦ ∑ qⁿ • (vₙ at ι n)`
gives a holomorphic function `theta` of `q` on the unit disc, hence a real analytic one
(`contDiffOn_theta`).
-/

noncomputable section

open MeasureTheory

namespace TernaryPeriodPolynomials.Regularity

/-! ### Linear kernels on the upper half plane -/

section Kernel

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The quotient `q = (v - i u) / (v + i u)`. -/
def kernelRatio (u v : ℂ) : ℂ := (v - Complex.I * u) / (v + Complex.I * u)

/-- The binomial coefficient `C(n + k - 1, n)` as a real number. -/
def binomR (k n : ℕ) : ℝ := (((n + (k - 1)).choose (k - 1) : ℕ) : ℝ)

/-- The binomial coefficient `C(n + k - 1, n)` as a complex number. -/
def binomCoeff (k n : ℕ) : ℂ := ((binomR k n : ℝ) : ℂ)

/-- The constant `r (2 i)^k ((v + i u)^k)⁻¹` in the Cayley coefficients of `r • (u z + v)^(-k)`. -/
def kernelScalar (k : ℕ) (r u v : ℂ) : ℂ :=
  r * (2 * Complex.I) ^ k * ((v + Complex.I * u) ^ k)⁻¹

/-- The Cayley coefficients of `z ↦ r • ((u z + v)^k)⁻¹ • e`. -/
def kernelCoeff (k : ℕ) (r u v : ℂ) (e : E) (n : ℕ) : E :=
  (kernelScalar k r u v * binomCoeff k n * kernelRatio u v ^ n) • e

theorem upper_add_I_ne_zero {z : ℂ} (hz : z ∈ upper) : z + Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hz' : 0 < z.im := hz
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith

theorem kernel_denom_ne_zero {u v : ℂ} (h : ‖v - Complex.I * u‖ < ‖v + Complex.I * u‖) :
    v + Complex.I * u ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at h
  exact absurd h (not_lt.2 (norm_nonneg _))

theorem norm_kernelRatio_lt_one {u v : ℂ} (h : ‖v - Complex.I * u‖ < ‖v + Complex.I * u‖) :
    ‖kernelRatio u v‖ < 1 := by
  have h0 : 0 < ‖v + Complex.I * u‖ := lt_of_le_of_lt (norm_nonneg _) h
  rw [kernelRatio, norm_div, div_lt_one h0]
  exact h

theorem binomR_nonneg (k n : ℕ) : 0 ≤ binomR k n := Nat.cast_nonneg _

theorem binomR_le (hk : 1 ≤ k) (n : ℕ) :
    binomR k n ≤ (k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [binomR, Nat.add_sub_cancel]
  have h1 : (((n + j).choose j : ℕ) : ℝ) ≤ ((n + j : ℕ) : ℝ) ^ j := by
    exact_mod_cast Nat.choose_le_pow (n + j) j
  have h2 : ((n + j : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc (((n + j).choose j : ℕ) : ℝ) ≤ ((n + j : ℕ) : ℝ) ^ j := h1
    _ ≤ (((j + 1 : ℕ) : ℝ) * ((n : ℝ) + 1)) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 j
    _ = ((j + 1 : ℕ) : ℝ) ^ j * ((n : ℝ) + 1) ^ j := mul_pow _ _ _

omit [CompleteSpace E] in
theorem norm_kernelCoeff_le (hk : 1 ≤ k) (r u v : ℂ) (e : E)
    (h : ‖v - Complex.I * u‖ < ‖v + Complex.I * u‖) (n : ℕ) :
    ‖kernelCoeff k r u v e n‖ ≤
      (‖kernelScalar k r u v‖ * (k : ℝ) ^ (k - 1) * ‖e‖) * ((n : ℝ) + 1) ^ (k - 1) := by
  have hq := norm_kernelRatio_lt_one h
  unfold kernelCoeff
  rw [norm_smul, norm_mul, norm_mul, norm_pow, binomCoeff, Complex.norm_real,
    Real.norm_of_nonneg (binomR_nonneg k n)]
  have h1 : ‖kernelRatio u v‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
  have h2 := binomR_le hk n
  have hS := norm_nonneg (kernelScalar k r u v)
  have he := norm_nonneg e
  have h3 : binomR k n * ‖kernelRatio u v‖ ^ n ≤
      ((k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1)) * 1 :=
    mul_le_mul h2 h1 (pow_nonneg (norm_nonneg _) _) (by positivity)
  calc ‖kernelScalar k r u v‖ * binomR k n * ‖kernelRatio u v‖ ^ n * ‖e‖
      = ‖kernelScalar k r u v‖ * (binomR k n * ‖kernelRatio u v‖ ^ n) * ‖e‖ := by ring
    _ ≤ ‖kernelScalar k r u v‖ * (((k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1)) * 1) * ‖e‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hS) he
    _ = (‖kernelScalar k r u v‖ * (k : ℝ) ^ (k - 1) * ‖e‖) * ((n : ℝ) + 1) ^ (k - 1) := by ring

omit [CompleteSpace E] in
/-- The Cayley expansion of `z ↦ r • ((u z + v)^k)⁻¹ • e` on the upper half plane. -/
theorem kernel_eq_upperSeries (hk : 1 ≤ k) (r u v : ℂ) (e : E)
    (h : ‖v - Complex.I * u‖ < ‖v + Complex.I * u‖) {z : ℂ} (hz : z ∈ upper) :
    r • ((u * z + v) ^ k)⁻¹ • e = upperSeries k (kernelCoeff k r u v e) z := by
  have hD : v + Complex.I * u ≠ 0 := kernel_denom_ne_zero h
  have hq : ‖kernelRatio u v‖ < 1 := norm_kernelRatio_lt_one h
  have hζ : ‖cay z‖ < 1 := norm_cay_lt_one hz
  have hzI : z + Complex.I ≠ 0 := upper_add_I_ne_zero hz
  have hqζ : ‖kernelRatio u v * cay z‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (kernelRatio u v), norm_nonneg (cay z)]
  have h1q : (1 : ℂ) - kernelRatio u v * cay z ≠ 0 := by
    intro h0
    have h2 : kernelRatio u v * cay z = 1 := by linear_combination -h0
    rw [h2, norm_one] at hqζ
    exact lt_irrefl _ hqζ
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have key : (1 - kernelRatio u v * cay z) * ((v + Complex.I * u) * (z + Complex.I)) =
      2 * Complex.I * (u * z + v) := by
    unfold kernelRatio cay
    field_simp
    ring
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) (k - 1) hqζ
  have hpow : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hpow] at hs
  have hsum : HasSum (fun n => cay z ^ n • kernelCoeff k r u v e n)
      ((kernelScalar k r u v * (1 / (1 - kernelRatio u v * cay z) ^ k)) • e) := by
    have h1 := (hs.mul_left (kernelScalar k r u v)).smul_const e
    have hfun : (fun n => cay z ^ n • kernelCoeff k r u v e n) =
        fun n => (kernelScalar k r u v * ((((n + (k - 1)).choose (k - 1) : ℕ) : ℂ) *
          (kernelRatio u v * cay z) ^ n)) • e := by
      funext n
      simp only [kernelCoeff, binomCoeff, binomR, Complex.ofReal_natCast, smul_smul]
      congr 1
      ring
    rw [hfun]
    exact h1
  have hu : u * z + v = (1 - kernelRatio u v * cay z) *
      ((v + Complex.I * u) * (z + Complex.I)) / (2 * Complex.I) := by
    rw [eq_div_iff h2I]
    linear_combination (-1 : ℂ) * key
  unfold upperSeries
  rw [hsum.tsum_eq, smul_smul, smul_smul]
  congr 1
  rw [hu]
  unfold kernelScalar
  field_simp
  have h2Ik : (Complex.I * 2) ^ k ≠ 0 := pow_ne_zero _ (by rw [mul_comm]; exact h2I)
  rw [div_pow, mul_assoc r (((1 - kernelRatio u v * cay z) * (v + Complex.I * u) *
    (z + Complex.I)) ^ k / (Complex.I * 2) ^ k) _, div_mul_cancel₀ _ h2Ik, mul_pow, mul_pow]
  ring

/-- The coefficients of a function equal to `r • ((u z + v)^k)⁻¹ • e` on the upper half plane. -/
theorem upperCoeff_of_eqOn_kernel (hk : 1 ≤ k) {G : ℂ → E} (r u v : ℂ) (e : E)
    (h : ‖v - Complex.I * u‖ < ‖v + Complex.I * u‖)
    (hG : ∀ z ∈ upper, G z = r • ((u * z + v) ^ k)⁻¹ • e) (n : ℕ) :
    upperCoeff k G n = kernelCoeff k r u v e n := by
  have h1 : upperCoeff k G n = upperCoeff k (upperSeries k (kernelCoeff k r u v e)) n :=
    upperCoeff_congr (fun z hz => by rw [hG z hz, kernel_eq_upperSeries hk r u v e h hz]) n
  rw [h1]
  exact upperCoeff_upperSeries (norm_kernelCoeff_le hk r u v e h) n

/-- The coefficients of a function vanishing on the upper half plane. -/
theorem upperCoeff_of_eqOn_zero {G : ℂ → E} (hG : ∀ z ∈ upper, G z = 0) (n : ℕ) :
    upperCoeff k G n = 0 :=
  (upperCoeff_congr (G' := fun _ : ℂ => (0 : E)) (fun z hz => hG z hz) n).trans
    (upperCoeff_zero_fun n)

end Kernel

/-! ### A holomorphic family of vectors in `ℓ²(ℕ ⊕ ℕ; E)` -/

section Theta

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The vector with value `x n` at the coordinate `ι n`. -/
def thetaTerm (ι : ℕ → ℕ ⊕ ℕ) (x : ℕ → E) (n : ℕ) : lp (fun _ : ℕ ⊕ ℕ => E) 2 :=
  lp.single 2 (ι n) (x n)

/-- The vector `∑ qⁿ • thetaTerm n`, with value `qⁿ • x n` at the coordinate `ι n`. -/
def theta (ι : ℕ → ℕ ⊕ ℕ) (x : ℕ → E) (q : ℂ) : lp (fun _ : ℕ ⊕ ℕ => E) 2 :=
  ∑' n, q ^ n • thetaTerm ι x n

/-- Evaluation at a coordinate, as a continuous linear map. -/
def lpEval (j : ℕ ⊕ ℕ) : lp (fun _ : ℕ ⊕ ℕ => E) 2 →L[ℂ] E :=
  lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℕ ⊕ ℕ => E) (p := 2) j

omit [CompleteSpace E] in
theorem lpEval_apply (j : ℕ ⊕ ℕ) (f : lp (fun _ : ℕ ⊕ ℕ => E) 2) : lpEval j f = f j := rfl

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem norm_thetaTerm (ι : ℕ → ℕ ⊕ ℕ) (x : ℕ → E) (n : ℕ) : ‖thetaTerm ι x n‖ = ‖x n‖ :=
  lp.norm_single (by norm_num) _ _

theorem differentiableOn_theta (ι : ℕ → ℕ ⊕ ℕ) {x : ℕ → E} {C : ℝ} {N : ℕ}
    (hx : ∀ n, ‖x n‖ ≤ C * ((n : ℝ) + 1) ^ N) :
    DifferentiableOn ℂ (theta ι x) (Metric.ball 0 1) :=
  differentiableOn_tsum_of_bound (c := thetaTerm ι x) fun n => by
    rw [norm_thetaTerm]
    exact hx n

theorem contDiffOn_theta (ι : ℕ → ℕ ⊕ ℕ) {x : ℕ → E} {C : ℝ} {N : ℕ}
    (hx : ∀ n, ‖x n‖ ≤ C * ((n : ℝ) + 1) ^ N) :
    ContDiffOn ℝ ⊤ (theta ι x) (Metric.ball 0 1) :=
  ((differentiableOn_theta ι hx).contDiffOn Metric.isOpen_ball).restrict_scalars ℝ

theorem hasSum_theta (ι : ℕ → ℕ ⊕ ℕ) {x : ℕ → E} {C : ℝ} {N : ℕ}
    (hx : ∀ n, ‖x n‖ ≤ C * ((n : ℝ) + 1) ^ N) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => q ^ n • thetaTerm ι x n) (theta ι x q) := by
  have hc : ∀ n, ‖thetaTerm ι x n‖ ≤ C * ((n : ℝ) + 1) ^ N := fun n => by
    rw [norm_thetaTerm]
    exact hx n
  have hs : Summable (fun n => q ^ n • thetaTerm ι x n) := by
    refine Summable.of_norm ?_
    refine (summable_norm_of_bound hc (norm_nonneg q) hq).congr fun n => ?_
    rw [norm_smul, norm_pow, mul_comm]
  exact hs.hasSum

omit [CompleteSpace E] in
theorem lpEval_smul_thetaTerm (ι : ℕ → ℕ ⊕ ℕ) (x : ℕ → E) (q : ℂ) (n : ℕ) (j : ℕ ⊕ ℕ) :
    lpEval j (q ^ n • thetaTerm ι x n) = q ^ n • (Pi.single (ι n) (x n) : ℕ ⊕ ℕ → E) j := rfl

/-- The coordinate `ι m` of `theta` is `qᵐ • x m`. -/
theorem theta_apply_self (ι : ℕ → ℕ ⊕ ℕ) (hι : Function.Injective ι) {x : ℕ → E} {C : ℝ}
    {N : ℕ} (hx : ∀ n, ‖x n‖ ≤ C * ((n : ℝ) + 1) ^ N) {q : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    theta ι x q (ι m) = q ^ m • x m := by
  have h1 := (lpEval (E := E) (ι m)).hasSum (hasSum_theta ι hx hq)
  have h2 : HasSum (fun n => lpEval (ι m) (q ^ n • thetaTerm ι x n))
      (lpEval (ι m) (q ^ m • thetaTerm ι x m)) :=
    hasSum_single m fun n hn => by
      rw [lpEval_smul_thetaTerm, Pi.single_eq_of_ne (fun h => hn (hι h).symm), smul_zero]
  have h3 := h1.unique h2
  rw [lpEval_apply] at h3
  rw [h3, lpEval_smul_thetaTerm, Pi.single_eq_same]

/-- The coordinates outside the range of `ι` vanish. -/
theorem theta_apply_of_forall_ne (ι : ℕ → ℕ ⊕ ℕ) {x : ℕ → E} {C : ℝ} {N : ℕ}
    (hx : ∀ n, ‖x n‖ ≤ C * ((n : ℝ) + 1) ^ N) {q : ℂ} (hq : ‖q‖ < 1) (j : ℕ ⊕ ℕ)
    (hj : ∀ n, ι n ≠ j) : theta ι x q j = 0 := by
  have h1 := (lpEval (E := E) j).hasSum (hasSum_theta ι hx hq)
  have h2 : HasSum (fun n => lpEval j (q ^ n • thetaTerm ι x n)) 0 := by
    have hz : (fun n => lpEval j (q ^ n • thetaTerm ι x n)) = fun _ => (0 : E) :=
      funext fun n => by
        rw [lpEval_smul_thetaTerm, Pi.single_eq_of_ne (fun h => hj n h.symm), smul_zero]
    rw [hz]
    exact hasSum_zero
  have h3 := h1.unique h2
  rwa [lpEval_apply] at h3

end Theta

/-! ### The vectors `n ↦ √(4^(1-k) βₙ) C(n + k - 1, n) • e` -/

section Vectors

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coordinates `√(4^(1-k) βₙ) C(n + k - 1, n) • e` of the translated lowest weight vectors. -/
def thetaVec (k : ℕ) (e : E) (n : ℕ) : E :=
  ((bergmanScale k n * binomR k n : ℝ) : ℂ) • e

theorem discMoment_anti {m m' : ℕ} (h : m' ≤ m) {a : ℝ} (ha : -1 < a) :
    discMoment m a ≤ discMoment m' a := by
  unfold discMoment
  refine setIntegral_mono_on (integrableOn_moment m ha) (integrableOn_moment m' ha)
    Metric.isOpen_ball.measurableSet ?_
  intro ζ hζ
  have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  have h2 : 0 ≤ (1 - ‖ζ‖ ^ 2) ^ a := Real.rpow_nonneg (by nlinarith [norm_nonneg ζ]) _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) h1.le h) h2

theorem bergmanScale_le (hk : 2 ≤ k) (n : ℕ) : bergmanScale k n ≤ bergmanScale k 0 := by
  unfold bergmanScale
  refine Real.sqrt_le_sqrt ?_
  unfold bergmanWeight
  refine mul_le_mul_of_nonneg_left ?_ (BergmanAux.four_rpow_pos k).le
  have ha : (-1 : ℝ) < (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact discMoment_anti (Nat.mul_le_mul_left 2 (Nat.zero_le n)) ha

theorem norm_thetaVec_le (hk : 2 ≤ k) (e : E) (n : ℕ) :
    ‖thetaVec k e n‖ ≤
      (bergmanScale k 0 * (k : ℝ) ^ (k - 1) * ‖e‖) * ((n : ℝ) + 1) ^ (k - 1) := by
  unfold thetaVec
  rw [norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (bergmanScale_nonneg k n) (binomR_nonneg k n))]
  have h1 := bergmanScale_le hk n
  have h2 := binomR_le (by omega : 1 ≤ k) n
  have h3 : bergmanScale k n * binomR k n ≤
      bergmanScale k 0 * ((k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1)) :=
    mul_le_mul h1 h2 (binomR_nonneg k n) (bergmanScale_nonneg k 0)
  calc bergmanScale k n * binomR k n * ‖e‖
      ≤ bergmanScale k 0 * ((k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1)) * ‖e‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg e)
    _ = (bergmanScale k 0 * (k : ℝ) ^ (k - 1) * ‖e‖) * ((n : ℝ) + 1) ^ (k - 1) := by ring

end Vectors

end TernaryPeriodPolynomials.Regularity

end
