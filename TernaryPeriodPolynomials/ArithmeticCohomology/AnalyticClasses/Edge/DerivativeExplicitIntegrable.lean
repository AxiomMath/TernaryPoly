module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitBounds

@[expose] public section


/-!
# Integrability of the mixed derivative vector and of its closed form

Every scalar test of the mixed derivative vector is continuous in the good-line coordinate and
bounded by `C (1 + s² + t²)^{-(n+3)/4}`: the transfer scale has that size, the values of the
scalar form at `i` are bounded uniformly in the adelic point, the coefficients `cᵢ` are bounded
by `54`, and the coefficient action of the orthogonal factor has bounded tests. The two terms of
the closed form satisfy the same bound, since `|F_h(z(u))| ≤ C (α / √R)^{n+3}` and
`‖E‖ ≤ 3 α R`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### The coefficient action of the orthogonal factor -/

theorem continuous_gsOrth_inv : Continuous fun u : ℝ × ℝ => (gsOrth u)⁻¹ := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun u => (gsOrthMatrix u)ᵀ
    exact continuous_gsOrthMatrix.matrix_transpose
  · simp only [inv_inv]
    exact continuous_gsOrthMatrix

theorem abs_gsOrthMatrix_le (u : ℝ × ℝ) (a b : Fin 3) : |gsOrthMatrix u a b| ≤ 1 := by
  have row : ∑ c, gsOrthMatrix u a c * gsOrthMatrix u a c = 1 := by
    have := congrFun (congrFun (gsOrthMatrix_mul_transpose u) a) a
    simpa [Matrix.mul_apply] using this
  have single := Finset.single_le_sum (fun c _ => mul_self_nonneg (gsOrthMatrix u a c))
    (Finset.mem_univ b)
  rw [← sq_le_one_iff_abs_le_one, sq]
  linarith

/-- Complex matrices with entries in the closed unit disc. -/
def unitEntries : Set (Matrix (Fin 3) (Fin 3) ℂ) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall 0 1

theorem isCompact_unitEntries : IsCompact unitEntries :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1

theorem complexOrth_mem_unitEntries (u : ℝ × ℝ) : complexOrth u ∈ unitEntries := by
  intro a _ b _
  simpa [complexOrth_apply, Complex.norm_real] using abs_gsOrthMatrix_le u a b

/-- **Bounded tests of the coefficient action of the orthogonal factor.** -/
theorem exists_bound_functional_coefficient (Q : HomogeneousPoly n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ M, ∀ u, ‖functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ Q)‖ ≤ M := by
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    obtain ⟨M, hM⟩ := isCompact_unitEntries.exists_bound_of_continuousOn
      (substitute_coeff_continuous Q.val monomial).continuousOn
    refine ⟨M, fun u => ?_⟩
    change ‖(realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ Q).val.coeff monomial‖ ≤ M
    rw [realCoefficientComponent_gsOrth_inv_val, coeff_C_mul, det_gsOrthMatrix, norm_mul]
    simpa [complexOrth] using hM _ (complexOrth_mem_unitEntries u)
  | zero => exact ⟨0, fun u => by simp⟩
  | add first second _ _ hfirst hsecond =>
    obtain ⟨M, hM⟩ := hfirst
    obtain ⟨M', hM'⟩ := hsecond
    exact ⟨M + M', fun u => (norm_add_le _ _).trans (add_le_add (hM u) (hM' u))⟩
  | smul c functional _ hfunctional =>
    obtain ⟨M, hM⟩ := hfunctional
    refine ⟨‖c‖ * M, fun u => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hM u) (norm_nonneg c)

theorem continuous_functional_coefficient (Q : HomogeneousPoly n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous fun u => functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ Q) :=
  realCoefficientComponent_functional_continuous _ continuous_gsOrth_inv Q functional

/-! ### The mixed derivative vector as a combination -/

theorem ternaryLin_isHomogeneous (a b : ℂ) : (ternaryLin a b).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)

/-- The power `(a X₀ + b X₁)ⁿ` as a ternary homogeneous polynomial. -/
def ternaryLinPow (n : ℕ) (a b : ℂ) : HomogeneousPoly n :=
  ⟨ternaryLin a b ^ n, by simpa using (ternaryLin_isHomogeneous a b).pow n⟩

theorem edgeMixedVector_eq_smul (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (i : Fin 2)
    (h : BinaryAdelicGL) :
    edgeMixedVector n F u i h =
      (transferScale n u * (2⁻¹ * F (movedPoint u h) Complex.I * ((n : ℂ) + 1) * holCoeff u i)) •
          realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
            (ternaryLinPow n 1 (-Complex.I)) +
        (transferScale n u * (2⁻¹ * F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I *
          ((n : ℂ) + 1) * antiCoeff u i)) •
          realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
            (ternaryLinPow n (-1) (-Complex.I)) := by
  apply Subtype.ext
  rw [edgeMixedVector_val, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    realCoefficientComponent_gsOrth_inv_val, realCoefficientComponent_gsOrth_inv_val]
  simp only [complexOrth, ternaryLinPow, map_add, map_mul, map_pow, substitute_C', smul_eq_C_mul]
  ring

/-! ### Bounds for the coefficients -/

theorem norm_cubicP_le {E N : ℂ} (h : ‖N‖ ≤ ‖E‖) : ‖cubicP E N‖ ≤ 8 * ‖E‖ ^ 3 := by
  have hE := norm_nonneg E
  have hN := norm_nonneg N
  calc ‖cubicP E N‖ ≤ ‖E‖ ^ 3 + 3 * ‖E‖ ^ 2 * ‖N‖ + 3 * ‖E‖ * ‖N‖ ^ 2 + ‖N‖ ^ 3 := by
        rw [cubicP]
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
          simp [norm_pow]
    _ ≤ 8 * ‖E‖ ^ 3 := by nlinarith [mul_le_mul h h hN hE, pow_le_pow_left₀ hN h 3]

theorem norm_cubicQ_le {E N : ℂ} (h : ‖N‖ ≤ ‖E‖) : ‖cubicQ E N‖ ≤ 8 * ‖E‖ ^ 3 := by
  have hE := norm_nonneg E
  have hN := norm_nonneg N
  calc ‖cubicQ E N‖ ≤ ‖E‖ ^ 3 + 3 * ‖E‖ ^ 2 * ‖N‖ + 3 * ‖E‖ * ‖N‖ ^ 2 + ‖N‖ ^ 3 := by
        rw [cubicQ]
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
          simp [norm_pow]
    _ ≤ 8 * ‖E‖ ^ 3 := by nlinarith [mul_le_mul h h hN hE, pow_le_pow_left₀ hN h 3]

theorem norm_le_of_cubic_identity {c E a R cube unit : ℂ} (ha : a ≠ 0) (hR : R ≠ 0)
    (hE : ‖E‖ ≤ 3 * ‖a‖ * ‖R‖) (hcube : ‖cube‖ ≤ 8 * ‖E‖ ^ 3) (hunit : ‖unit‖ = 1)
    (h : c * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 = 2 * Complex.I * a ^ 3 * (unit * cube)) :
    ‖c‖ ≤ 54 := by
  have hn := congrArg norm h
  simp only [norm_mul, norm_pow, Complex.norm_I, hunit, Complex.norm_ofNat, mul_one,
    one_mul] at hn
  have ha' := norm_pos_iff.mpr ha
  have hR' := norm_pos_iff.mpr hR
  have hE0 := norm_nonneg E
  have bound : ‖cube‖ ≤ 8 * (3 * ‖a‖ * ‖R‖) ^ 3 :=
    hcube.trans (by gcongr)
  have key : ‖c‖ * (8 * ‖a‖ ^ 6 * ‖R‖ ^ 3) ≤ 54 * (8 * ‖a‖ ^ 6 * ‖R‖ ^ 3) := by
    have e : ‖c‖ * (8 * ‖a‖ ^ 6 * ‖R‖ ^ 3) = 2 * ‖a‖ ^ 3 * ‖cube‖ := by
      rw [← hn]
      ring
    rw [e]
    nlinarith [pow_pos ha' 3]
  exact le_of_mul_le_mul_right key (by positivity)

theorem norm_holN_le (u : ℝ × ℝ) : ‖holN u‖ ≤ ‖holE u‖ :=
  (norm_lt_of_parts (by rw [holN_re, holE_re]) (by rw [holN_im, holE_im]; exact im_sq_lt u)).le

theorem norm_antiN_le (u : ℝ × ℝ) : ‖antiN u‖ ≤ ‖antiE u‖ :=
  (norm_lt_of_parts (by rw [antiN_re, antiE_re])
    (by rw [antiN_im, antiE_im]; exact im_sq_lt u)).le

theorem norm_holE_le' (u : ℝ × ℝ) :
    ‖holE u‖ ≤ 3 * ‖(gsAlpha u : ℂ)‖ * ‖(gsRadius u : ℂ)‖ := by
  rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (gsAlpha_pos u).le,
    Real.norm_of_nonneg (gsRadius_pos u).le]
  exact norm_holE_le u

theorem norm_antiE_le' (u : ℝ × ℝ) :
    ‖antiE u‖ ≤ 3 * ‖(gsAlpha u : ℂ)‖ * ‖(gsRadius u : ℂ)‖ := by
  rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (gsAlpha_pos u).le,
    Real.norm_of_nonneg (gsRadius_pos u).le]
  exact norm_antiE_le u

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

theorem norm_holCoeff_le (u : ℝ × ℝ) (i : Fin 2) : ‖holCoeff u i‖ ≤ 54 := by
  obtain rfl | rfl := fin_two_cases i
  · exact norm_le_of_cubic_identity (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u)
      (norm_holE_le' u) (norm_cubicQ_le (norm_holN_le u)) Complex.norm_I (holCoeff_zero_eq u)
  · exact norm_le_of_cubic_identity (unit := -1) (gsAlpha_complex_ne_zero u)
      (gsRadius_complex_ne_zero u) (norm_holE_le' u) (norm_cubicP_le (norm_holN_le u))
      (by simp) (by rw [holCoeff_one_eq]; ring)

theorem norm_antiCoeff_le (u : ℝ × ℝ) (i : Fin 2) : ‖antiCoeff u i‖ ≤ 54 := by
  obtain rfl | rfl := fin_two_cases i
  · exact norm_le_of_cubic_identity (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u)
      (norm_antiE_le' u) (norm_cubicQ_le (norm_antiN_le u)) (by simp) (antiCoeff_zero_eq u)
  · exact norm_le_of_cubic_identity (unit := -1) (gsAlpha_complex_ne_zero u)
      (gsRadius_complex_ne_zero u) (norm_antiE_le' u) (norm_cubicP_le (norm_antiN_le u))
      (by simp) (by rw [antiCoeff_one_eq]; ring)

/-! ### Continuity in the good-line coordinate -/

theorem goodPoint_im (u : ℝ × ℝ) : (goodPoint u).im = gsRadius u / gsAlpha u ^ 2 := by
  rw [goodPoint, ← Complex.ofReal_pow, Complex.div_ofReal_im]
  simp

theorem goodPoint_im_pos (u : ℝ × ℝ) : 0 < (goodPoint u).im := by
  rw [goodPoint_im]
  have := gsRadius_pos u
  have := gsAlpha_pos u
  positivity

theorem reflection_goodPoint_im_pos (u : ℝ × ℝ) :
    0 < (binaryComplexReflection (goodPoint u)).im := by
  rw [binaryComplexReflection_im]
  exact goodPoint_im_pos u

theorem continuous_complex_gsAlpha : Continuous fun u : ℝ × ℝ => (gsAlpha u : ℂ) :=
  Complex.continuous_ofReal.comp continuous_gsAlpha

theorem continuous_complex_gsRadius : Continuous fun u : ℝ × ℝ => (gsRadius u : ℂ) :=
  Complex.continuous_ofReal.comp continuous_gsRadius

theorem continuous_goodPoint : Continuous goodPoint := by
  have ha := continuous_complex_gsAlpha
  have hR := continuous_complex_gsRadius
  refine Continuous.div (by fun_prop) (ha.pow 2) fun u => pow_ne_zero 2
    (gsAlpha_complex_ne_zero u)

theorem continuous_scalar_goodPoint {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (h : BinaryAdelicGL) : Continuous fun u => F h (goodPoint u) :=
  (hF.holomorphic h).continuousOn.comp_continuous continuous_goodPoint goodPoint_im_pos

theorem continuous_scalar_reflection {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (h : BinaryAdelicGL) : Continuous fun u => F h (binaryComplexReflection (goodPoint u)) :=
  (hF.holomorphic h).continuousOn.comp_continuous
    (binaryComplexReflection.continuous.comp continuous_goodPoint) reflection_goodPoint_im_pos

theorem continuous_sqrt_gsRadius : Continuous fun u : ℝ × ℝ => (Real.sqrt (gsRadius u) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_gsRadius.sqrt)

theorem continuous_levi_scale (k : ℕ) :
    Continuous fun u : ℝ × ℝ =>
      (((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ k)⁻¹ := by
  have hq := continuous_sqrt_gsRadius
  refine Continuous.inv₀ ?_ fun u => ?_
  · simp only [Complex.ofReal_div]
    exact (continuous_complex_gsAlpha.div hq fun u => sqrt_gsRadius_complex_ne_zero u).pow k
  · rw [Complex.ofReal_div]
    exact pow_ne_zero k (div_ne_zero (gsAlpha_complex_ne_zero u)
      (sqrt_gsRadius_complex_ne_zero u))

theorem continuous_movedValue {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (h : BinaryAdelicGL) : Continuous fun u => F (movedPoint u h) Complex.I := by
  simp only [eichlerData_movedPoint hF]
  exact (continuous_levi_scale (n + 3)).mul (continuous_scalar_goodPoint hF h)

theorem continuous_movedValue_J {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (h : BinaryAdelicGL) :
    Continuous fun u => F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I := by
  simp only [eichlerData_movedPoint_J hF]
  exact (continuous_levi_scale (n + 3)).mul (continuous_scalar_reflection hF _)

theorem continuous_transferScale : Continuous fun u : ℝ × ℝ => transferScale n u := by
  simp only [transferScale_eq]
  exact (continuous_sqrt_gsRadius.pow (n + 3)).inv₀ fun u =>
    pow_ne_zero _ (sqrt_gsRadius_complex_ne_zero u)

theorem continuous_holE : Continuous holE := by
  have ha := continuous_complex_gsAlpha
  have hR := continuous_complex_gsRadius
  unfold holE
  fun_prop

theorem continuous_holN : Continuous holN := by
  have ha := continuous_complex_gsAlpha
  have hR := continuous_complex_gsRadius
  unfold holN
  fun_prop

theorem continuous_antiE : Continuous antiE := by
  have ha := continuous_complex_gsAlpha
  have hR := continuous_complex_gsRadius
  unfold antiE
  fun_prop

theorem continuous_antiN : Continuous antiN := by
  have ha := continuous_complex_gsAlpha
  have hR := continuous_complex_gsRadius
  unfold antiN
  fun_prop

theorem continuous_of_cubic_identity {c cube : ℝ × ℝ → ℂ} (hcube : Continuous cube)
    (h : ∀ u, c u * (2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 * (gsRadius u : ℂ) ^ 3 =
      cube u) : Continuous c := by
  have nonzero : ∀ u, (2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 * (gsRadius u : ℂ) ^ 3 ≠ 0 :=
    fun u => mul_ne_zero (pow_ne_zero 3 (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (pow_ne_zero 2 (gsAlpha_complex_ne_zero u)))) (pow_ne_zero 3 (gsRadius_complex_ne_zero u))
  have e : c = fun u => cube u / ((2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 *
      (gsRadius u : ℂ) ^ 3) :=
    funext fun u => eq_div_of_mul_eq (nonzero u) (by rw [← mul_assoc]; exact h u)
  rw [e]
  have ha := continuous_complex_gsAlpha
  have hR := continuous_complex_gsRadius
  exact hcube.div (by fun_prop) nonzero

theorem continuous_holCoeff (i : Fin 2) : Continuous fun u => holCoeff u i := by
  have hE := continuous_holE
  have hN := continuous_holN
  have ha := continuous_complex_gsAlpha
  obtain rfl | rfl := fin_two_cases i
  · exact continuous_of_cubic_identity (by unfold cubicQ; fun_prop) holCoeff_zero_eq
  · exact continuous_of_cubic_identity (by unfold cubicP; fun_prop) holCoeff_one_eq

theorem continuous_antiCoeff (i : Fin 2) : Continuous fun u => antiCoeff u i := by
  have hE := continuous_antiE
  have hN := continuous_antiN
  have ha := continuous_complex_gsAlpha
  obtain rfl | rfl := fin_two_cases i
  · exact continuous_of_cubic_identity (by unfold cubicQ; fun_prop) antiCoeff_zero_eq
  · exact continuous_of_cubic_identity (by unfold cubicP; fun_prop) antiCoeff_one_eq

/-! ### Integrability of the tests of the mixed derivative vector -/

theorem exists_bound_at_I {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F) :
    ∃ C, 0 ≤ C ∧ ∀ h, ‖F h Complex.I‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bounded {Complex.I} (by simp) isCompact_singleton
  exact ⟨max C 0, le_max_right _ _, fun h => (hC h _ rfl).trans (le_max_left _ _)⟩

theorem norm_transferScale (u : ℝ × ℝ) :
    ‖transferScale n u‖ = (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n + 3 : ℕ) : ℝ) / 4)) := by
  rw [transferScale_eq, norm_inv_sqrt_pow]

/-- A continuous function bounded by `C (1 + s² + t²)^{-p}`, `p > 1`, is integrable. -/
theorem integrable_of_continuous_decay {f : ℝ × ℝ → ℂ} (hf : Continuous f) {C p : ℝ}
    (hp : 1 < p) (bound : ∀ u : ℝ × ℝ, ‖f u‖ ≤ C * (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-p)) :
    Integrable f :=
  integrable_of_decay hf.aestronglyMeasurable hp bound

theorem decay_exponent (large : 2 ≤ n) : 1 < ((n + 3 : ℕ) : ℝ) / 4 := by
  rw [lt_div_iff₀ (by norm_num)]
  have : (2 : ℝ) ≤ n := by exact_mod_cast large
  push_cast
  linarith

theorem integrable_term {c : ℝ × ℝ → ℂ} (hc : Continuous c) {B : ℝ}
    (hB : ∀ u, ‖c u‖ ≤ B) (Q : HomogeneousPoly n) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (large : 2 ≤ n) :
    Integrable fun u => transferScale n u * c u *
      functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ Q) := by
  obtain ⟨M, hM⟩ := exists_bound_functional_coefficient Q functional
  refine integrable_of_continuous_decay ((continuous_transferScale.mul hc).mul
    (continuous_functional_coefficient Q functional)) (decay_exponent large)
    (C := B * M) fun u => ?_
  rw [norm_mul, norm_mul, norm_transferScale]
  have hpow := Real.rpow_nonneg (one_add_sq_pos u).le (-(((n + 3 : ℕ) : ℝ) / 4))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB u)
  calc _ ≤ (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n + 3 : ℕ) : ℝ) / 4)) * B * M := by
        gcongr
        · exact hB u
        · exact hM u
    _ = _ := by ring

/-- **Every test of the mixed derivative vector is integrable.** -/
theorem integrable_functional_edgeMixedVector {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F) (large : 2 ≤ n) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable fun u => functional (edgeMixedVector n F u i h) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_at_I hF
  have holBound : ∀ u, ‖2⁻¹ * F (movedPoint u h) Complex.I * ((n : ℂ) + 1) * holCoeff u i‖ ≤
      2⁻¹ * C * ((n : ℝ) + 1) * 54 := by
    intro u
    rw [norm_mul, norm_mul, norm_mul]
    have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
    rw [hn, norm_inv, Complex.norm_ofNat]
    gcongr
    · exact hC _
    · exact norm_holCoeff_le u i
  have antiBound : ∀ u, ‖2⁻¹ * F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I *
      ((n : ℂ) + 1) * antiCoeff u i‖ ≤ 2⁻¹ * C * ((n : ℝ) + 1) * 54 := by
    intro u
    rw [norm_mul, norm_mul, norm_mul]
    have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
    rw [hn, norm_inv, Complex.norm_ofNat]
    gcongr
    · exact hC _
    · exact norm_antiCoeff_le u i
  have hol := integrable_term (((continuous_const.mul (continuous_movedValue hF h)).mul
    continuous_const).mul (continuous_holCoeff i)) holBound (ternaryLinPow n 1 (-Complex.I))
    functional large
  have anti := integrable_term (((continuous_const.mul (continuous_movedValue_J hF h)).mul
    continuous_const).mul (continuous_antiCoeff i)) antiBound
    (ternaryLinPow n (-1) (-Complex.I)) functional large
  refine (hol.add anti).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [edgeMixedVector_eq_smul, map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.mul_apply]

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
