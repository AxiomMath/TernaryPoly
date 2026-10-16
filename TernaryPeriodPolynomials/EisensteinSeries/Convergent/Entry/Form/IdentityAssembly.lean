module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityCovariance
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityBaseCase
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.FrameOrthogonal

@[expose] public section


/-!
# The pointwise form identity (assembly)

`form_identity_coeff_of_R3`: for `n ≥ 3`, `h` holomorphic on the upper half-plane with the cusp decay
`‖h z‖² (Im z)^{n+3} ≤ M`, every invertible `g` with `0 < det g`, all directions `V, W` and every polynomial
coefficient `m`:
the function `(s,t) ↦ coeff_m ω̃_h(L_{s,t} g)(V,W)` is integrable over `ℝ²` and
`∫_{ℝ²} coeff_m ω̃_h(L_{s,t} g)(V,W) = c_∞ · coeff_m σ̃_h(g)(V,W)`, `c_∞ = -2πi/(n+1)`
(σ̃ = the frame coefficient of the line seed), **given the covariance of the line seed under the line parabolic**
(`R3`, a hypothesis here; in `LineSeedCovariance`).
Proof: Iwasawa `g = q k` (`exists_lineParabolic_mul_orthogonal`), the covariance of the integrated seed
(`intFrameCoeff_lineParabolic`, R1 + R2), that of the line seed (R3), the orthogonal twist
(`frameCoefficient_orthogonal`, `lineFrameCoefficient_orthogonal`, with `coeff_rho_eq_sum` expressing the
coefficients of `ρ(kᵀ) P` as a fixed finite combination of the coefficients of `P`) and the base point
(`base_form_identity_coeff`) for `h' = slashTwisted (n+3) C h`, whose holomorphy and decay are
`slashTwisted_differentiableOn`, `slashTwisted_decay`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex MeasureTheory MvPolynomial TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

theorem mobius_im_pos (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : 0 < C.det) (z : ℂ) (hz : 0 < z.im) :
    0 < (((C 0 0 : ℂ) * z + C 0 1) / ((C 1 0 : ℂ) * z + C 1 1)).im := by
  have hne := mobius_denom_ne C hC z hz
  rw [mobius_im, ← Matrix.det_fin_two]
  have hn : 0 < Complex.normSq ((C 1 0 : ℂ) * z + C 1 1) := Complex.normSq_pos.mpr hne
  positivity

theorem slashTwisted_differentiableOn (k : ℕ) (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : 0 < C.det) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ (slashTwisted k C h) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hne := mobius_denom_ne C hC z hz
  have hM : DifferentiableAt ℂ (fun w : ℂ => ((C 0 0 : ℂ) * w + C 0 1) / ((C 1 0 : ℂ) * w + C 1 1)) z :=
    ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)).div
      ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)) hne
  have hhm : DifferentiableAt ℂ h (((C 0 0 : ℂ) * z + C 0 1) / ((C 1 0 : ℂ) * z + C 1 1)) :=
    (hh _ (mobius_im_pos C hC z hz)).differentiableAt
      (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds (mobius_im_pos C hC z hz))
  unfold slashTwisted
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.mul ?_ (hhm.comp z hM)
  exact (differentiableAt_const _).mul
    (((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)).zpow (Or.inl hne))


theorem slashTwisted_decay (k : ℕ) (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : 0 < C.det) (h : ℂ → ℂ) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ k ≤ M) (z : ℂ) (hz : 0 < z.im) :
    ‖slashTwisted k C h z‖ ^ 2 * z.im ^ k ≤ C.det ^ k * M := by
  have hne := mobius_denom_ne C hC z hz
  have hN : 0 < Complex.normSq ((C 1 0 : ℂ) * z + C 1 1) := Complex.normSq_pos.mpr hne
  set N := Complex.normSq ((C 1 0 : ℂ) * z + C 1 1) with hNdef
  set w := ((C 0 0 : ℂ) * z + C 0 1) / ((C 1 0 : ℂ) * z + C 1 1) with hw
  have hwim : w.im = C.det * z.im / N := by
    rw [hw, mobius_im, ← Matrix.det_fin_two]
  have hwpos : 0 < w.im := mobius_im_pos C hC z hz
  have hzim : z.im = w.im * N / C.det := by
    rw [hwim]; field_simp
  have hnorm : ‖slashTwisted k C h z‖ ^ 2 = (C.det ^ k) ^ 2 * (N ^ k)⁻¹ * ‖h w‖ ^ 2 := by
    unfold slashTwisted
    rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_pow, norm_zpow, ← hw]
    have hDn : ‖(C 1 0 : ℂ) * z + C 1 1‖ ^ 2 = N := by rw [hNdef, Complex.sq_norm]
    have hdetn : ‖(C.det : ℂ)‖ = C.det := by
      rw [Complex.norm_real, Real.norm_of_nonneg hC.le]
    rw [hdetn, zpow_neg, zpow_natCast, inv_pow]
    have e1 : (‖(C 1 0 : ℂ) * z + C 1 1‖ ^ k) ^ 2 = N ^ k := by
      rw [show (‖(C 1 0 : ℂ) * z + C 1 1‖ ^ k) ^ 2 = (‖(C 1 0 : ℂ) * z + C 1 1‖ ^ 2) ^ k by ring, hDn]
    rw [e1]
  rw [hnorm, hzim]
  calc (C.det ^ k) ^ 2 * (N ^ k)⁻¹ * ‖h w‖ ^ 2 * (w.im * N / C.det) ^ k
      = C.det ^ k * (‖h w‖ ^ 2 * w.im ^ k) := by
        rw [div_pow, mul_pow]
        field_simp
    _ ≤ C.det ^ k * M := by gcongr; exact hM w hwpos


theorem rho_C_mul (g : Matrix (Fin 3) (Fin 3) ℝ) (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (C c * q) = C c * SeedC3.rho g q := by
  unfold SeedC3.rho
  rw [map_mul, bind₁_C_right]
  ring

/-- The set of monomials of degree `n` in three variables. -/
def degSet (n : ℕ) : Finset (Fin 3 →₀ ℕ) := Finset.finsuppAntidiag Finset.univ n

theorem mem_degSet {n : ℕ} {m : Fin 3 →₀ ℕ} : m ∈ degSet n ↔ m.sum (fun _ k => k) = n := by
  unfold degSet
  have e : m.sum (fun _ k => k) = ∑ i, m i := by rw [sum_eq_of_multinomial, Fin.sum_univ_three]
  rw [Finset.mem_finsuppAntidiag, e]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.subset_univ _⟩⟩

/-- The coefficients of `ρ(g) Q` are finite combinations of the coefficients of `Q` (for `Q` of degree `n`). -/
theorem coeff_rho_eq_sum (g : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : ∀ m' : Fin 3 →₀ ℕ, m'.sum (fun _ k => k) ≠ n → Q.coeff m' = 0)
    (m : Fin 3 →₀ ℕ) :
    (SeedC3.rho g Q).coeff m =
      ∑ m' ∈ degSet n, Q.coeff m' *
        (SeedC3.rho g (MvPolynomial.monomial m' 1)).coeff m := by
  have hQsum : Q = ∑ m' ∈ degSet n, MvPolynomial.monomial m' (Q.coeff m') := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    refine Finset.sum_subset ?_ ?_
    · intro m' hm'
      rw [mem_degSet]
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hm') (hQ m' hne)
    · intro m' _ hm'
      rw [MvPolynomial.notMem_support_iff.mp hm']
      simp
  conv_lhs => rw [hQsum]
  rw [rho_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl (fun m' _ => ?_)
  rw [show MvPolynomial.monomial m' (Q.coeff m') =
    C (Q.coeff m') * MvPolynomial.monomial m' (1 : ℂ) by
      rw [MvPolynomial.C_mul_monomial, mul_one], rho_C_mul, MvPolynomial.coeff_C_mul]


theorem coeff_frameCoefficient_entryFrame_eq_zero (n : ℕ) (h : ℂ → ℂ) (s t : ℝ)
    (V W : Matrix (Fin 3) (Fin 3) ℝ) (m' : Fin 3 →₀ ℕ) (hm' : m'.sum (fun _ k => k) ≠ n) :
    (frameCoefficient (seedForm n h) (entryFrame s t) V W).coeff m' = 0 := by
  rw [seed_frameCoefficient_entryFrame_sym, MvPolynomial.coeff_C_mul, coeff_linForm_pow, ite_eq_right hm',
    mul_zero]

theorem coeff_lineFrameCoefficient_one_eq_zero (n : ℕ) (h : ℂ → ℂ) (V W : Matrix (Fin 3) (Fin 3) ℝ)
    (m' : Fin 3 →₀ ℕ) (hm' : m'.sum (fun _ k => k) ≠ n) :
    (lineFrameCoefficient (lineSeedForm n h) 1 V W).coeff m' = 0 := by
  have hform : (C Complex.I * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) =
      C 0 * X 0 + C (-1) * X 1 + C Complex.I * X 2 := by
    simp; ring
  rw [lineFrameCoefficient_one, MvPolynomial.coeff_C_mul, hform, coeff_linForm_pow, ite_eq_right hm', mul_zero]


/-- **The pointwise form identity, one coefficient, given the line-seed covariance R3.** -/
theorem form_identity_coeff_of_R3 (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (R3 : ∀ (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ), 0 < a → 0 < C.det →
      ∀ g V W : Matrix (Fin 3) (Fin 3) ℝ, g.det ≠ 0 →
        lineFrameCoefficient (lineSeedForm n h) (lineParabolic a b C * g) V W =
          MvPolynomial.C (((a ^ 2 / C.det : ℝ)) : ℂ) *
            lineFrameCoefficient (lineSeedForm n (slashTwisted (n + 3) C h)) g V W)
    (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : 0 < g.det) (V W : Matrix (Fin 3) (Fin 3) ℝ)
    (m : Fin 3 →₀ ℕ) :
    Integrable (fun st : ℝ × ℝ =>
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) V W).coeff m) ∧
    intFrameCoeff n h g V W m =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        (lineFrameCoefficient (lineSeedForm n h) g V W).coeff m := by
  obtain ⟨a, b, C, k, ha, hC, hk, hgk⟩ := exists_lineParabolic_mul_orthogonal g hg
  have hkdet : k.det ≠ 0 := by
    have h1 : k.det * k.det = 1 := by
      have := congrArg Matrix.det hk
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    intro h0; rw [h0] at h1; simp at h1
  subst hgk
  set h' := slashTwisted (n + 3) C h with hh'def
  have hh' : DifferentiableOn ℂ h' {z : ℂ | 0 < z.im} := slashTwisted_differentiableOn (n + 3) C hC h hh
  have hM' : ∀ z : ℂ, 0 < z.im → ‖h' z‖ ^ 2 * z.im ^ (n + 3) ≤ C.det ^ (n + 3) * M :=
    fun z hz => slashTwisted_decay (n + 3) C hC h M hM z hz
  set V' := k * V * k.transpose with hV'
  set W' := k * W * k.transpose with hW'
  set r : (Fin 3 →₀ ℕ) → ℂ := fun m' =>
    (SeedC3.rho k.transpose (MvPolynomial.monomial m' 1)).coeff m with hr
  -- pointwise expansion of the integrand for `h'` at `g = k`
  have hpt : ∀ st : ℝ × ℝ, (frameCoefficient (seedForm n h') (entryFrame st.1 st.2 * k) V W).coeff m =
      ∑ m' ∈ degSet n, (frameCoefficient (seedForm n h') (entryFrame st.1 st.2) V' W').coeff m' * r m' := by
    intro st
    rw [frameCoefficient_orthogonal _ _ k V W hk]
    refine coeff_rho_eq_sum k.transpose n _ (fun m' hm' =>
      coeff_frameCoefficient_entryFrame_eq_zero n h' st.1 st.2 V' W' m' hm') m
  have hbase : ∀ m' ∈ degSet n,
      Integrable (fun st : ℝ × ℝ => (frameCoefficient (seedForm n h') (entryFrame st.1 st.2) V' W').coeff m') ∧
      ∫ st : ℝ × ℝ, (frameCoefficient (seedForm n h') (entryFrame st.1 st.2) V' W').coeff m' =
        (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
          (lineFrameCoefficient (lineSeedForm n h') 1 V' W').coeff m' :=
    fun m' hm' => base_form_identity_coeff n hn h' hh' _ hM' m' (mem_degSet.mp hm') V' W'
  have hintk : Integrable (fun st : ℝ × ℝ => (frameCoefficient (seedForm n h') (entryFrame st.1 st.2 * k) V W).coeff m) := by
    simp_rw [hpt]
    exact integrable_finsetSum _ (fun m' hm' => (hbase m' hm').1.mul_const _)
  refine ⟨integrable_lineParabolic n h a b C ha hC k V W hkdet m hintk, ?_⟩
  rw [intFrameCoeff_lineParabolic n h a b C ha hC k V W hkdet m, R3 a b C ha hC k V W hkdet,
    MvPolynomial.coeff_C_mul]
  have hk1 : lineFrameCoefficient (lineSeedForm n h') k V W =
      SeedC3.rho k.transpose (lineFrameCoefficient (lineSeedForm n h') 1 V' W') := by
    have := lineFrameCoefficient_orthogonal (lineSeedForm n h') 1 k V W hk
    rwa [Matrix.one_mul] at this
  rw [hk1, coeff_rho_eq_sum k.transpose n _ (fun m' hm' =>
    coeff_lineFrameCoefficient_one_eq_zero n h' V' W' m' hm') m]
  unfold intFrameCoeff
  rw [← hh'def]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun m' hm' => (hbase m' hm').1.mul_const _)]
  simp_rw [integral_mul_const]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m' hm' => ?_)
  rw [(hbase m' hm').2]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
