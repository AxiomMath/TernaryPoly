module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityTangent
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Iwasawa
public import TernaryPeriodPolynomials.BoundaryComparison.StokesComparison

@[expose] public section


/-!
# R1: Levi covariance of the seed's frame coefficient

For `A` with `det A > 0`, `t > 0` and invertible `g`,
`ω̃_h(diag(A,t) g)(V,W) = ω̃_{h'}(g)(V,W)` with `h' = slashTwisted (n+3) A h`
(`frameCoefficient_planeLevi`).  Steps: the chart equivariance
`gramChart (m G mᵀ) = leviMap A t (gramChart G)` for `m = planeLevi A t` (`gramChart_planeLevi`, using the Möbius
covariance `mobius_tauOfSchur` of the upper-half-plane root of a binary form and its uniqueness
`eq_tauOfSchur_of_root`), the chain rule for the chart tangents `chartTangent_planeLevi`, the expansion of a
pulled-back form through the Jacobian (`frameValue_expand`), the `seed_closed_equivariant (iii)`
(`formPullback (leviMap A t) (seedForm n h) = leviCoefficientAction A t ∘ seedForm n h'`) and
`leviCoefficientAction A t = ρ(diag(A,t))` (`leviCoefficientAction_eq_rho`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex MvPolynomial TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

theorem planeLevi_det (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : (planeLevi A t).det = A.det * t := by
  simp [planeLevi, Matrix.det_fin_three, Matrix.det_fin_two]; ring

/-- The inverse of the plane Levi element. -/
theorem planeLevi_inv (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hA : A.det ≠ 0) (ht : t ≠ 0) :
    (planeLevi A t)⁻¹ = !![A 1 1 / A.det, -A 0 1 / A.det, 0; -A 1 0 / A.det, A 0 0 / A.det, 0; 0, 0, t⁻¹] := by
  have hd : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> linarith [hd]


/-- The coefficient action of the Levi element is `ρ(diag(A, t))`. -/
theorem leviCoefficientAction_eq_rho (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hA : A.det ≠ 0) (ht : t ≠ 0)
    (q : MvPolynomial (Fin 3) ℂ) : leviCoefficientAction A t q = SeedC3.rho (planeLevi A t) q := by
  unfold leviCoefficientAction SeedC3.rho
  rw [planeLevi_det, planeLevi_inv A t hA ht]
  congr 2
  congr 1
  funext i
  fin_cases i <;> simp [Fin.sum_univ_three]


/-- The upper-half-plane root `(s₀₁ + i √det)/s₁₁` of the binary form with Gram entries `s₀₀, s₀₁, s₁₁`. -/
def tauOfSchur (s00 s01 s11 : ℝ) : ℂ := ((s01 : ℂ) + Complex.I * (Real.sqrt (s00 * s11 - s01 ^ 2) : ℂ)) / s11

/-- Uniqueness of the root in the upper half-plane. -/
theorem eq_tauOfSchur_of_root (s00 s01 s11 : ℝ) (hs : 0 < s11) (hd : 0 < s00 * s11 - s01 ^ 2) (x : ℂ)
    (hx : 0 < x.im) (hroot : (s00 : ℂ) - 2 * s01 * x + s11 * x ^ 2 = 0) :
    x = tauOfSchur s00 s01 s11 := by
  have hq : 0 < Real.sqrt (s00 * s11 - s01 ^ 2) := Real.sqrt_pos.mpr hd
  have hq2 : Real.sqrt (s00 * s11 - s01 ^ 2) ^ 2 = s00 * s11 - s01 ^ 2 := Real.sq_sqrt hd.le
  set q := Real.sqrt (s00 * s11 - s01 ^ 2) with hqdef
  have hsC : (s11 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hprod : (x - ((s01 : ℂ) + Complex.I * q) / s11) * (x - ((s01 : ℂ) - Complex.I * q) / s11) = 0 := by
    have hq2C : (q : ℂ) ^ 2 = s00 * s11 - (s01 : ℂ) ^ 2 := by exact_mod_cast hq2
    field_simp
    linear_combination (s11 : ℂ) * hroot + (-(q : ℂ) ^ 2) * Complex.I_sq + hq2C
  rcases mul_eq_zero.mp hprod with h1 | h1
  · unfold tauOfSchur
    have := sub_eq_zero.mp h1
    rw [this]
  · exfalso
    have h2 : x = ((s01 : ℂ) - Complex.I * q) / s11 := sub_eq_zero.mp h1
    have him : x.im = -(q / s11) := by
      rw [h2, Complex.div_ofReal_im]
      simp
      ring
    rw [him] at hx
    have : 0 < q / s11 := div_pos hq hs
    linarith


theorem tauOfSchur_root (s00 s01 s11 : ℝ) (hs : 0 < s11) (hd : 0 < s00 * s11 - s01 ^ 2) :
    (s00 : ℂ) - 2 * s01 * tauOfSchur s00 s01 s11 + s11 * tauOfSchur s00 s01 s11 ^ 2 = 0 := by
  have hq2 : Real.sqrt (s00 * s11 - s01 ^ 2) ^ 2 = s00 * s11 - s01 ^ 2 := Real.sq_sqrt hd.le
  set q := Real.sqrt (s00 * s11 - s01 ^ 2) with hqdef
  have hq2C : (q : ℂ) ^ 2 = s00 * s11 - (s01 : ℂ) ^ 2 := by exact_mod_cast hq2
  have hsC : (s11 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold tauOfSchur
  rw [← hqdef]
  field_simp
  linear_combination ((q : ℂ) ^ 2) * Complex.I_sq - hq2C

theorem tauOfSchur_im (s00 s01 s11 : ℝ) :
    (tauOfSchur s00 s01 s11).im = Real.sqrt (s00 * s11 - s01 ^ 2) / s11 := by
  unfold tauOfSchur
  rw [Complex.div_ofReal_im]
  simp


theorem mobius_im (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im =
      (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp
  ring

/-- **Möbius covariance of the root**: if `S' = A S Aᵀ` (`det A > 0`), the upper-half-plane root of `S'` is the
Möbius image of that of `S`. -/
theorem mobius_tauOfSchur (s00 s01 s11 a b c d : ℝ) (hs : 0 < s11) (hd : 0 < s00 * s11 - s01 ^ 2)
    (hA : 0 < a * d - b * c) :
    tauOfSchur (a ^ 2 * s00 + 2 * a * b * s01 + b ^ 2 * s11)
        (a * c * s00 + (a * d + b * c) * s01 + b * d * s11) (c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11) =
      ((a : ℂ) * tauOfSchur s00 s01 s11 + b) / ((c : ℂ) * tauOfSchur s00 s01 s11 + d) := by
  set τ := tauOfSchur s00 s01 s11 with hτ
  have hτim : τ.im = Real.sqrt (s00 * s11 - s01 ^ 2) / s11 := tauOfSchur_im _ _ _
  have hq : 0 < Real.sqrt (s00 * s11 - s01 ^ 2) := Real.sqrt_pos.mpr hd
  have hτpos : 0 < τ.im := by rw [hτim]; exact div_pos hq hs
  have hroot := tauOfSchur_root s00 s01 s11 hs hd
  rw [← hτ] at hroot
  have hDne : (c : ℂ) * τ + d ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.im h0
    have h2 := congrArg Complex.re h0
    simp at h1 h2
    rcases h1 with h1 | h1
    · rw [h1] at h2
      simp at h2
      rw [h1, h2] at hA
      simp at hA
    · linarith
  have hnorm : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hDne
  have hs' : 0 < c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11 := by
    have h1 : (c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11) * s11 =
        (c * s01 + d * s11) ^ 2 + c ^ 2 * (s00 * s11 - s01 ^ 2) := by ring
    have h2 : 0 < (c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11) * s11 := by
      rw [h1]
      by_cases hc : c = 0
      · have hd0 : d ≠ 0 := by
          rintro rfl; rw [hc] at hA; simp at hA
        rw [hc]; simp; positivity
      · have : 0 < c ^ 2 * (s00 * s11 - s01 ^ 2) := by positivity
        nlinarith [sq_nonneg (c * s01 + d * s11)]
    exact pos_of_mul_pos_left h2 hs.le |> fun h => by nlinarith
  have hd' : 0 < (a ^ 2 * s00 + 2 * a * b * s01 + b ^ 2 * s11) *
      (c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11) -
      (a * c * s00 + (a * d + b * c) * s01 + b * d * s11) ^ 2 := by
    have : (a ^ 2 * s00 + 2 * a * b * s01 + b ^ 2 * s11) *
      (c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11) -
      (a * c * s00 + (a * d + b * c) * s01 + b * d * s11) ^ 2 = (a * d - b * c) ^ 2 * (s00 * s11 - s01 ^ 2) := by ring
    rw [this]; positivity
  refine (eq_tauOfSchur_of_root _ _ _ hs' hd' _ ?_ ?_).symm
  · rw [mobius_im]
    positivity
  · have key : ((a ^ 2 * s00 + 2 * a * b * s01 + b ^ 2 * s11 : ℝ) : ℂ) * ((c : ℂ) * τ + d) ^ 2 -
        2 * ((a * c * s00 + (a * d + b * c) * s01 + b * d * s11 : ℝ) : ℂ) *
          ((a : ℂ) * τ + b) * ((c : ℂ) * τ + d) +
        ((c ^ 2 * s00 + 2 * c * d * s01 + d ^ 2 * s11 : ℝ) : ℂ) * ((a : ℂ) * τ + b) ^ 2 =
        (((a : ℂ) * d - b * c) ^ 2) * ((s00 : ℂ) - 2 * s01 * τ + s11 * τ ^ 2) := by
      push_cast; ring
    rw [hroot, mul_zero] at key
    generalize (c : ℂ) * τ + d = D at hDne key ⊢
    generalize (a : ℂ) * τ + b = N at key ⊢
    push_cast at key ⊢
    field_simp
    linear_combination key


theorem planeLevi_conj (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : G.IsSymm) :
    planeLevi A t * G * (planeLevi A t).transpose =
      !![A 0 0 ^ 2 * G 0 0 + 2 * A 0 0 * A 0 1 * G 0 1 + A 0 1 ^ 2 * G 1 1,
          A 0 0 * A 1 0 * G 0 0 + (A 0 0 * A 1 1 + A 0 1 * A 1 0) * G 0 1 + A 0 1 * A 1 1 * G 1 1,
          t * (A 0 0 * G 0 2 + A 0 1 * G 1 2);
        A 0 0 * A 1 0 * G 0 0 + (A 0 0 * A 1 1 + A 0 1 * A 1 0) * G 0 1 + A 0 1 * A 1 1 * G 1 1,
          A 1 0 ^ 2 * G 0 0 + 2 * A 1 0 * A 1 1 * G 0 1 + A 1 1 ^ 2 * G 1 1,
          t * (A 1 0 * G 0 2 + A 1 1 * G 1 2);
        t * (A 0 0 * G 0 2 + A 0 1 * G 1 2), t * (A 1 0 * G 0 2 + A 1 1 * G 1 2), t ^ 2 * G 2 2] := by
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have h20 : G 2 0 = G 0 2 := hG.apply 0 2
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul,
      dotProduct, h10, h20, h21]
  all_goals ring


theorem gramPlaneTau_eq_tauOfSchur (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) :
    gramPlaneTau G = tauOfSchur (gramSchur G 0 0) (gramSchur G 0 1) (gramSchur G 1 1) := by
  unfold gramPlaneTau tauOfSchur
  rw [gramSchur_det G hG]
  have hs : (gramSchur G 1 1 : ℂ) = (gramSchur G 1 1 : ℂ) := rfl
  push_cast
  by_cases h0 : (gramSchur G 1 1 : ℂ) = 0
  · simp [h0]
  · field_simp

/-- **Chart equivariance for the plane Levi elements**: `gramChart (m G mᵀ) = leviMap A t (gramChart G)`. -/
theorem gramChart_planeLevi (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hA : 0 < A.det) (ht : 0 < t)
    (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k.det ≠ 0) :
    gramChart (planeLevi A t * (k * k.transpose) * (planeLevi A t).transpose) =
      leviMap A t (gramChart (k * k.transpose)) := by
  set G := k * k.transpose with hGdef
  have hGs : G.IsSymm := gram_isSymm k
  have hR := gram_pos_22 k hk
  have hS11 := gramSchur_pos_11 k hk
  have hSd := gramSchur_det_pos k hk
  rw [← hGdef] at hR hS11 hSd
  have hX := planeLevi_conj A t G hGs
  set X := planeLevi A t * G * (planeLevi A t).transpose with hXdef
  have hXs : X.IsSymm := by
    rw [hXdef]; unfold Matrix.IsSymm
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hGs.eq]
  have hR0 : G 2 2 ≠ 0 := hR.ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hX22 : X 2 2 = t ^ 2 * G 2 2 := by rw [hX]; simp
  have hX02 : X 0 2 = t * (A 0 0 * G 0 2 + A 0 1 * G 1 2) := by rw [hX]; simp
  have hX12 : X 1 2 = t * (A 1 0 * G 0 2 + A 1 1 * G 1 2) := by rw [hX]; simp
  have hX00 : X 0 0 = A 0 0 ^ 2 * G 0 0 + 2 * A 0 0 * A 0 1 * G 0 1 + A 0 1 ^ 2 * G 1 1 := by
    rw [hX]; simp
  have hX01 : X 0 1 = A 0 0 * A 1 0 * G 0 0 + (A 0 0 * A 1 1 + A 0 1 * A 1 0) * G 0 1 +
      A 0 1 * A 1 1 * G 1 1 := by rw [hX]; simp
  have hX11 : X 1 1 = A 1 0 ^ 2 * G 0 0 + 2 * A 1 0 * A 1 1 * G 0 1 + A 1 1 ^ 2 * G 1 1 := by
    rw [hX]; simp
  have hS00 : gramSchur X 0 0 = A 0 0 ^ 2 * gramSchur G 0 0 + 2 * A 0 0 * A 0 1 * gramSchur G 0 1 +
      A 0 1 ^ 2 * gramSchur G 1 1 := by
    rw [gramSchur_apply, gramSchur_apply, gramSchur_apply, gramSchur_apply]
    simp only [Fin.castSucc_zero, Fin.castSucc_one]
    rw [hX00, hX02, hX22]; field_simp; ring
  have hS01 : gramSchur X 0 1 = A 0 0 * A 1 0 * gramSchur G 0 0 +
      (A 0 0 * A 1 1 + A 0 1 * A 1 0) * gramSchur G 0 1 + A 0 1 * A 1 1 * gramSchur G 1 1 := by
    rw [gramSchur_apply, gramSchur_apply, gramSchur_apply, gramSchur_apply]
    simp only [Fin.castSucc_zero, Fin.castSucc_one]
    rw [hX01, hX02, hX12, hX22]; field_simp; ring
  have hSX11 : gramSchur X 1 1 = A 1 0 ^ 2 * gramSchur G 0 0 + 2 * A 1 0 * A 1 1 * gramSchur G 0 1 +
      A 1 1 ^ 2 * gramSchur G 1 1 := by
    rw [gramSchur_apply, gramSchur_apply, gramSchur_apply, gramSchur_apply]
    simp only [Fin.castSucc_zero, Fin.castSucc_one]
    rw [hX11, hX12, hX22]; field_simp; ring
  have hAdet : 0 < A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    rw [← Matrix.det_fin_two]; exact hA
  have hSd' : 0 < gramSchur G 0 0 * gramSchur G 1 1 - gramSchur G 0 1 ^ 2 := by
    rw [← gramSchur_det G hGs]; exact hSd
  have hτ : gramPlaneTau X = ((A 0 0 : ℂ) * gramPlaneTau G + A 0 1) / ((A 1 0 : ℂ) * gramPlaneTau G + A 1 1) := by
    rw [gramPlaneTau_eq_tauOfSchur X hXs, hS00, hS01, hSX11,
      mobius_tauOfSchur _ _ _ _ _ _ _ hS11 hSd' hAdet, ← gramPlaneTau_eq_tauOfSchur G hGs]
  have c0 : (gramPlaneU X).1 = (A 0 0 * (gramPlaneU G).1 + A 0 1 * (gramPlaneU G).2) / t := by
    simp only [gramPlaneU]
    rw [hX02, hX22]
    field_simp
  have c1 : (gramPlaneU X).2 = (A 1 0 * (gramPlaneU G).1 + A 1 1 * (gramPlaneU G).2) / t := by
    simp only [gramPlaneU]
    rw [hX12, hX22]
    field_simp
  have c2 : (gramPlaneTau X).re = (((A 0 0 : ℂ) * seedTau (gramChart G) + A 0 1) /
      ((A 1 0 : ℂ) * seedTau (gramChart G) + A 1 1)).re := by
    rw [seedTau_gramChart_eq, hτ]
  have c3 : (gramPlaneTau X).im = (((A 0 0 : ℂ) * seedTau (gramChart G) + A 0 1) /
      ((A 1 0 : ℂ) * seedTau (gramChart G) + A 1 1)).im := by
    rw [seedTau_gramChart_eq, hτ]
  have c4 : Real.sqrt (gramNormal X) = t * Real.sqrt (gramNormal G) := by
    unfold gramNormal
    rw [hX22, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  funext i
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4


theorem hasDerivAt_gramChart_curve (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) (a : Fin 5) :
    HasDerivAt (fun ε => gramChart (gramCurve g V ε) a)
      (planeTangent (g * g.transpose) (g * (V + V.transpose) * g.transpose) a) 0 := by
  have hG := hasDerivAt_gramCurve g V
  have h0 := gramCurve_zero g V
  have hR : 0 < (gramCurve g V 0) 2 2 := by rw [h0]; exact gram_pos_22 g hg
  have h11 : 0 < gramSchur (gramCurve g V 0) 1 1 := by rw [h0]; exact gramSchur_pos_11 g hg
  have hdet : 0 < (gramSchur (gramCurve g V 0)).det := by rw [h0]; exact gramSchur_det_pos g hg
  have hτ := hasDerivAt_gramPlaneTau (gramCurve g V) _ (gramCurve_isSymm g V) hG hR h11 hdet
  have hu := hasDerivAt_gramPlaneU (gramCurve g V) _ hG hR.ne'
  have hs := ((hG 2 2).sqrt hR.ne')
  rw [h0] at hτ hu hs
  unfold planeTangent
  fin_cases a
  · exact hu 0
  · exact hu 1
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hτ
  · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hτ
  · exact hs


theorem mobius_denom_ne (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) (z : ℂ) (hz : 0 < z.im) :
    (A 1 0 : ℂ) * z + A 1 1 ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  have h2 := congrArg Complex.re h0
  simp at h1 h2
  have hd : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  rcases h1 with h1 | h1
  · rw [h1] at h2 hd
    simp at h2
    rw [h2] at hd
    rw [hd] at hA
    simp at hA
  · linarith

theorem leviMap_differentiableAt (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hA : 0 < A.det) (p : Fin 5 → ℝ)
    (hp : 0 < p 3) : DifferentiableAt ℝ (leviMap A t) p := by
  have hz : DifferentiableAt ℝ (fun q : Fin 5 → ℝ => seedTau q) p := by
    unfold seedTau; fun_prop
  have hne := mobius_denom_ne A hA (seedTau p) (by simpa [seedTau] using hp)
  have hM : DifferentiableAt ℂ (fun w : ℂ => ((A 0 0 : ℂ) * w + A 0 1) / ((A 1 0 : ℂ) * w + A 1 1)) (seedTau p) :=
    ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)).div
      ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)) hne
  have hMz : DifferentiableAt ℝ (fun q : Fin 5 → ℝ =>
      ((A 0 0 : ℂ) * seedTau q + A 0 1) / ((A 1 0 : ℂ) * seedTau q + A 1 1)) p :=
    (hM.restrictScalars ℝ).comp p hz
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · exact (by fun_prop : DifferentiableAt ℝ (fun q : Fin 5 → ℝ => (A 0 0 * q 0 + A 0 1 * q 1) / t) p)
  · exact (by fun_prop : DifferentiableAt ℝ (fun q : Fin 5 → ℝ => (A 1 0 * q 0 + A 1 1 * q 1) / t) p)
  · exact (Complex.reCLM.differentiableAt.comp p hMz)
  · exact (Complex.imCLM.differentiableAt.comp p hMz)
  · exact (by fun_prop : DifferentiableAt ℝ (fun q : Fin 5 → ℝ => t * q 4) p)


theorem gramPlaneTau_im_pos (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    0 < (gramPlaneTau (g * g.transpose)).im := by
  rw [gramPlaneTau_eq_tauOfSchur _ (gram_isSymm g), tauOfSchur_im]
  have hs := gramSchur_pos_11 g hg
  have hd := gramSchur_det_pos g hg
  rw [gramSchur_det _ (gram_isSymm g)] at hd
  exact div_pos (Real.sqrt_pos.mpr hd) hs

theorem gramCurve_planeLevi (m g V : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) :
    gramCurve (m * g) V ε = m * gramCurve g V ε * m.transpose := by
  unfold gramCurve
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem gramCurve_eq_gram (g V : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) :
    gramCurve g V ε = (g * (1 + ε • V)) * (g * (1 + ε • V)).transpose := by
  unfold gramCurve
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **The chart tangent transforms by the derivative of the Levi map.** -/
theorem chartTangent_planeLevi (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hA : 0 < A.det) (ht : 0 < t)
    (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    chartTangent (planeLevi A t * g) V =
      fderiv ℝ (leviMap A t) (gramChart (g * g.transpose)) (chartTangent g V) := by
  have hγ : HasDerivAt (fun ε => gramChart (gramCurve g V ε)) (chartTangent g V) 0 := by
    rw [chartTangent_eq g V hg]
    exact hasDerivAt_pi.mpr (hasDerivAt_gramChart_curve g V hg)
  have hp0 : 0 < (gramChart (g * g.transpose)) 3 := by
    show 0 < (gramPlaneTau (g * g.transpose)).im
    exact gramPlaneTau_im_pos g hg
  have h0 : gramCurve g V 0 = g * g.transpose := gramCurve_zero g V
  have hF : HasFDerivAt (leviMap A t) (fderiv ℝ (leviMap A t) (gramChart (gramCurve g V 0)))
      (gramChart (gramCurve g V 0)) := by
    rw [h0]
    exact (leviMap_differentiableAt A t hA (gramChart (g * g.transpose)) hp0).hasFDerivAt
  have hlev := hF.comp_hasDerivAt (0 : ℝ) hγ
  rw [h0] at hlev
  -- eventual equality with the curve of `m * g`
  have hdetcont : ContinuousAt (fun ε : ℝ => (g * (1 + ε • V)).det) 0 := by
    have : Continuous (fun ε : ℝ => (g * (1 + ε • V)).det) :=
      (continuous_const.matrix_mul (continuous_const.add (continuous_id.smul continuous_const))).matrix_det
    exact this.continuousAt
  have hne : ∀ᶠ ε in nhds (0 : ℝ), (g * (1 + ε • V)).det ≠ 0 := by
    apply hdetcont.eventually_ne
    simpa using hg
  have heq : (fun ε => leviMap A t (gramChart (gramCurve g V ε))) =ᶠ[nhds (0 : ℝ)]
      (fun ε => gramChart (gramCurve (planeLevi A t * g) V ε)) := by
    filter_upwards [hne] with ε hε
    rw [gramCurve_planeLevi, gramCurve_eq_gram, ← gramChart_planeLevi A t hA ht _ hε]
  have hfinal := hlev.congr_of_eventuallyEq heq.symm
  funext a
  exact (hasDerivAt_pi.mp hfinal a).deriv


theorem rho_sum_C_mul {ι : Type*} (g : Matrix (Fin 3) (Fin 3) ℝ) (s : Finset ι) (r : ι → ℂ)
    (q : ι → MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (∑ i ∈ s, C (r i) * q i) = ∑ i ∈ s, C (r i) * SeedC3.rho g (q i) := by
  unfold SeedC3.rho
  simp only [Finset.mul_sum, map_sum, map_mul, bind₁_C_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem rho_sum {ι : Type*} (g : Matrix (Fin 3) (Fin 3) ℝ) (s : Finset ι)
    (q : ι → MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (∑ i ∈ s, q i) = ∑ i ∈ s, SeedC3.rho g (q i) := by
  unfold SeedC3.rho
  simp only [map_sum, Finset.mul_sum]

theorem linear_apply_eq_sum' (L : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)) (v : Fin 5 → ℝ) (c : Fin 5) :
    L v c = ∑ i : Fin 5, v i * L (Pi.single i 1) c := by
  have hv : v = ∑ i : Fin 5, v i • (Pi.single i 1 : Fin 5 → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [Finset.sum_apply, map_smul]

/-- The frame value of a pullback: expansion through the Jacobian. -/
theorem frameValue_expand (L : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)) (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (q : Fin 5 → ℝ) (u w : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, (C (((L u a * L w b : ℝ)) : ℂ) : MvPolynomial (Fin 3) ℂ) * ω q a b =
      ∑ i : Fin 5, ∑ j : Fin 5, C ((u i * w j : ℝ) : ℂ) *
        ∑ a : Fin 5, ∑ b : Fin 5, C ((L (Pi.single i 1) a * L (Pi.single j 1) b : ℝ) : ℂ) * ω q a b := by
  have sw : ∀ (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ),
      ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
    intro f
    calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hexp : ∀ a b : Fin 5, (C ((L u a * L w b : ℝ) : ℂ) : MvPolynomial (Fin 3) ℂ) * ω q a b =
      ∑ i, ∑ j, C ((u i * w j : ℝ) : ℂ) * (C ((L (Pi.single i 1) a * L (Pi.single j 1) b : ℝ) : ℂ) *
        ω q a b) := by
    intro a b
    rw [linear_apply_eq_sum' L u, linear_apply_eq_sum' L w, Finset.sum_mul_sum]
    push_cast
    simp only [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have key : ∀ (x y : ℂ) (z : MvPolynomial (Fin 3) ℂ), (C x : MvPolynomial (Fin 3) ℂ) * (C y * z) =
        C (x * y) * z := fun x y z => by rw [C_mul, mul_assoc]
    rw [key]
    congr 2
    ring
  simp_rw [hexp]
  rw [sw]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Finset.mul_sum]


/-- **R1: Levi covariance of the seed's frame coefficient.** For `A` with `det A > 0` and `t > 0`,
`ω̃_h(diag(A,t) g)(V,W) = ω̃_{h'}(g)(V,W)` with `h' = slashTwisted (n+3) A h` (`seed_closed_equivariant (iii)`). -/
theorem frameCoefficient_planeLevi (n : ℕ) (h : ℂ → ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (hA : 0 < A.det) (ht : 0 < t) (g V W : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    frameCoefficient (seedForm n h) (planeLevi A t * g) V W =
      frameCoefficient (seedForm n (slashTwisted (n + 3) A h)) g V W := by
  have hmdet : (planeLevi A t).det ≠ 0 := by
    rw [planeLevi_det]; exact (mul_pos hA ht).ne'
  have hmg : (planeLevi A t * g).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hmdet hg
  have hgram : (planeLevi A t * g) * (planeLevi A t * g).transpose =
      planeLevi A t * (g * g.transpose) * (planeLevi A t).transpose := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hchart : gramChart ((planeLevi A t * g) * (planeLevi A t * g).transpose) =
      leviMap A t (gramChart (g * g.transpose)) := by
    rw [hgram]; exact gramChart_planeLevi A t hA ht g hg
  have hp0 : 0 < (gramChart (g * g.transpose)) 3 := by
    show 0 < (gramPlaneTau (g * g.transpose)).im
    exact gramPlaneTau_im_pos g hg
  have hFV : frameValue (seedForm n h) (planeLevi A t * g) V W =
      SeedC3.rho (planeLevi A t) (frameValue (seedForm n (slashTwisted (n + 3) A h)) g V W) := by
    unfold frameValue
    rw [chartTangent_planeLevi A t hA ht g V hg, chartTangent_planeLevi A t hA ht g W hg, hchart]
    rw [frameValue_expand (fderiv ℝ (leviMap A t) (gramChart (g * g.transpose)))
      (seedForm n h) (leviMap A t (gramChart (g * g.transpose))) (chartTangent g V) (chartTangent g W)]
    have hC3 := (seed_closed_equivariant n h).2.2.1 A t hA ht (gramChart (g * g.transpose)) hp0
    rw [rho_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [rho_sum_C_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    have := hC3 i j
    unfold formPullback at this
    rw [this, leviCoefficientAction_eq_rho A t hA.ne' ht.ne']
  unfold frameCoefficient
  rw [hFV, ← rho_mul]
  congr 1
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hmdet),
    Matrix.mul_one]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
