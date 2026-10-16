module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Seed

@[expose] public section


/-!
# The tangent vector of the plane chart in closed form

For an invertible `g` the tangent `dL_g V` of the plane horospherical chart `gramChart` at `g SO(3)`
(the paper's `dL_g V` in plane coordinates, `chartTangent g V`) is computed in closed form:
with `G = g gᵀ` and `D = g (V + Vᵀ) gᵀ` it is `planeTangent G D`, whose entries are

* `du_i = (D_{i2} G₂₂ - G_{i2} D₂₂) / G₂₂²`,
* `dτ = i (dS₀₀ - 2τ dS₀₁ + τ² dS₁₁) / (2 √det S)` with `S` the Schur complement of `G₂₂` and
  `dS_{ij} = D_{ij} - (D_{i2}G_{j2} + G_{i2}D_{j2})/G₂₂ + G_{i2}G_{j2}D₂₂/G₂₂²`,
* `dt = D₂₂ / (2 √G₂₂)`.

The derivative along an arbitrary curve of symmetric matrices with the right positivity is
`hasDerivAt_gramPlaneTau`, `hasDerivAt_gramPlaneU`; `chartTangent_eq` is the bridge to the parent's
`RealEntrySeed.chartTangent`.  Also the positivity of the Gram data of an invertible matrix.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

/-- The pure-algebra derivative of the Schur entry `S_{ij} = G_{ij} - G_{i2}G_{j2}/G_{22}`
in the direction `D`. -/
def schurDeriv (G D : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : ℝ :=
  D i j - (D i 2 * G j 2 + G i 2 * D j 2) / G 2 2 + G i 2 * G j 2 * D 2 2 / G 2 2 ^ 2

theorem hasDerivAt_schur (G : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, HasDerivAt (fun ε => G ε i j) (D i j) 0) (hR : G 0 2 2 ≠ 0) (i j : Fin 3) :
    HasDerivAt (fun ε => G ε i j - G ε i 2 * G ε j 2 / G ε 2 2) (schurDeriv (G 0) D i j) 0 := by
  have h1 := ((hG i 2).mul (hG j 2)).div (hG 2 2) hR
  have h2 := (hG i j).sub h1
  refine HasDerivAt.congr_deriv h2 ?_
  unfold schurDeriv
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem gramSchur_apply (G : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 2) :
    gramSchur G i j = G i.castSucc j.castSucc - G i.castSucc 2 * G j.castSucc 2 / G 2 2 := by
  fin_cases i <;> fin_cases j <;> simp [gramSchur]

theorem gramSchur_det (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) :
    (gramSchur G).det = gramSchur G 0 0 * gramSchur G 1 1 - gramSchur G 0 1 ^ 2 := by
  have h10 : gramSchur G 1 0 = gramSchur G 0 1 := by
    rw [gramSchur_apply, gramSchur_apply]
    have := hG.apply 0 1
    have := hG.apply 0 2
    have := hG.apply 1 2
    simp_all [Fin.castSucc]
    ring
  rw [Matrix.det_fin_two, h10]; ring


/-- The raw real/imaginary derivative formula of `τ = S₀₁/S₁₁ + i √det S / S₁₁`. -/
def tauDerivRaw (s00 s01 s11 d00 d01 d11 : ℝ) : ℂ :=
  (((d01 * s11 - s01 * d11) / s11 ^ 2 : ℝ) : ℂ) + Complex.I *
    (((((d00 * s11 + s00 * d11 - 2 * s01 * d01) / (2 * Real.sqrt (s00 * s11 - s01 ^ 2))) * s11 -
      Real.sqrt (s00 * s11 - s01 ^ 2) * d11) / s11 ^ 2 : ℝ) : ℂ)

/-- The compact form `dτ = i (dS₀₀ - 2 τ dS₀₁ + τ² dS₁₁) / (2 √det S)`. -/
theorem tauDerivRaw_eq (s00 s01 s11 d00 d01 d11 : ℝ) (hs : 0 < s11) (hd : 0 < s00 * s11 - s01 ^ 2) :
    tauDerivRaw s00 s01 s11 d00 d01 d11 =
      Complex.I / (2 * (Real.sqrt (s00 * s11 - s01 ^ 2) : ℂ)) *
        ((d00 : ℂ) - 2 * (((s01 : ℂ) + Complex.I * (Real.sqrt (s00 * s11 - s01 ^ 2) : ℂ)) / s11) * d01 +
          (((s01 : ℂ) + Complex.I * (Real.sqrt (s00 * s11 - s01 ^ 2) : ℂ)) / s11) ^ 2 * d11) := by
  set q := Real.sqrt (s00 * s11 - s01 ^ 2) with hq
  have hqpos : 0 < q := Real.sqrt_pos.mpr hd
  have hq2 : q ^ 2 = s00 * s11 - s01 ^ 2 := Real.sq_sqrt hd.le
  have hs00 : s00 = (q ^ 2 + s01 ^ 2) / s11 := by field_simp; linarith
  unfold tauDerivRaw
  rw [← hq]
  have hsne : (s11 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  rw [hs00]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring


/-- The Schur-complement derivative matrix entries `(i,j) ∈ Fin 2`. -/
def schurDeriv2 (G D : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 2) : ℝ :=
  schurDeriv G D i.castSucc j.castSucc

/-- The derivative of the plane coordinate `τ` along a Gram direction `D`:
`i (dS₀₀ - 2τ dS₀₁ + τ² dS₁₁) / (2 √det S)`. -/
def planeDTau (G D : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  Complex.I / (2 * (Real.sqrt (gramSchur G).det : ℂ)) *
    ((schurDeriv2 G D 0 0 : ℂ) - 2 * gramPlaneTau G * (schurDeriv2 G D 0 1 : ℂ) +
      gramPlaneTau G ^ 2 * (schurDeriv2 G D 1 1 : ℂ))

theorem hasDerivAt_gramPlaneTau (G : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ ε, (G ε).IsSymm) (hG : ∀ i j, HasDerivAt (fun ε => G ε i j) (D i j) 0)
    (hR : 0 < G 0 2 2) (h11 : 0 < gramSchur (G 0) 1 1) (hdet : 0 < (gramSchur (G 0)).det) :
    HasDerivAt (fun ε => gramPlaneTau (G ε)) (planeDTau (G 0) D) 0 := by
  have hS : ∀ i j : Fin 2, HasDerivAt (fun ε => gramSchur (G ε) i j) (schurDeriv2 (G 0) D i j) 0 := by
    intro i j
    have := hasDerivAt_schur G D hG hR.ne' i.castSucc j.castSucc
    simp only [gramSchur_apply]
    exact this
  have hdet' : 0 < gramSchur (G 0) 0 0 * gramSchur (G 0) 1 1 - gramSchur (G 0) 0 1 ^ 2 := by
    rw [← gramSchur_det _ (hsym 0)]; exact hdet
  have hfun : (fun ε => gramPlaneTau (G ε)) = fun ε =>
      ((gramSchur (G ε) 0 1 / gramSchur (G ε) 1 1 : ℝ) : ℂ) + Complex.I *
        ((Real.sqrt (gramSchur (G ε) 0 0 * gramSchur (G ε) 1 1 - gramSchur (G ε) 0 1 ^ 2) /
          gramSchur (G ε) 1 1 : ℝ) : ℂ) := by
    funext ε
    unfold gramPlaneTau
    rw [gramSchur_det _ (hsym ε)]
  rw [hfun]
  have hre := (hS 0 1).div (hS 1 1) h11.ne'
  have hdetD := ((hS 0 0).mul (hS 1 1)).sub ((hS 0 1).pow 2)
  have hsq : HasDerivAt (fun ε => Real.sqrt (gramSchur (G ε) 0 0 * gramSchur (G ε) 1 1 -
      gramSchur (G ε) 0 1 ^ 2)) _ 0 := hdetD.sqrt hdet'.ne'
  have him := hsq.div (hS 1 1) h11.ne'
  have hc := (hre.ofReal_comp).add (him.ofReal_comp.const_mul Complex.I)
  refine HasDerivAt.congr_deriv hc ?_
  have := tauDerivRaw_eq (gramSchur (G 0) 0 0) (gramSchur (G 0) 0 1) (gramSchur (G 0) 1 1)
    (schurDeriv2 (G 0) D 0 0) (schurDeriv2 (G 0) D 0 1) (schurDeriv2 (G 0) D 1 1) h11 hdet'
  have key : planeDTau (G 0) D = tauDerivRaw (gramSchur (G 0) 0 0) (gramSchur (G 0) 0 1)
      (gramSchur (G 0) 1 1) (schurDeriv2 (G 0) D 0 0) (schurDeriv2 (G 0) D 0 1)
      (schurDeriv2 (G 0) D 1 1) := by
    rw [this]
    unfold planeDTau gramPlaneTau
    rw [gramSchur_det _ (hsym 0)]
    push_cast
    ring
  rw [key]
  unfold tauDerivRaw
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]


/-- The derivative of the plane coordinates `u = G_{·2}/G₂₂` in the direction `D`. -/
def planeDU (G D : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 2) : ℝ :=
  (D i.castSucc 2 * G 2 2 - G i.castSucc 2 * D 2 2) / G 2 2 ^ 2

theorem hasDerivAt_gramPlaneU (G : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, HasDerivAt (fun ε => G ε i j) (D i j) 0) (hR : G 0 2 2 ≠ 0) (i : Fin 2) :
    HasDerivAt (fun ε => G ε i.castSucc 2 / G ε 2 2) (planeDU (G 0) D i) 0 :=
  (hG i.castSucc 2).div (hG 2 2) hR

theorem hasDerivAt_gramCurve (g V : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    HasDerivAt (fun ε => gramCurve g V ε i j) ((g * (V + V.transpose) * g.transpose) i j) 0 := by
  have hfun : (fun ε => gramCurve g V ε i j) = fun ε =>
      (g * g.transpose) i j + (ε * ((g * (V + V.transpose) * g.transpose) i j) +
        ε ^ 2 * ((g * V * V.transpose * g.transpose) i j)) := by
    funext ε
    have : gramCurve g V ε = g * g.transpose + ε • (g * (V + V.transpose) * g.transpose) +
        (ε ^ 2) • (g * V * V.transpose * g.transpose) := by
      unfold gramCurve
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, smul_add,
        smul_smul, Matrix.mul_assoc]
      module
    rw [this]
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun ε : ℝ => ε * ((g * (V + V.transpose) * g.transpose) i j))
      ((g * (V + V.transpose) * g.transpose) i j) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const ((g * (V + V.transpose) * g.transpose) i j)
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * ((g * V * V.transpose * g.transpose) i j))
      0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ))).mul_const ((g * V * V.transpose * g.transpose) i j)
  simpa using (h1.add h2).const_add ((g * g.transpose) i j)


/-! ### Positivity of the Gram data of an invertible matrix -/

theorem gram_entry (g : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (g * g.transpose) i j = g i 0 * g j 0 + g i 1 * g j 1 + g i 2 * g j 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

theorem gram_isSymm (g : Matrix (Fin 3) (Fin 3) ℝ) : (g * g.transpose).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_pos_22 (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) : 0 < (g * g.transpose) 2 2 := by
  rw [gram_entry]
  by_contra hle
  rw [not_lt] at hle
  have h0 : g 2 0 = 0 := by nlinarith [sq_nonneg (g 2 0), sq_nonneg (g 2 1), sq_nonneg (g 2 2)]
  have h1 : g 2 1 = 0 := by nlinarith [sq_nonneg (g 2 0), sq_nonneg (g 2 1), sq_nonneg (g 2 2)]
  have h2 : g 2 2 = 0 := by nlinarith [sq_nonneg (g 2 0), sq_nonneg (g 2 1), sq_nonneg (g 2 2)]
  apply hg
  rw [Matrix.det_fin_three, h0, h1, h2]; ring

theorem gram_minor_pos (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    0 < (g * g.transpose) 1 1 * (g * g.transpose) 2 2 - (g * g.transpose) 1 2 ^ 2 := by
  simp only [gram_entry]
  have hl : (g 1 0 * g 1 0 + g 1 1 * g 1 1 + g 1 2 * g 1 2) * (g 2 0 * g 2 0 + g 2 1 * g 2 1 + g 2 2 * g 2 2) -
      (g 1 0 * g 2 0 + g 1 1 * g 2 1 + g 1 2 * g 2 2) ^ 2 =
      (g 1 0 * g 2 1 - g 1 1 * g 2 0) ^ 2 + (g 1 0 * g 2 2 - g 1 2 * g 2 0) ^ 2 +
        (g 1 1 * g 2 2 - g 1 2 * g 2 1) ^ 2 := by ring
  rw [hl]
  by_contra hle
  rw [not_lt] at hle
  have c0 : g 1 0 * g 2 1 - g 1 1 * g 2 0 = 0 := by
    nlinarith [sq_nonneg (g 1 0 * g 2 1 - g 1 1 * g 2 0), sq_nonneg (g 1 0 * g 2 2 - g 1 2 * g 2 0),
      sq_nonneg (g 1 1 * g 2 2 - g 1 2 * g 2 1)]
  have c1 : g 1 0 * g 2 2 - g 1 2 * g 2 0 = 0 := by
    nlinarith [sq_nonneg (g 1 0 * g 2 1 - g 1 1 * g 2 0), sq_nonneg (g 1 0 * g 2 2 - g 1 2 * g 2 0),
      sq_nonneg (g 1 1 * g 2 2 - g 1 2 * g 2 1)]
  have c2 : g 1 1 * g 2 2 - g 1 2 * g 2 1 = 0 := by
    nlinarith [sq_nonneg (g 1 0 * g 2 1 - g 1 1 * g 2 0), sq_nonneg (g 1 0 * g 2 2 - g 1 2 * g 2 0),
      sq_nonneg (g 1 1 * g 2 2 - g 1 2 * g 2 1)]
  apply hg
  rw [Matrix.det_fin_three]
  linear_combination (g 0 0) * c2 - (g 0 1) * c1 + (g 0 2) * c0

theorem gramSchur_det_eq' (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (hR : G 2 2 ≠ 0) :
    (gramSchur G).det = G.det / G 2 2 := by
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have h20 : G 2 0 = G 0 2 := hG.apply 0 2
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  rw [gramSchur_det _ hG, gramSchur_apply, gramSchur_apply, gramSchur_apply, Matrix.det_fin_three,
    h10, h20, h21]
  simp only [Fin.castSucc_zero, Fin.castSucc_one]
  field_simp
  ring

theorem gramSchur_det_eq (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    (gramSchur (g * g.transpose)).det = g.det ^ 2 / (g * g.transpose) 2 2 := by
  rw [gramSchur_det_eq' _ (gram_isSymm g) (gram_pos_22 g hg).ne', Matrix.det_mul,
    Matrix.det_transpose, sq]

theorem gramSchur_pos_11 (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    0 < gramSchur (g * g.transpose) 1 1 := by
  have hR := gram_pos_22 g hg
  have hm := gram_minor_pos g hg
  rw [gramSchur_apply]
  simp only [Fin.castSucc_one]
  have : (g * g.transpose) 1 1 - (g * g.transpose) 1 2 * (g * g.transpose) 1 2 / (g * g.transpose) 2 2 =
      ((g * g.transpose) 1 1 * (g * g.transpose) 2 2 - (g * g.transpose) 1 2 ^ 2) /
        (g * g.transpose) 2 2 := by field_simp
  rw [this]; positivity

theorem gramSchur_det_pos (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    0 < (gramSchur (g * g.transpose)).det := by
  rw [gramSchur_det_eq g hg]
  have := gram_pos_22 g hg
  positivity


/-! ### The tangent vector of the plane chart -/

/-- The plane-chart coordinates of the tangent `D` at the Gram matrix `G`:
`(du₁, du₂, Re dτ, Im dτ, dt)`. -/
def planeTangent (G D : Matrix (Fin 3) (Fin 3) ℝ) : Fin 5 → ℝ :=
  ![planeDU G D 0, planeDU G D 1, (planeDTau G D).re, (planeDTau G D).im,
    D 2 2 / (2 * Real.sqrt (G 2 2))]

theorem gramCurve_zero (g V : Matrix (Fin 3) (Fin 3) ℝ) : gramCurve g V 0 = g * g.transpose := by
  simp [gramCurve]

theorem gramCurve_isSymm (g V : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) : (gramCurve g V ε).IsSymm := by
  unfold gramCurve Matrix.IsSymm
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **The chart tangent is the Fréchet-type derivative of the plane chart.** For an invertible
`g`, `dL_g V` in plane coordinates is `planeTangent (g gᵀ) (g (V + Vᵀ) gᵀ)`. -/
theorem chartTangent_eq (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    chartTangent g V = planeTangent (g * g.transpose) (g * (V + V.transpose) * g.transpose) := by
  have hG := hasDerivAt_gramCurve g V
  have h0 := gramCurve_zero g V
  have hR : 0 < (gramCurve g V 0) 2 2 := by rw [h0]; exact gram_pos_22 g hg
  have h11 : 0 < gramSchur (gramCurve g V 0) 1 1 := by rw [h0]; exact gramSchur_pos_11 g hg
  have hdet : 0 < (gramSchur (gramCurve g V 0)).det := by rw [h0]; exact gramSchur_det_pos g hg
  have hτ := hasDerivAt_gramPlaneTau (gramCurve g V) _ (gramCurve_isSymm g V) hG hR h11 hdet
  have hu := hasDerivAt_gramPlaneU (gramCurve g V) _ hG hR.ne'
  have hs := ((hG 2 2).sqrt hR.ne')
  rw [h0] at hτ hu hs
  funext a
  unfold chartTangent planeTangent
  fin_cases a
  · exact (hu 0).deriv
  · exact (hu 1).deriv
  · have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hτ
    exact this.deriv
  · have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hτ
    exact this.deriv
  · exact hs.deriv

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
