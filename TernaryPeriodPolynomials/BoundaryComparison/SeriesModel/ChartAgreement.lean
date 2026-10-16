module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.TranslatedSeed

@[expose] public section


/-!
# The four plane coordinates of `conePoint` and of `gramChart` agree on symmetric Gram matrices

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.FormCochainBridge TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
  TernaryPeriodPolynomials.Argument

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem symPart_of_isSymm {G : Mat3} (hG : G.IsSymm) : symPart G = G := by
  have : G.transpose = G := hG
  simp [symPart, this, ← two_smul ℝ G, smul_smul]

theorem gramCone_pos22 {G : Mat3} (hG : G ∈ gramCone) : 0 < G 2 2 := by
  have := (mem_gramCone_iff.1 hG) ![0, 0, 1] (by intro h; simpa using congrFun h 2)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this

theorem gramCone_minor_pos {G : Mat3} (hG : G ∈ gramCone) (hs : G.IsSymm) :
    0 < G 1 1 * G 2 2 - G 1 2 * G 1 2 := by
  have h22 := gramCone_pos22 hG
  have h := (mem_gramCone_iff.1 hG) ![0, G 2 2, -G 1 2] (by
    intro h; have := congrFun h 1; simp at this; linarith)
  have s21 : G 2 1 = G 1 2 := by
    have := congrFun (congrFun hs 1) 2; simpa [Matrix.transpose_apply] using this
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  rw [s21] at h
  nlinarith [mul_pos h22 h22]

theorem isSymm_entry {G : Mat3} (hs : G.IsSymm) (i j : Fin 3) : G j i = G i j := by
  have := congrFun (congrFun hs i) j
  simpa [Matrix.transpose_apply] using this

theorem det_eq_mul_schur {G : Mat3} (hs : G.IsSymm) (h22 : G 2 2 ≠ 0) :
    G.det = G 2 2 * (gramSchur G).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp only [gramSchur, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  rw [isSymm_entry hs 0 1, isSymm_entry hs 0 2, isSymm_entry hs 1 2]
  field_simp
  ring

theorem mem_gramDomain_of_cone {G : Mat3} (hG : G ∈ gramCone) (hs : G.IsSymm) : G ∈ gramDomain := by
  have h22 := gramCone_pos22 hG
  have hm := gramCone_minor_pos hG hs
  refine ⟨h22, ?_, ?_⟩
  · have : (gramSchur G) 1 1 = (G 1 1 * G 2 2 - G 1 2 * G 1 2) / G 2 2 := by
      simp only [gramSchur, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.empty_val']
      field_simp
    rw [this]; exact div_pos hm h22
  · have hd : 0 < G.det := by
      have := (posDef_symPart hG).det_pos
      rwa [symPart_of_isSymm hs] at this
    rw [det_eq_mul_schur hs h22.ne'] at hd
    exact (pos_iff_pos_of_mul_pos hd).1 h22

theorem conePoint_apply_eq {G : Mat3} (hG : G ∈ gramCone) (hs : G.IsSymm) (a : Fin 5) (ha : a ≠ 4) :
    conePoint G a = gramChart G a := by
  have hD := mem_gramDomain_of_cone hG hs
  obtain ⟨h22, hS11pos0, hdS⟩ := hD
  have hdet : 0 < G.det := by
    have := (posDef_symPart hG).det_pos
    rwa [symPart_of_isSymm hs] at this
  set c : ℝ := G.det ^ (-(1 / 3 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hdet _
  have hc3 : c ^ 3 * G.det = 1 := by
    have : c ^ 3 = G.det⁻¹ := by
      rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hdet.le]
      norm_num
      exact Real.rpow_neg_one G.det
    rw [this]; exact inv_mul_cancel₀ hdet.ne'
  have hN : ∀ i j, (normGram (symPart G)) i j = c * G i j := by
    intro i j
    rw [symPart_of_isSymm hs]
    simp [normGram, hc]
  have hS11 : gramSchur G 1 1 = G 1 1 - G 1 2 * G 1 2 / G 2 2 := by
    simp [gramSchur]
  have hS01 : gramSchur G 0 1 = G 0 1 - G 0 2 * G 1 2 / G 2 2 := by
    simp [gramSchur]
  have hS00 : gramSchur G 0 0 = G 0 0 - G 0 2 * G 0 2 / G 2 2 := by
    simp [gramSchur]
  have hS10 : gramSchur G 1 0 = gramSchur G 0 1 := by
    simp only [gramSchur, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [isSymm_entry hs 0 1]; ring
  have hS11' : 0 < G 1 1 - G 1 2 * G 1 2 / G 2 2 := by rw [← hS11]; exact hS11pos0
  have hcne : c ≠ 0 := hcpos.ne'
  have h22' : G 2 2 ≠ 0 := h22.ne'
  have hnum : ∀ i j : Fin 3, normGram (symPart G) i j = c * G i j := hN
  have hu0 : normGram (symPart G) 0 2 / normGram (symPart G) 2 2 = G 0 2 / G 2 2 := by
    rw [hN, hN]; exact mul_div_mul_left _ _ hcne
  have hu1 : normGram (symPart G) 1 2 / normGram (symPart G) 2 2 = G 1 2 / G 2 2 := by
    rw [hN, hN]; exact mul_div_mul_left _ _ hcne
  have hden : normGram (symPart G) 1 1 - normGram (symPart G) 1 2 * normGram (symPart G) 1 2 /
      normGram (symPart G) 2 2 = c * (G 1 1 - G 1 2 * G 1 2 / G 2 2) := by
    rw [hN, hN, hN]; field_simp
  have hnum2 : normGram (symPart G) 0 1 - normGram (symPart G) 0 2 * normGram (symPart G) 1 2 /
      normGram (symPart G) 2 2 = c * (G 0 1 - G 0 2 * G 1 2 / G 2 2) := by
    rw [hN, hN, hN, hN]; field_simp
  unfold conePoint
  fin_cases a
  · simp only [planePoint, Fin.zero_eta, Matrix.cons_val_zero]
    simp only [gramChart, gramPlaneU, Matrix.cons_val_zero]
    exact hu0
  · simp only [planePoint, Fin.mk_one, Matrix.cons_val_one]
    simp only [gramChart, gramPlaneU, Matrix.cons_val_one]
    exact hu1
  · simp only [planePoint, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [gramChart, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [gramChart_re_tau, hS01, hS11, hden, hnum2]
    exact mul_div_mul_left _ _ hcne
  · simp only [planePoint, Fin.reduceFinMk, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    simp only [gramChart, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    rw [gramChart_im_tau, hS11, hden, hN 2 2]
    have hsq : 0 < Real.sqrt (c * G 2 2) := Real.sqrt_pos.2 (mul_pos hcpos h22)
    have hdetS : (gramSchur G).det = (1 / (Real.sqrt (c * G 2 2) * c)) ^ 2 := by
      have h1 := det_eq_mul_schur hs h22'
      have h2 : (Real.sqrt (c * G 2 2)) ^ 2 = c * G 2 2 := Real.sq_sqrt (mul_pos hcpos h22).le
      have h3 : (gramSchur G).det = 1 / (c ^ 3 * G 2 2) := by
        field_simp
        nlinarith [hc3, h1]
      rw [h3, div_pow, one_pow, mul_pow, h2]
      congr 1; ring
    rw [hdetS, Real.sqrt_sq (by positivity)]
    field_simp
  · exact absurd rfl ha

theorem fderiv_conePoint_apply {G Q : Mat3} (hG : G ∈ gramCone) (hGs : G.IsSymm) (hQs : Q.IsSymm)
    (a : Fin 5) (ha : a ≠ 4) : fderiv ℝ conePoint G Q a = planeTangent G Q a := by
  have hline : HasDerivAt (fun ε : ℝ => G + ε • Q) Q 0 := line_hasDerivAt G Q
  have hd : DifferentiableAt ℝ conePoint (G + (0 : ℝ) • Q) := by
    rw [zero_smul, add_zero]
    exact (contDiffOn_conePoint G hG).contDiffAt (isOpen_gramCone.mem_nhds hG) |>.differentiableAt (by simp)
  have h1 : HasDerivAt (conePoint ∘ fun ε : ℝ => G + ε • Q) (fderiv ℝ conePoint (G + (0 : ℝ) • Q) Q) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have h0 : G + (0 : ℝ) • Q = G := by simp
  rw [h0] at h1
  have h2 : HasDerivAt (fun ε : ℝ => conePoint (G + ε • Q) a) (fderiv ℝ conePoint G Q a) 0 :=
    (hasDerivAt_pi.1 h1) a
  have hev : (fun ε : ℝ => conePoint (G + ε • Q) a) =ᶠ[nhds 0] fun ε : ℝ => gramChart (G + ε • Q) a := by
    have hopen : IsOpen {ε : ℝ | G + ε • Q ∈ gramCone} :=
      isOpen_gramCone.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds (by simpa using hG)] with ε hε
    exact conePoint_apply_eq hε (line_isSymm G Q hGs hQs ε) a ha
  have h3 := (hev.hasDerivAt_iff).1 h2
  exact h3.unique (hasDerivAt_gramChart_line G Q hGs hQs (mem_gramDomain_of_cone hG hGs) a)

theorem seedForm_four_left (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (j : Fin 5) : seedForm n h p 4 j = 0 := by
  simp [seedForm, seedBeta, seedDTau]

theorem seedForm_four_right (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i : Fin 5) : seedForm n h p i 4 = 0 := by
  simp [seedForm, seedBeta, seedDTau]

theorem seedForm_congr (n : ℕ) (h : ℂ → ℂ) {p p' : Fin 5 → ℝ} (hp : ∀ i : Fin 5, i ≠ 4 → p i = p' i) (i j : Fin 5) :
    seedForm n h p i j = seedForm n h p' i j := by
  have h0 := hp 0 (by decide); have h1 := hp 1 (by decide); have h2 := hp 2 (by decide); have h3 := hp 3 (by decide)
  simp only [seedForm, seedBeta, seedDTau, seedLinear, seedTau, h0, h1, h2, h3]

theorem isSymm_affTri {P₀ P₁ P₂ : Mat3} (h₀ : P₀.IsSymm) (h₁ : P₁.IsSymm) (h₂ : P₂.IsSymm) (q : ℝ × ℝ) :
    (affTri P₀ P₁ P₂ q).IsSymm := by
  unfold affTri Matrix.IsSymm at *
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, h₀, h₁, h₂]

/-- **The Gram-cone pullback of the seed is the library's `formPair`**: on symmetric tangent vectors at a symmetric Gram matrix the
normalized chart `conePoint` and the chart `gramChart` give the same value of the seed `ω_h` (the seed ignores the fifth coordinate). -/
theorem seed_cone_eq_formPair (n : ℕ) (h : ℂ → ℂ) {G Q₁ Q₂ : Mat3} (hG : G ∈ gramCone) (hGs : G.IsSymm)
    (h1 : Q₁.IsSymm) (h2 : Q₂.IsSymm) :
    ∑ k : Fin 5, ∑ l : Fin 5, MvPolynomial.C (((fderiv ℝ conePoint G Q₁ k * fderiv ℝ conePoint G Q₂ l : ℝ)) : ℂ) *
        seedForm n h (conePoint G) k l = formPair (seedForm n h) G Q₁ Q₂ := by
  unfold formPair
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hk : k = 4
  · subst hk; simp [seedForm_four_left]
  by_cases hl : l = 4
  · subst hl; simp [seedForm_four_right]
  rw [fderiv_conePoint_apply hG hGs h1 k hk, fderiv_conePoint_apply hG hGs h2 l hl,
    seedForm_congr n h (fun i hi => conePoint_apply_eq hG hGs i hi) k l]

theorem isSymm_gramOf (y : GeneralEisenstein.RealGL3) : (gramOf y).IsSymm := by
  unfold gramOf Matrix.IsSymm
  simp [Matrix.transpose_mul]

theorem isSymm_conj {g P : Mat3} (hP : P.IsSymm) : (g * P * g.transpose).IsSymm := by
  unfold Matrix.IsSymm at *
  simp [Matrix.transpose_mul, hP, Matrix.mul_assoc]

/-- **`seedTri` at translated vertices is the library's `twPull`-integrand `formPair`**. -/
theorem seedTri_translate (n : ℕ) (h : ℂ → ℂ) (δ : Matrix.SpecialLinearGroup (Fin 3) ℤ)
    (y : Fin 3 → GeneralEisenstein.RealGL3) {q : ℝ × ℝ} (hq : q ∈ stdTriangle) :
    seedTri n h (fun i => Matrix.SpecialLinearGroup.mapGL ℝ δ * y i) q =
      formPair (seedForm n h) (realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose)
        (realMat δ * (gramOf (y 1) - gramOf (y 0)) * (realMat δ).transpose)
        (realMat δ * (gramOf (y 2) - gramOf (y 0)) * (realMat δ).transpose) := by
  have hp : ∀ i, gramOf (y i) ∈ gramCone := fun i => gramOf_mem_gramCone (y i)
  have hpt : affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q ∈ gramCone :=
    affTri_mem convex_gramCone (hp 0) (hp 1) (hp 2) hq
  have e1 : ∀ i, gramOf (Matrix.SpecialLinearGroup.mapGL ℝ δ * y i) =
      realMat δ * gramOf (y i) * (realMat δ).transpose := by
    intro i; rw [gramOf_mul, mapGL_val]
  have haff : affTri (realMat δ * gramOf (y 0) * (realMat δ).transpose)
      (realMat δ * gramOf (y 1) * (realMat δ).transpose) (realMat δ * gramOf (y 2) * (realMat δ).transpose) q =
      realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose := by
    simp only [affTri]
    simp only [← FormCochainBridge.conjCLM_apply, map_add, map_smul, map_sub]
  have hdiff : ∀ i j, realMat δ * gramOf (y i) * (realMat δ).transpose -
      realMat δ * gramOf (y j) * (realMat δ).transpose =
      realMat δ * (gramOf (y i) - gramOf (y j)) * (realMat δ).transpose := by
    intro i j; simp [Matrix.mul_sub, Matrix.sub_mul]
  have hcone : realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose ∈ gramCone :=
    conj_mem_gramCone (det_realMat δ) hpt
  have hsy : ∀ i j, (gramOf (y i) - gramOf (y j)).IsSymm := by
    intro i j; unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, isSymm_gramOf, isSymm_gramOf]
  unfold seedTri
  simp only [e1, haff, hdiff]
  exact seed_cone_eq_formPair n h hcone
    (isSymm_conj (isSymm_affTri (isSymm_gramOf _) (isSymm_gramOf _) (isSymm_gramOf _) q))
    (isSymm_conj (hsy 1 0)) (isSymm_conj (hsy 2 0))

/-- **The library's plane integral cochain `planeIntG` at `M = δ ∈ SL₃(ℤ)` is the translated seed Gram-triangle cochain.** -/
theorem planeIntG_eq_seedTri (n : ℕ) (h : ℂ → ℂ) (δ : Matrix.SpecialLinearGroup (Fin 3) ℤ)
    (y : Fin 3 → GeneralEisenstein.RealGL3) (κ : Fin 3 →₀ ℕ) :
    planeIntG n h (realMat δ) (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ =
      ∫ q in stdTriangle, (rho (realMat δ)⁻¹
        (seedTri n h (fun i => Matrix.SpecialLinearGroup.mapGL ℝ δ * y i) q)).coeff κ := by
  unfold planeIntG
  refine MeasureTheory.setIntegral_congr_fun measurableSet_stdTriangle fun q hq => ?_
  rw [seedTri_translate n h δ y hq]
  rfl

open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4 TernaryPeriodPolynomials.Argument.Statements.EisensteinClass in
/-- **R1 (classical side).**  The coefficient of the Gram-triangle cochain of the Eisenstein series is the sum over the cosets
`Γ_P δ` of the library's plane integral cochains `planeIntG` of the seed `ω_f` at the group element `δ`:
`coeff_m F(y) = ∑'_{c} planeIntG n (f ∘ ofComplex) (realMat δ_c) (gramOf y₀) (gramOf y₁) (gramOf y₂) m`.
This is exactly the shape of the first summand of `cOmegaCoeff n D F y g` (at `g_∞ = δ_c`), so the series is the coset sum of the
holomorphic halves of `cOmega`. -/
theorem coeff_gramCochain_planeIntG (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {Fm : Type*}
    [FunLike Fm UpperHalfPlane ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
    [CuspFormClass Fm Λ ((n + 3 : ℕ) : ℤ)] (f : Fm) (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (y : Fin 3 → GeneralEisenstein.RealGL3) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (gramCochain Γ n (planeEisensteinInv Γ Λ n f hn hLevi) y)).coeff m =
      ∑' c : PlaneCoset Γ, planeIntG n (fun z => f (UpperHalfPlane.ofComplex z)) (realMat (Quotient.out c).1)
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) m := by
  rw [coeff_gramCochain_translated Γ Λ n f hn hLevi y m]
  exact tsum_congr fun c => (planeIntG_eq_seedTri n _ _ y m).symm

end TernaryPeriodPolynomials.Argument.FormSeriesModel
