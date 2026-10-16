module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitTransport

@[expose] public section


/-!
# The closed form of the lower radical coordinate of the mixed derivative

In the disc coordinate `w = (z - i) / (z + i)` of the Levi point `z = z(u)` of the good-line
vertex, the lower radical coordinate of the mixed derivative vector is
`κ R^{-(n+3)} (G_h(w) Ψ(w) + G_{hJ}(w₂) Ψ'(w₂))`, where `κ = (n + 1) / 8 · (-1/2)ⁿ`,
`G_h(w) = F_h(z) (z + i)^{n+3}` for `z = i (1 + w) / (1 - w)`, `w₂` is the disc coordinate of
`refl z`, and `Ψ(w) = ((1 - 3w²) L₋ + (3w - w³) L₊) (L₋ - w L₊)ⁿ`,
`Ψ'(w) = ((1 - 3w²) L₊ + (3w - w³) L₋) (L₊ - w L₋)ⁿ`, with `L₋ = X₀ + i X₁`, `L₊ = X₀ - i X₁`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### The disc coordinate -/

/-- The disc coordinate `w = N / E = (z - i) / (z + i)` of the Levi point `z(u)`. -/
def holDisc (u : ℝ × ℝ) : ℂ := holN u / holE u

/-- The disc coordinate `N₂ / E₂` of the reflected Levi point `refl z(u)`. -/
def antiDisc (u : ℝ × ℝ) : ℂ := antiN u / antiE u

/-- The point `i (1 + w) / (1 - w)` of the upper half plane. -/
def diskPoint (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

/-- The holomorphic function `G(w) = F_h(z) (z + i)^{n+3}`, `z = i (1 + w) / (1 - w)`, on the
unit disc. -/
def discForm (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (w : ℂ) : ℂ :=
  F h (diskPoint w) * (diskPoint w + Complex.I) ^ (n + 3)

/-- The cubic `1 + 3w - 3w² - w³`. -/
def discP (w : ℂ) : ℂ := 1 + 3 * w - 3 * w ^ 2 - w ^ 3

/-- The cubic `i (1 - 3w - 3w² + w³)`. -/
def discQ (w : ℂ) : ℂ := Complex.I * (1 - 3 * w - 3 * w ^ 2 + w ^ 3)

/-- The constant `κ = (n + 1) / 8 · (-1/2)ⁿ`. -/
def edgeConstant (n : ℕ) : ℂ := ((n : ℂ) + 1) / 8 * (-1 / 2) ^ n

theorem holE_im (u : ℝ × ℝ) : (holE u).im = gsRadius u + gsAlpha u ^ 2 := by
  simp [holE, ← Complex.ofReal_pow]

theorem antiE_im (u : ℝ × ℝ) : (antiE u).im = gsRadius u + gsAlpha u ^ 2 := by
  simp [antiE, ← Complex.ofReal_pow]

theorem holE_ne_zero (u : ℝ × ℝ) : holE u ≠ 0 := by
  intro zero
  have := holE_im u
  rw [zero, Complex.zero_im] at this
  have := gsRadius_pos u
  nlinarith [sq_nonneg (gsAlpha u)]

theorem antiE_ne_zero (u : ℝ × ℝ) : antiE u ≠ 0 := by
  intro zero
  have := antiE_im u
  rw [zero, Complex.zero_im] at this
  have := gsRadius_pos u
  nlinarith [sq_nonneg (gsAlpha u)]

theorem holE_sub_holN (u : ℝ × ℝ) : holE u - holN u = 2 * Complex.I * (gsAlpha u : ℂ) ^ 2 := by
  simp only [holE, holN]
  ring

theorem antiE_sub_antiN (u : ℝ × ℝ) :
    antiE u - antiN u = 2 * Complex.I * (gsAlpha u : ℂ) ^ 2 := by
  simp only [antiE, antiN]
  ring

theorem goodPoint_add_I (u : ℝ × ℝ) : goodPoint u + Complex.I = holE u / (gsAlpha u : ℂ) ^ 2 := by
  have ha := gsAlpha_complex_ne_zero u
  rw [goodPoint, holE]
  field_simp
  ring

theorem reflection_goodPoint (u : ℝ × ℝ) :
    binaryComplexReflection (goodPoint u) =
      (Complex.I * (gsRadius u : ℂ) + (u.1 : ℂ) * (u.2 : ℂ)) / (gsAlpha u : ℂ) ^ 2 := by
  rw [goodPoint, binaryComplexReflection]
  simp only [_root_.neg_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_div₀,
    map_sub, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem reflection_goodPoint_add_I (u : ℝ × ℝ) :
    binaryComplexReflection (goodPoint u) + Complex.I = antiE u / (gsAlpha u : ℂ) ^ 2 := by
  have ha := gsAlpha_complex_ne_zero u
  rw [reflection_goodPoint, antiE]
  field_simp
  ring

theorem diskPoint_holDisc (u : ℝ × ℝ) : diskPoint (holDisc u) = goodPoint u := by
  have hE := holE_ne_zero u
  have ha := gsAlpha_complex_ne_zero u
  have hEN := holE_sub_holN u
  rw [diskPoint, holDisc, goodPoint, one_add_div hE, one_sub_div hE, mul_div_assoc',
    div_div_div_cancel_right₀ hE, hEN]
  simp only [holE, holN]
  field_simp
  ring

theorem diskPoint_antiDisc (u : ℝ × ℝ) :
    diskPoint (antiDisc u) = binaryComplexReflection (goodPoint u) := by
  have hE := antiE_ne_zero u
  have ha := gsAlpha_complex_ne_zero u
  have hEN := antiE_sub_antiN u
  rw [diskPoint, antiDisc, reflection_goodPoint, one_add_div hE, one_sub_div hE, mul_div_assoc',
    div_div_div_cancel_right₀ hE, hEN]
  simp only [antiE, antiN]
  field_simp
  ring

theorem discForm_holDisc (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    discForm n F h (holDisc u) = F h (goodPoint u) * (holE u / (gsAlpha u : ℂ) ^ 2) ^ (n + 3) := by
  rw [discForm, diskPoint_holDisc, goodPoint_add_I]

theorem discForm_antiDisc (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    discForm n F h (antiDisc u) = F h (binaryComplexReflection (goodPoint u)) *
      (antiE u / (gsAlpha u : ℂ) ^ 2) ^ (n + 3) := by
  rw [discForm, diskPoint_antiDisc, reflection_goodPoint_add_I]

/-! ### The coefficients in the disc coordinate -/

theorem C_mul_binaryLin (μ p q : ℂ) : C μ * binaryLin p q = binaryLin (μ * p) (μ * q) := by
  simp only [binaryLin, map_mul]
  ring

theorem two_I_cube (a : ℂ) : (2 * Complex.I * a ^ 2) ^ 3 = -8 * Complex.I * a ^ 6 := by
  linear_combination (8 * Complex.I * a ^ 6) * Complex.I_sq

theorem binaryLin_hol_of_identity {c₀ c₁ E N a R : ℂ} (hE : E ≠ 0) (ha : a ≠ 0) (hR : R ≠ 0)
    (h₁ : c₁ * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 = -2 * Complex.I * a ^ 3 * cubicP E N)
    (h₀ : c₀ * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 =
      2 * Complex.I * a ^ 3 * (Complex.I * cubicQ E N)) :
    binaryLin (-c₁) c₀ =
      C (-E ^ 3 / (4 * a ^ 3 * R ^ 3)) * binaryLin (discP (N / E)) (discQ (N / E)) := by
  have hD : -8 * Complex.I * a ^ 6 * R ^ 3 ≠ 0 := by
    have := Complex.I_ne_zero
    simp_all
  rw [two_I_cube, mul_assoc] at h₁ h₀
  rw [eq_div_of_mul_eq hD h₁, eq_div_of_mul_eq hD h₀, C_mul_binaryLin]
  have := Complex.I_ne_zero
  congr 1 <;> simp only [discP, discQ, cubicP, cubicQ] <;> field_simp <;> ring

theorem binaryLin_anti_of_identity {c₀ c₁ E N a R : ℂ} (hE : E ≠ 0) (ha : a ≠ 0) (hR : R ≠ 0)
    (h₁ : c₁ * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 = -2 * Complex.I * a ^ 3 * cubicP E N)
    (h₀ : c₀ * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 =
      2 * Complex.I * a ^ 3 * (-Complex.I * cubicQ E N)) :
    binaryLin (-c₁) c₀ =
      C (-E ^ 3 / (4 * a ^ 3 * R ^ 3)) * binaryLin (discP (N / E)) (-discQ (N / E)) := by
  have hD : -8 * Complex.I * a ^ 6 * R ^ 3 ≠ 0 := by
    have := Complex.I_ne_zero
    simp_all
  rw [two_I_cube, mul_assoc] at h₁ h₀
  rw [eq_div_of_mul_eq hD h₁, eq_div_of_mul_eq hD h₀, C_mul_binaryLin]
  have := Complex.I_ne_zero
  congr 1 <;> simp only [discP, discQ, cubicP, cubicQ] <;> field_simp <;> ring

theorem binaryLin_holCoeff (u : ℝ × ℝ) :
    binaryLin (-holCoeff u 1) (holCoeff u 0) =
      C (-holE u ^ 3 / (4 * (gsAlpha u : ℂ) ^ 3 * (gsRadius u : ℂ) ^ 3)) *
        binaryLin (discP (holDisc u)) (discQ (holDisc u)) :=
  binaryLin_hol_of_identity (holE_ne_zero u) (gsAlpha_complex_ne_zero u)
    (gsRadius_complex_ne_zero u) (holCoeff_one_eq u) (holCoeff_zero_eq u)

theorem binaryLin_antiCoeff (u : ℝ × ℝ) :
    binaryLin (-antiCoeff u 1) (antiCoeff u 0) =
      C (-antiE u ^ 3 / (4 * (gsAlpha u : ℂ) ^ 3 * (gsRadius u : ℂ) ^ 3)) *
        binaryLin (discP (antiDisc u)) (-discQ (antiDisc u)) :=
  binaryLin_anti_of_identity (antiE_ne_zero u) (gsAlpha_complex_ne_zero u)
    (gsRadius_complex_ne_zero u) (antiCoeff_one_eq u) (antiCoeff_zero_eq u)

theorem holE_add_holN (u : ℝ × ℝ) :
    holE u + holN u = 2 * (Complex.I * (gsRadius u : ℂ) - (u.1 : ℂ) * (u.2 : ℂ)) := by
  simp only [holE, holN]
  ring

theorem antiE_add_antiN (u : ℝ × ℝ) :
    antiE u + antiN u = 2 * (Complex.I * (gsRadius u : ℂ) + (u.1 : ℂ) * (u.2 : ℂ)) := by
  simp only [antiE, antiN]
  ring

theorem binaryLin_holFrame (u : ℝ × ℝ) :
    binaryLin (complexOrth u 0 0 - Complex.I * complexOrth u 1 0)
        (complexOrth u 0 1 - Complex.I * complexOrth u 1 1) =
      C (-holE u / (2 * (gsAlpha u : ℂ) * (gsRadius u : ℂ))) *
        binaryLin (1 - holDisc u) (Complex.I * (1 + holDisc u)) := by
  have hE := holE_ne_zero u
  have ha := gsAlpha_complex_ne_zero u
  have hR := gsRadius_complex_ne_zero u
  have key : Complex.I * ((holE u + holN u) / holE u) =
      (-2 * (gsRadius u : ℂ) - 2 * Complex.I * (u.1 : ℂ) * (u.2 : ℂ)) / holE u := by
    rw [holE_add_holN, ← mul_div_assoc]
    congr 1
    linear_combination (2 * (gsRadius u : ℂ)) * Complex.I_sq
  rw [C_mul_binaryLin]
  simp only [complexOrth_apply, gsOrthMatrix_00, gsOrthMatrix_10, gsOrthMatrix_01,
    gsOrthMatrix_11, holDisc]
  push_cast
  congr 1
  · rw [one_sub_div hE, holE_sub_holN]
    field_simp
    ring
  · rw [one_add_div hE, key]
    field_simp
    ring

theorem binaryLin_antiFrame (u : ℝ × ℝ) :
    binaryLin (-complexOrth u 0 0 - Complex.I * complexOrth u 1 0)
        (-complexOrth u 0 1 - Complex.I * complexOrth u 1 1) =
      C (-antiE u / (2 * (gsAlpha u : ℂ) * (gsRadius u : ℂ))) *
        binaryLin (1 - antiDisc u) (-Complex.I * (1 + antiDisc u)) := by
  have hE := antiE_ne_zero u
  have ha := gsAlpha_complex_ne_zero u
  have hR := gsRadius_complex_ne_zero u
  have key : -Complex.I * ((antiE u + antiN u) / antiE u) =
      (2 * (gsRadius u : ℂ) - 2 * Complex.I * (u.1 : ℂ) * (u.2 : ℂ)) / antiE u := by
    rw [antiE_add_antiN, ← mul_div_assoc]
    congr 1
    linear_combination (-2 * (gsRadius u : ℂ)) * Complex.I_sq
  rw [C_mul_binaryLin]
  simp only [complexOrth_apply, gsOrthMatrix_00, gsOrthMatrix_10, gsOrthMatrix_01,
    gsOrthMatrix_11, antiDisc]
  push_cast
  congr 1
  · rw [one_sub_div hE, antiE_sub_antiN]
    field_simp
    ring
  · rw [one_add_div hE, key]
    field_simp
    ring

/-- **The scalar in the disc coordinate.** -/
theorem edge_scalar_identity (q a R E F₀ : ℂ) (hq : q ≠ 0) (ha : a ≠ 0) (hR : R ≠ 0) :
    (q ^ (n + 3))⁻¹ * ((-1 : ℝ) : ℂ) * 2⁻¹ * ((n : ℂ) + 1) * (((a / q) ^ (n + 3))⁻¹ * F₀) *
        (-E ^ 3 / (4 * a ^ 3 * R ^ 3)) * (-E / (2 * a * R)) ^ n =
      edgeConstant n * (R ^ (n + 3))⁻¹ * (F₀ * (E / a ^ 2) ^ (n + 3)) := by
  rw [edgeConstant, div_pow (-1 : ℂ) 2 n]
  simp only [div_pow, neg_div, neg_pow (E / (2 * a * R)), mul_pow, Complex.ofReal_neg,
    Complex.ofReal_one]
  field_simp
  ring

/-! ### The two polynomial factors -/

/-- `Ψ(w) = ((1 - 3w²) L₋ + (3w - w³) L₊) (L₋ - w L₊)ⁿ` in the weight basis
`L₋^j L₊^{n+1-j}`. -/
def holPsi (n : ℕ) (w : ℂ) : Binary.HomogeneousPoly (n + 1) :=
  ∑ m : Fin (n + 1), ((n.choose m : ℂ) * (-w) ^ (n - m)) •
    ((1 - 3 * w ^ 2) • binaryWeightBasis (n + 1) m.succ +
      (3 * w - w ^ 3) • binaryWeightBasis (n + 1) m.castSucc)

/-- `Ψ'(w) = ((1 - 3w²) L₊ + (3w - w³) L₋) (L₊ - w L₋)ⁿ` in the weight basis. -/
def antiPsi (n : ℕ) (w : ℂ) : Binary.HomogeneousPoly (n + 1) :=
  ∑ m : Fin (n + 1), ((n.choose m : ℂ) * (-w) ^ (n - m)) •
    ((1 - 3 * w ^ 2) • binaryWeightBasis (n + 1) m.rev.castSucc +
      (3 * w - w ^ 3) • binaryWeightBasis (n + 1) m.rev.succ)

theorem binaryLin_disc (w : ℂ) : binaryLin (discP w) (discQ w) =
    C (1 - 3 * w ^ 2) * binaryPositiveCoordinate +
      C (3 * w - w ^ 3) * binaryNegativeCoordinate := by
  simp only [binaryLin, discP, discQ, binaryPositiveCoordinate, binaryNegativeCoordinate, map_add,
    map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

theorem binaryLin_disc_anti (w : ℂ) : binaryLin (discP w) (-discQ w) =
    C (1 - 3 * w ^ 2) * binaryNegativeCoordinate +
      C (3 * w - w ^ 3) * binaryPositiveCoordinate := by
  simp only [binaryLin, discP, discQ, binaryPositiveCoordinate, binaryNegativeCoordinate, map_add,
    map_sub, map_mul, map_pow, map_ofNat, map_one, map_neg]
  ring

theorem binaryLin_frame (w : ℂ) : binaryLin (1 - w) (Complex.I * (1 + w)) =
    binaryPositiveCoordinate + C (-w) * binaryNegativeCoordinate := by
  simp only [binaryLin, binaryPositiveCoordinate, binaryNegativeCoordinate, map_add, map_sub,
    map_mul, map_one, map_neg]
  ring

theorem binaryLin_frame_anti (w : ℂ) : binaryLin (1 - w) (-Complex.I * (1 + w)) =
    binaryNegativeCoordinate + C (-w) * binaryPositiveCoordinate := by
  simp only [binaryLin, binaryPositiveCoordinate, binaryNegativeCoordinate, map_add, map_sub,
    map_mul, map_one, map_neg]
  ring

theorem holPsi_val (w : ℂ) : (holPsi n w).val =
    binaryLin (discP w) (discQ w) * binaryLin (1 - w) (Complex.I * (1 + w)) ^ n := by
  rw [binaryLin_disc, binaryLin_frame, add_pow, Finset.mul_sum, holPsi, Submodule.coe_sum,
    ← Fin.sum_univ_eq_sum_range (fun m => (C (1 - 3 * w ^ 2) * binaryPositiveCoordinate +
      C (3 * w - w ^ 3) * binaryNegativeCoordinate) *
      (binaryPositiveCoordinate ^ m * (C (-w) * binaryNegativeCoordinate) ^ (n - m) *
        (n.choose m : Binary.Poly)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm := m.isLt
  rw [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    binaryWeightBasis_coe, binaryWeightBasis_coe]
  simp only [Fin.val_succ, Fin.val_castSucc, smul_eq_C_mul]
  rw [show n + 1 - (m + 1) = n - m by omega, show n + 1 - (m : ℕ) = n - m + 1 by omega]
  simp only [mul_pow, map_mul, map_pow, map_natCast, map_neg]
  ring

theorem antiPsi_val (w : ℂ) : (antiPsi n w).val =
    binaryLin (discP w) (-discQ w) * binaryLin (1 - w) (-Complex.I * (1 + w)) ^ n := by
  rw [binaryLin_disc_anti, binaryLin_frame_anti, add_pow, Finset.mul_sum, antiPsi,
    Submodule.coe_sum, ← Fin.sum_univ_eq_sum_range (fun m =>
      (C (1 - 3 * w ^ 2) * binaryNegativeCoordinate +
        C (3 * w - w ^ 3) * binaryPositiveCoordinate) *
      (binaryNegativeCoordinate ^ m * (C (-w) * binaryPositiveCoordinate) ^ (n - m) *
        (n.choose m : Binary.Poly)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm := m.isLt
  rw [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    binaryWeightBasis_coe, binaryWeightBasis_coe]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_rev, smul_eq_C_mul]
  rw [show n + 1 - ((m : ℕ) + 1) = n - m by omega, show n + 1 - (n - (m : ℕ)) = m + 1 by omega,
    show n + 1 - (n - (m : ℕ) + 1) = m by omega]
  simp only [mul_pow, map_mul, map_pow, map_natCast, map_neg]
  ring

theorem holPsi_zero : holPsi n 0 = binaryWeightBasis (n + 1) (Fin.last (n + 1)) := by
  rw [holPsi, Finset.sum_eq_single (Fin.last n)]
  · simp [Fin.succ_last]
  · intro m _ hm
    have : n - (m : ℕ) ≠ 0 := by
      have := Fin.val_lt_last hm
      omega
    simp [zero_pow this]
  · simp

theorem antiPsi_zero : antiPsi n 0 = binaryWeightBasis (n + 1) 0 := by
  rw [antiPsi, Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro m _ hm
    have : n - (m : ℕ) ≠ 0 := by
      have := Fin.val_lt_last hm
      omega
    simp [zero_pow this]
  · simp

/-! ### The closed form -/

theorem C_combine (X μ ν Y : ℂ) (B₁ B₂ : Binary.Poly) (h : X * μ * ν ^ n = Y) :
    C X * (C μ * B₁) * (C ν * B₂) ^ n = C Y * (B₁ * B₂ ^ n) := by
  rw [← h, mul_pow, ← map_pow]
  simp only [map_mul]
  ring

theorem sqrt_gsRadius_complex_ne_zero (u : ℝ × ℝ) : (Real.sqrt (gsRadius u) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'

/-- **The closed form of the lower radical coordinate of the mixed derivative vector.** -/
theorem lowerRadicalCoordinate_edgeMixedVector_closed {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    lowerRadicalCoordinate n (fun i => edgeMixedVector n F u i h) =
      (edgeConstant n * ((gsRadius u : ℂ) ^ (n + 3))⁻¹ * discForm n F h (holDisc u)) •
          holPsi n (holDisc u) +
        (edgeConstant n * ((gsRadius u : ℂ) ^ (n + 3))⁻¹ *
          discForm n F (h * atInfinity UpperHalfPlane.J) (antiDisc u)) •
          antiPsi n (antiDisc u) := by
  apply Subtype.ext
  rw [lowerRadicalCoordinate_edgeMixedVector_val, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_smul, holPsi_val, antiPsi_val, smul_eq_C_mul, smul_eq_C_mul,
    binaryLin_holCoeff, binaryLin_antiCoeff, binaryLin_holFrame, binaryLin_antiFrame,
    transferScale_eq, det_gsOrthMatrix, eichlerData_movedPoint hF, eichlerData_movedPoint_J hF,
    discForm_holDisc, discForm_antiDisc, Complex.ofReal_div]
  have hq := sqrt_gsRadius_complex_ne_zero u
  have ha := gsAlpha_complex_ne_zero u
  have hR := gsRadius_complex_ne_zero u
  rw [C_combine _ _ _ _ _ _ (edge_scalar_identity _ _ _ (holE u) _ hq ha hR),
    C_combine _ _ _ _ _ _ (edge_scalar_identity _ _ _ (antiE u) _ hq ha hR)]

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
