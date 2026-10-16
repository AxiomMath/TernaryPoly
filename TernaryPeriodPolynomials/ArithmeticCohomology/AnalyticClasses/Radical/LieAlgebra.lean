module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.LiePointwise

@[expose] public section


/-!
# The coinvariant part of the mixed radical derivative

The `X₂ⁿ`-coefficient of the antisymmetrised mixed radical derivative of the transfer of the
Eichler normal form is explicit. Write `u = (s, t)`, `α = √(1 + s²)`, `R = √(1 + s² + t²)` and
`ζ = (s R - i t) / (R α)`. The coefficient action of `k(u)⁻¹` sends `X₂ⁿ`-coefficients of powers of
linear forms to powers of their `X₂`-coefficients, and the holomorphic Lie coefficient
`ż(R₀) ξ(R₁)·(1, -i) - ż(R₁) ξ(R₀)·(1, -i)` equals `ζ³`. After transporting the scalar form from
the moved point to the Levi point `z(u)` of the good-line vertex, the obstruction density is
`(n + 1) / 2 · ((-1)^{n+1} S_{F_h}(s, t) + S_{F_{hJ}}(s, -t))`, where
`S_f(u) = α^{-(n+3)} ζ^{n+3} f(z(u))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace RadicalLie

open EdgeExplicit

/-! ### The `X₂ⁿ`-coefficient of a power of a linear form -/

theorem coeff_single_two_mul_linear (g : MvPolynomial (Fin 3) ℂ) (a b c : ℂ) (m : ℕ) :
    (g * (C a * X 0 + C b * X 1 + C c * X 2)).coeff (Finsupp.single 2 (m + 1)) =
      c * g.coeff (Finsupp.single 2 m) := by
  have away (i : Fin 3) (hi : i ≠ 2) : (g * X i).coeff (Finsupp.single 2 (m + 1)) = 0 := by
    rw [coeff_mul_X', ite_eq_right]
    simp [Finsupp.mem_support_iff, hi.symm]
  have last : (g * X 2).coeff (Finsupp.single 2 (m + 1)) = g.coeff (Finsupp.single 2 m) := by
    rw [coeff_mul_X', ite_eq_left (by simp)]
    congr 1
    ext k
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  simp only [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [mul_left_comm g, mul_left_comm g, mul_left_comm g, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    away 0 (by decide), away 1 (by decide), last]
  ring

/-- **The `X₂ᵐ`-coefficient of the `m`-th power of a linear form is the `m`-th power of its
`X₂`-coefficient.** -/
theorem coeff_single_two_linear_pow (a b c : ℂ) (m : ℕ) :
    ((C a * X 0 + C b * X 1 + C c * X 2 : MvPolynomial (Fin 3) ℂ) ^ m).coeff (Finsupp.single 2 m) =
      c ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, coeff_single_two_mul_linear, ih, pow_succ, mul_comm]

/-! ### The coinvariant part of the moved vector -/

/-- The `X₂`-coefficient `k₀₂ - i k₁₂` of `(X₀ - i X₁) ∘ k(u)`. -/
def holTop (u : ℝ × ℝ) : ℂ := (gsOrthMatrix u 0 2 : ℂ) - Complex.I * (gsOrthMatrix u 1 2 : ℂ)

/-- The `X₂`-coefficient `-k₀₂ - i k₁₂` of `(-X₀ - i X₁) ∘ k(u)`. -/
def antiTop (u : ℝ × ℝ) : ℂ := -(gsOrthMatrix u 0 2 : ℂ) - Complex.I * (gsOrthMatrix u 1 2 : ℂ)

/-- **The coinvariant coordinate of `TS(u) · k⁻¹ ⋆ dμ(ξ) N'(dw)`.** -/
theorem topCoefficient_moved (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (ξ : Fin 2 → ℝ)
    (h : BinaryAdelicGL) (dw : ℂ) :
    movedTest u (topCoefficient n) (muDeriv n ξ (normalDerivVector n F h dw)) =
      transferScale n u * ((gsOrthMatrix u).det : ℂ) *
        (2⁻¹ * (F h Complex.I * dw) * ((n : ℂ) + 1) * ((ξ 0 : ℂ) - Complex.I * ξ 1) *
            holTop u ^ n +
          2⁻¹ * (binaryComplexReflection dw * F (h * atInfinity UpperHalfPlane.J) Complex.I) *
            ((n : ℂ) + 1) * ((ξ 0 : ℂ) + Complex.I * ξ 1) * antiTop u ^ n) := by
  change ((transferScale n u • realCoefficientComponent n
    trivialCharacter (gsOrth u)⁻¹ (muDeriv n ξ (normalDerivVector n F h dw))).val).coeff (Finsupp.single 2 n) = _
  have power (M : Matrix (Fin 3) (Fin 3) ℂ) (c a b : ℂ) :
      substitute M (C c * ternaryLin a b ^ n) = C c * (C (a * M 0 0 + b * M 1 0) * X 0 +
        C (a * M 0 1 + b * M 1 1) * X 1 + C (a * M 0 2 + b * M 1 2) * X 2) ^ n := by
    rw [map_mul, map_pow, substitute_C', substitute_ternaryLin]
  rw [Submodule.coe_smul, realCoefficientComponent_gsOrth_inv_val, muDeriv_normalDerivVector_val,
    smul_eq_C_mul, map_add, power, power]
  simp only [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_single_two_linear_pow]
  simp only [holTop, antiTop, Matrix.map_apply, Complex.coe_algebraMap]
  ring

/-! ### The obstruction density -/

/-- The radical velocity `ξ(k Rⱼ)` at the orthogonal Iwasawa factor. -/
def radicalVelocity (u : ℝ × ℝ) (j : Fin 2) : Fin 2 → ℝ :=
  radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity j)

/-- The Levi velocity `ż(k Rᵢ)` at the orthogonal Iwasawa factor. -/
def pointVelocity (u : ℝ × ℝ) (i : Fin 2) : ℂ :=
  pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)

/-- The holomorphic Lie coefficient `ż(R₀) ξ(R₁)·(1, -i) - ż(R₁) ξ(R₀)·(1, -i)`. -/
def holLie (u : ℝ × ℝ) : ℂ :=
  pointVelocity u 0 * ((radicalVelocity u 1 0 : ℂ) - Complex.I * radicalVelocity u 1 1) -
    pointVelocity u 1 * ((radicalVelocity u 0 0 : ℂ) - Complex.I * radicalVelocity u 0 1)

/-- The antiholomorphic Lie coefficient
`refl(ż(R₀)) ξ(R₁)·(1, i) - refl(ż(R₁)) ξ(R₀)·(1, i)`. -/
def antiLie (u : ℝ × ℝ) : ℂ :=
  binaryComplexReflection (pointVelocity u 0) *
      ((radicalVelocity u 1 0 : ℂ) + Complex.I * radicalVelocity u 1 1) -
    binaryComplexReflection (pointVelocity u 1) *
      ((radicalVelocity u 0 0 : ℂ) + Complex.I * radicalVelocity u 0 1)

variable (F : BinaryAdelicGL → ℂ → ℂ)

theorem radicalObstruction_eichlerNormal_eq
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (u : ℝ × ℝ)
    (h : BinaryAdelicGL) :
    radicalObstruction (eichlerNormal n F) u h =
      transferScale n u * ((gsOrthMatrix u).det : ℂ) * 2⁻¹ * ((n : ℂ) + 1) *
        (F (movedPoint u h) Complex.I * holLie u * holTop u ^ n +
          F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I * antiLie u *
            antiTop u ^ n) := by
  rw [radicalObstruction, radicalMixed_eichlerNormal F holomorphic,
    radicalMixed_eichlerNormal F holomorphic, topCoefficient_moved, topCoefficient_moved]
  simp only [holLie, antiLie, radicalVelocity, pointVelocity]
  ring

/-! ### Closed forms -/

/-- The unit `ζ(u) = (s R - i t) / (R α)`. -/
def radialUnit (u : ℝ × ℝ) : ℂ :=
  ((u.1 : ℂ) * (gsRadius u : ℂ) - Complex.I * (u.2 : ℂ)) / ((gsRadius u : ℂ) * (gsAlpha u : ℂ))

theorem holLie_identity_generic (s t a R : ℂ) (ha : a ≠ 0) (hR : R ≠ 0)
    (ha2 : a ^ 2 = 1 + s ^ 2) (hR2 : R ^ 2 = 1 + s ^ 2 + t ^ 2) :
    (-s / R + Complex.I / 2 * (2 * t / R ^ 2)) *
        ((1 - s ^ 2) / (R * a) - Complex.I * (-2 * s * t / (R ^ 2 * a))) -
      (t * (s ^ 2 - 1) / (R * a ^ 2) + Complex.I / 2 * (-2 * s * (s ^ 2 + 2 * t ^ 2 + 1) /
          (R ^ 2 * a ^ 2))) *
        (-(s * t) / (R * a) - Complex.I * ((s ^ 2 - t ^ 2 + 1) / (R ^ 2 * a))) =
      ((s * R - Complex.I * t) / (R * a)) ^ 3 := by
  have numerator : a ^ 2 * (-s * R + Complex.I * t) * ((1 - s ^ 2) * R + 2 * Complex.I * s * t) -
      (t * (s ^ 2 - 1) * R - Complex.I * s * (s ^ 2 + 2 * t ^ 2 + 1)) *
        (-s * t * R - Complex.I * (s ^ 2 - t ^ 2 + 1)) = R * (s * R - Complex.I * t) ^ 3 := by
    linear_combination (-s * (3 * Complex.I ^ 2 * t ^ 2 - 3 * Complex.I * R * s * t +
      R ^ 2 * s ^ 2 - a ^ 2 * s ^ 2 + a ^ 2 + s ^ 4 + s ^ 2 + t ^ 2)) * hR2 +
      (2 * Complex.I ^ 2 * s * t ^ 2 - 3 * Complex.I * R * s ^ 2 * t + Complex.I * R * t + s ^ 5 +
        s ^ 3 * t ^ 2 - s * t ^ 2 - s) * ha2 +
      (Complex.I * R * t ^ 3 - s ^ 5 - 2 * s ^ 3 * t ^ 2 - 2 * s ^ 3 - s * t ^ 4 - 2 * s * t ^ 2 -
        s) * Complex.I_sq
  have left : (-s / R + Complex.I / 2 * (2 * t / R ^ 2)) *
        ((1 - s ^ 2) / (R * a) - Complex.I * (-2 * s * t / (R ^ 2 * a))) -
      (t * (s ^ 2 - 1) / (R * a ^ 2) + Complex.I / 2 * (-2 * s * (s ^ 2 + 2 * t ^ 2 + 1) /
          (R ^ 2 * a ^ 2))) *
        (-(s * t) / (R * a) - Complex.I * ((s ^ 2 - t ^ 2 + 1) / (R ^ 2 * a))) =
      (a ^ 2 * (-s * R + Complex.I * t) * ((1 - s ^ 2) * R + 2 * Complex.I * s * t) -
        (t * (s ^ 2 - 1) * R - Complex.I * s * (s ^ 2 + 2 * t ^ 2 + 1)) *
          (-s * t * R - Complex.I * (s ^ 2 - t ^ 2 + 1))) / (R ^ 4 * a ^ 3) := by
    field_simp
    ring
  rw [left, numerator]
  field_simp

/-- **The holomorphic Lie coefficient is `ζ³`.** -/
theorem holLie_eq (u : ℝ × ℝ) : holLie u = radialUnit u ^ 3 := by
  have key := holLie_identity_generic (u.1 : ℂ) (u.2 : ℂ) _ _
    (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u) (gsAlpha_complex_sq u)
    (gsRadius_complex_sq u)
  simp only [holLie, radicalVelocity, pointVelocity, radicalDeriv_eq_gram, pointDeriv_eq_gram,
    Fin.castSucc_zero, Fin.castSucc_one, gramAxisZero_02, gramAxisZero_12, gramAxisZero_01,
    gramAxisZero_diag, gramAxisOne_02, gramAxisOne_12, gramAxisOne_01, gramAxisOne_diag]
  push_cast
  rw [radialUnit]
  linear_combination key

theorem binaryComplexReflection_eq_neg_conj (z : ℂ) :
    binaryComplexReflection z = -(starRingEnd ℂ) z := rfl

/-- **The antiholomorphic Lie coefficient is `-conj(ζ)³`.** -/
theorem antiLie_eq (u : ℝ × ℝ) : antiLie u = -((starRingEnd ℂ) (radialUnit u)) ^ 3 := by
  have conjugate : antiLie u = -(starRingEnd ℂ) (holLie u) := by
    simp only [antiLie, holLie, binaryComplexReflection_eq_neg_conj, map_sub, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [conjugate, holLie_eq, map_pow]

theorem holTop_eq (u : ℝ × ℝ) : holTop u = -radialUnit u := by
  have ha := gsAlpha_complex_ne_zero u
  have hr := gsRadius_complex_ne_zero u
  rw [holTop, gsOrthMatrix_02, gsOrthMatrix_12, radialUnit]
  push_cast
  field_simp
  ring

theorem antiTop_eq (u : ℝ × ℝ) : antiTop u = (starRingEnd ℂ) (radialUnit u) := by
  have ha := gsAlpha_complex_ne_zero u
  have hr := gsRadius_complex_ne_zero u
  rw [antiTop, gsOrthMatrix_02, gsOrthMatrix_12, radialUnit]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  field_simp

/-! ### The obstruction density in terms of the Levi point -/

/-- **The shape of the obstruction density**: `S_f(u) = α^{-(n+3)} ζ^{n+3} f(z(u))`. -/
def obstructionShape (n : ℕ) (f : ℂ → ℂ) (u : ℝ × ℝ) : ℂ :=
  ((gsAlpha u : ℂ) ^ (n + 3))⁻¹ * radialUnit u ^ (n + 3) * f (goodPoint u)

/-- The reflection `(s, t) ↦ (s, -t)` of the good-line coordinate. -/
def reflectCoordinate (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

theorem gsAlpha_reflect (u : ℝ × ℝ) : gsAlpha (reflectCoordinate u) = gsAlpha u := rfl

theorem gsRadius_reflect (u : ℝ × ℝ) : gsRadius (reflectCoordinate u) = gsRadius u := by
  simp [gsRadius, reflectCoordinate]

theorem radialUnit_reflect (u : ℝ × ℝ) :
    radialUnit (reflectCoordinate u) = (starRingEnd ℂ) (radialUnit u) := by
  rw [radialUnit, radialUnit, gsRadius_reflect, gsAlpha_reflect]
  simp only [reflectCoordinate, map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem goodPoint_reflect (u : ℝ × ℝ) :
    goodPoint (reflectCoordinate u) = binaryComplexReflection (goodPoint u) := by
  rw [goodPoint, goodPoint, gsRadius_reflect, gsAlpha_reflect, binaryComplexReflection_eq_neg_conj]
  simp only [reflectCoordinate, map_div₀, map_sub, map_mul, map_pow, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring

theorem obstructionShape_reflect (f : ℂ → ℂ) (u : ℝ × ℝ) :
    obstructionShape n f (reflectCoordinate u) =
      ((gsAlpha u : ℂ) ^ (n + 3))⁻¹ * (starRingEnd ℂ) (radialUnit u) ^ (n + 3) *
        f (binaryComplexReflection (goodPoint u)) := by
  rw [obstructionShape, gsAlpha_reflect, radialUnit_reflect, goodPoint_reflect]

theorem transferScale_mul_scale (u : ℝ × ℝ) :
    transferScale n u * (((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3))⁻¹ =
      ((gsAlpha u : ℂ) ^ (n + 3))⁻¹ := by
  have ha := gsAlpha_complex_ne_zero u
  have hq : (Real.sqrt (gsRadius u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
  rw [transferScale_eq, Complex.ofReal_div, div_pow, inv_div]
  field_simp

/-- **The obstruction density of the Eichler normal form**:
`(n + 1) / 2 · ((-1)^{n+1} S_{F_h}(s, t) + S_{F_{hJ}}(s, -t))`. -/
theorem radicalObstruction_eichlerNormal (hF : EichlerData n F) (u : ℝ × ℝ)
    (h : BinaryAdelicGL) :
    radicalObstruction (eichlerNormal n F) u h =
      2⁻¹ * ((n : ℂ) + 1) * ((-1) ^ (n + 1) * obstructionShape n (F h) u +
        obstructionShape n (F (h * atInfinity UpperHalfPlane.J)) (reflectCoordinate u)) := by
  rw [radicalObstruction_eichlerNormal_eq F hF.holomorphic, eichlerData_movedPoint hF,
    eichlerData_movedPoint_J hF, det_gsOrthMatrix, holLie_eq, antiLie_eq, holTop_eq, antiTop_eq,
    obstructionShape_reflect, obstructionShape]
  have scale := transferScale_mul_scale (n := n) u
  simp only [Complex.ofReal_neg, Complex.ofReal_one]
  rw [neg_pow (radialUnit u), pow_succ (-1 : ℂ) n, pow_add (radialUnit u),
    pow_add ((starRingEnd ℂ) (radialUnit u))]
  linear_combination (2⁻¹ * ((n : ℂ) + 1) * (-(-1) ^ n * radialUnit u ^ n * radialUnit u ^ 3 *
    F h (goodPoint u) + (starRingEnd ℂ) (radialUnit u) ^ n *
      (starRingEnd ℂ) (radialUnit u) ^ 3 *
      F (h * atInfinity UpperHalfPlane.J) (binaryComplexReflection (goodPoint u)))) * scale

end RadicalLie

end TernaryPeriodPolynomials.AnalyticClasses
