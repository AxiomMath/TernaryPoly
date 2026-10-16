module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitPointwise

@[expose] public section


/-!
# The lower radical coordinate of the mixed derivative vector

The mixed derivative vector of the edge section is a combination of powers of linear forms: the
derivative of the pointwise normal form at `i` is `½ F_{h'}(i) ż P(i) + ½ refl(ż) J ⋆ (F(i) P(i))`,
`dμ(ξ)` sends `c L^{n+1}` to `(n + 1) c (ξ · ∇L) L^n`, the coefficient action of `k⁻¹` composes
linear forms with `k`, and the lower radical coordinate restricts `X₁ v₀ - X₀ v₁` to `X₂ = 0`.
The result is the sum of a holomorphic and an antiholomorphic term, each a scalar times a linear
form times the `n`-th power of the linear form `(L∘k)|_{X₂ = 0}`, `L = X₀ ∓ i X₁`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### Linear forms -/

/-- The binary linear form `a X₀ + b X₁`. -/
def binaryLin (a b : ℂ) : Binary.Poly := C a * X 0 + C b * X 1

/-- The ternary linear form `a X₀ + b X₁`. -/
def ternaryLin (a b : ℂ) : Poly := C a * X 0 + C b * X 1

theorem binaryPolynomialLift_binaryLin (a b : ℂ) :
    binaryPolynomialLift (binaryLin a b) = ternaryLin a b := by
  simp [binaryLin, ternaryLin, binaryPolynomialLift]

theorem pderiv_zero_ternaryLin_pow (a b : ℂ) (m : ℕ) :
    pderiv (0 : Fin 3) (ternaryLin a b ^ (m + 1)) = C (((m : ℂ) + 1) * a) * ternaryLin a b ^ m := by
  rw [Derivation.leibniz_pow, Nat.add_sub_cancel]
  simp [ternaryLin, pderiv_X, nsmul_eq_mul, smul_eq_mul]
  ring

theorem pderiv_one_ternaryLin_pow (a b : ℂ) (m : ℕ) :
    pderiv (1 : Fin 3) (ternaryLin a b ^ (m + 1)) = C (((m : ℂ) + 1) * b) * ternaryLin a b ^ m := by
  rw [Derivation.leibniz_pow, Nat.add_sub_cancel]
  simp [ternaryLin, pderiv_X, nsmul_eq_mul, smul_eq_mul]
  ring

/-- **`dμ(ξ)` on a power of a linear form.** -/
theorem muDeriv_val_of_eq (ξ : Fin 2 → ℝ) (P : Binary.HomogeneousPoly (n + 1)) {c a b : ℂ}
    (hP : P.val = C c * binaryLin a b ^ (n + 1)) :
    (muDeriv n ξ P).val =
      C (c * ((n : ℂ) + 1) * ((ξ 0 : ℂ) * a + (ξ 1 : ℂ) * b)) * ternaryLin a b ^ n := by
  have inner : ((upperRadicalDeriv (n + 1) ξ) (binaryHomogeneousLift (n + 1) P)).val =
      X 2 * -(C (ξ 0 : ℂ) * pderiv (0 : Fin 3) (binaryPolynomialLift P.val) +
        C (ξ 1 : ℂ) * pderiv (1 : Fin 3) (binaryPolynomialLift P.val)) := by
    change (ξ 0 : ℂ) • ((-1 : ℂ) • (X 2 * pderiv (0 : Fin 3) (binaryPolynomialLift P.val))) +
      (ξ 1 : ℂ) • ((-1 : ℂ) • (X 2 * pderiv (1 : Fin 3) (binaryPolynomialLift P.val))) = _
    simp only [smul_eq_C_mul]
    simp only [map_neg, map_one]
    ring
  have value : (muDeriv n ξ P).val =
      C (ξ 0 : ℂ) * pderiv (0 : Fin 3) (binaryPolynomialLift P.val) +
        C (ξ 1 : ℂ) * pderiv (1 : Fin 3) (binaryPolynomialLift P.val) := by
    change -((homogeneousLastDivide n) ((upperRadicalDeriv (n + 1) ξ)
      (binaryHomogeneousLift (n + 1) P))).val = _
    change -(((upperRadicalDeriv (n + 1) ξ) (binaryHomogeneousLift (n + 1) P)).val.divMonomial
      (Finsupp.single 2 1)) = _
    rw [inner, X_mul_divMonomial, neg_neg]
  have constant : binaryPolynomialLift (C c) = C c := rename_C _ _
  rw [value, hP, map_mul, constant, map_pow, binaryPolynomialLift_binaryLin,
    Derivation.leibniz, Derivation.leibniz, pderiv_zero_ternaryLin_pow, pderiv_one_ternaryLin_pow]
  simp only [pderiv_C, smul_eq_mul, map_mul, map_add]
  ring

/-! ### The coefficient action, substitution and restriction -/

theorem realCoefficientComponent_val (g : RealGL3) (Q : HomogeneousPoly n) :
    (realCoefficientComponent n trivialCharacter g Q).val =
      C (((g.val.det : ℝ) : ℂ)⁻¹) *
        substitute ((g⁻¹ : RealGL3).val.map (algebraMap ℝ ℂ)) Q.val := by
  rw [realCoefficientComponent_trivial, homogeneousAction_coe, action_apply, smul_eq_C_mul]
  congr 2
  change ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g).val.det) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg_one]
  congr 1
  exact ((algebraMap ℝ ℂ).map_det g.val).symm

theorem realCoefficientComponent_gsOrth_inv_val (u : ℝ × ℝ) (Q : HomogeneousPoly n) :
    (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ Q).val =
      C (((gsOrthMatrix u).det : ℝ) : ℂ) *
        substitute ((gsOrthMatrix u).map (algebraMap ℝ ℂ)) Q.val := by
  rw [realCoefficientComponent_val, inv_inv, gsOrth_val]
  congr 2
  have unit : ((gsOrth u)⁻¹ : RealGL3).val.det * (gsOrthMatrix u).det = 1 := by
    rw [← Matrix.det_mul, ← gsOrth_val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  rw [eq_inv_of_mul_eq_one_left unit, Complex.ofReal_inv, inv_inv]

theorem substitute_ternaryLin (M : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) :
    substitute M (ternaryLin a b) = C (a * M 0 0 + b * M 1 0) * X 0 +
      C (a * M 0 1 + b * M 1 1) * X 1 + C (a * M 0 2 + b * M 1 2) * X 2 := by
  simp only [ternaryLin, map_add, map_mul, substitute_X, linearForm, Fin.sum_univ_three]
  simp only [substitute, bind₁_C_right]
  ring

theorem restrict_substitute_ternaryLin (M : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) :
    binaryPolynomialRestrict (substitute M (ternaryLin a b)) =
      binaryLin (a * M 0 0 + b * M 1 0) (a * M 0 1 + b * M 1 1) := by
  rw [substitute_ternaryLin]
  simp [binaryLin, binaryPolynomialRestrict]

/-! ### The derivative of the normal form at `i` -/

theorem normPower_det_J (z : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity UpperHalfPlane.J)) z = 1 :=
  normPower_det_unimodular (by rw [det_upperJ, abs_neg, abs_one]) z

/-- **The derivative of the pointwise normal form at `i`**:
`N'(dw) = ½ F_{h}(i) dw P(i) + ½ refl(dw) F_{hJ}(i) J ⋆ P(i)`. -/
theorem normalDerivVector_eq (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (dw : ℂ) :
    normalDerivVector n F h dw =
      (2⁻¹ * (F h Complex.I * dw)) • binaryPointPower (n + 1) Complex.I +
        (2⁻¹ * (binaryComplexReflection dw * F (h * atInfinity UpperHalfPlane.J) Complex.I)) •
          binaryCoefficient n UpperHalfPlane.J (binaryPointPower (n + 1) Complex.I) := by
  have expand : binaryCoefficient n UpperHalfPlane.J (binaryPointPower (n + 1) Complex.I) =
      ∑ x, (binaryWeightBasis (n + 1)).repr (binaryPointPower (n + 1) Complex.I) x •
        binaryCoefficient n UpperHalfPlane.J (binaryWeightBasis (n + 1) x) := by
    conv_lhs => rw [← (binaryWeightBasis (n + 1)).sum_repr (binaryPointPower (n + 1) Complex.I)]
    simp only [map_sum, map_smul]
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  rw [normalDerivVector, Module.Basis.repr_sum_self, eichlerPointNormalDeriv_apply, expand]
  simp only [map_add, map_smul, map_sum, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul, eichlerKernel, eichlerReflectionCoeff,
    normPower_det_J, one_mul, binaryComplexReflection_basepoint, Module.Basis.coord_apply]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun x _ => by ring

/-! ### The mixed derivative vector -/

theorem binaryPointPower_I_val :
    (binaryPointPower (n + 1) Complex.I).val = C 1 * binaryLin 1 (-Complex.I) ^ (n + 1) := by
  simp [binaryPointPower, binaryLin, sub_eq_add_neg]

theorem upperJ_inv : (UpperHalfPlane.J : BinaryRealGL)⁻¹ = UpperHalfPlane.J :=
  inv_eq_of_mul_eq_one_left upperJ_mul_self

theorem binaryCoefficient_J_binaryPointPower_I_val :
    (binaryCoefficient n UpperHalfPlane.J (binaryPointPower (n + 1) Complex.I)).val =
      C (-1) * binaryLin (-1) (-Complex.I) ^ (n + 1) := by
  rw [binaryCoefficient_val_eq, det_upperJ, ← map_inv, upperJ_inv, smul_eq_C_mul]
  have matrix : ((GeneralLinearGroup.map (algebraMap ℝ ℂ)) UpperHalfPlane.J).val =
      !![-1, 0; 0, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [UpperHalfPlane.J, GeneralLinearGroup.map_apply]
  rw [matrix]
  simp [binaryPointPower, binaryLin, Binary.substitute_X, Binary.linearForm, Fin.sum_univ_two,
    sub_eq_add_neg]

theorem smul_val_of_eq {P : Binary.HomogeneousPoly (n + 1)} {c' : ℂ} {Q : Binary.Poly}
    (hP : P.val = C c' * Q) (c : ℂ) : (c • P).val = C (c * c') * Q := by
  rw [Submodule.coe_smul, hP, smul_eq_C_mul, map_mul, mul_assoc]

theorem muDeriv_normalDerivVector_val (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (dw : ℂ)
    (ξ : Fin 2 → ℝ) :
    (muDeriv n ξ (normalDerivVector n F h dw)).val =
      C (2⁻¹ * (F h Complex.I * dw) * ((n : ℂ) + 1) * ((ξ 0 : ℂ) - Complex.I * ξ 1)) *
          ternaryLin 1 (-Complex.I) ^ n +
        C (2⁻¹ * (binaryComplexReflection dw * F (h * atInfinity UpperHalfPlane.J) Complex.I) *
          ((n : ℂ) + 1) * ((ξ 0 : ℂ) + Complex.I * ξ 1)) * ternaryLin (-1) (-Complex.I) ^ n := by
  rw [normalDerivVector_eq, map_add, Submodule.coe_add,
    muDeriv_val_of_eq ξ _ (smul_val_of_eq binaryPointPower_I_val _),
    muDeriv_val_of_eq ξ _ (smul_val_of_eq binaryCoefficient_J_binaryPointPower_I_val _)]
  congr 3 <;> ring

/-- The holomorphic coefficient `ż(H) (ξ(Rᵢ) · (1, -i)) - ż(Rᵢ) (ξ(H) · (1, -i))`. -/
def holCoeff (u : ℝ × ℝ) (i : Fin 2) : ℂ :=
  pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) *
      ((radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i) 0 : ℂ) -
        Complex.I * radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i) 1) -
    pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i) *
      ((radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 0 : ℂ) -
        Complex.I * radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 1)

/-- The antiholomorphic coefficient
`refl(ż(H)) (ξ(Rᵢ) · (1, i)) - refl(ż(Rᵢ)) (ξ(H) · (1, i))`. -/
def antiCoeff (u : ℝ × ℝ) (i : Fin 2) : ℂ :=
  binaryComplexReflection (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity)) *
      ((radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i) 0 : ℂ) +
        Complex.I * radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i) 1) -
    binaryComplexReflection (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)) *
      ((radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 0 : ℂ) +
        Complex.I * radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 1)

/-- The complex matrix of the orthogonal Iwasawa factor. -/
def complexOrth (u : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℂ := (gsOrthMatrix u).map (algebraMap ℝ ℂ)

theorem edgeMixedVector_val (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (i : Fin 2)
    (h : BinaryAdelicGL) :
    (edgeMixedVector n F u i h).val =
      C (transferScale n u * ((gsOrthMatrix u).det : ℂ)) * substitute (complexOrth u)
        (C (2⁻¹ * F (movedPoint u h) Complex.I * ((n : ℂ) + 1) * holCoeff u i) *
            ternaryLin 1 (-Complex.I) ^ n +
          C (2⁻¹ * F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I * ((n : ℂ) + 1) *
            antiCoeff u i) * ternaryLin (-1) (-Complex.I) ^ n) := by
  rw [edgeMixedVector, LinearMap.smul_apply, Submodule.coe_smul,
    realCoefficientComponent_gsOrth_inv_val, Submodule.coe_sub, muDeriv_normalDerivVector_val,
    muDeriv_normalDerivVector_val, smul_eq_C_mul, ← mul_assoc, ← map_mul]
  congr 2
  simp only [holCoeff, antiCoeff, map_sub, map_add, map_mul]
  ring

theorem substitute_C' (M : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ) : substitute M (C c) = C c := by
  simp [substitute]

theorem binaryPolynomialRestrict_C' (c : ℂ) : binaryPolynomialRestrict (C c) = C c := by
  simp [binaryPolynomialRestrict]

/-- **The lower radical coordinate of the mixed derivative vector**: a holomorphic term
`TS det k (n+1)/2 F_{h'}(i) (c₀ X₁ - c₁ X₀) ((L₊ ∘ k)|_{X₂=0})ⁿ` plus the antiholomorphic term
with `F_{h'J}(i)` and `L = -X₀ - i X₁`. -/
theorem lowerRadicalCoordinate_edgeMixedVector_val (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ)
    (h : BinaryAdelicGL) :
    (lowerRadicalCoordinate n (fun i => edgeMixedVector n F u i h)).val =
      C (transferScale n u * ((gsOrthMatrix u).det : ℂ) * 2⁻¹ * ((n : ℂ) + 1) *
          F (movedPoint u h) Complex.I) * binaryLin (-holCoeff u 1) (holCoeff u 0) *
        binaryLin (complexOrth u 0 0 - Complex.I * complexOrth u 1 0)
          (complexOrth u 0 1 - Complex.I * complexOrth u 1 1) ^ n +
      C (transferScale n u * ((gsOrthMatrix u).det : ℂ) * 2⁻¹ * ((n : ℂ) + 1) *
          F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I) *
        binaryLin (-antiCoeff u 1) (antiCoeff u 0) *
        binaryLin (-complexOrth u 0 0 - Complex.I * complexOrth u 1 0)
          (-complexOrth u 0 1 - Complex.I * complexOrth u 1 1) ^ n := by
  change binaryPolynomialRestrict (lowerRadicalContraction (edgeMixedVector n F u 0 h).val
    (edgeMixedVector n F u 1 h).val) = _
  rw [edgeMixedVector_val, edgeMixedVector_val, lowerRadicalContraction]
  simp only [map_sub, map_mul, map_add, map_pow, substitute_C', binaryPolynomialRestrict_C',
    restrict_substitute_ternaryLin, binaryPolynomialRestrict_X]
  have first : binaryLin (1 * complexOrth u 0 0 + -Complex.I * complexOrth u 1 0)
      (1 * complexOrth u 0 1 + -Complex.I * complexOrth u 1 1) =
      binaryLin (complexOrth u 0 0 - Complex.I * complexOrth u 1 0)
        (complexOrth u 0 1 - Complex.I * complexOrth u 1 1) := by
    congr 1 <;> ring
  have second : binaryLin (-1 * complexOrth u 0 0 + -Complex.I * complexOrth u 1 0)
      (-1 * complexOrth u 0 1 + -Complex.I * complexOrth u 1 1) =
      binaryLin (-complexOrth u 0 0 - Complex.I * complexOrth u 1 0)
        (-complexOrth u 0 1 - Complex.I * complexOrth u 1 1) := by
    congr 1 <;> ring
  rw [first, second]
  simp only [binaryLin, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]
  ring

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
