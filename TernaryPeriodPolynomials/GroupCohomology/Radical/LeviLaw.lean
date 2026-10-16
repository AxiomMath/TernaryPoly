module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BinaryCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.IntegralNormalization

@[expose] public section


/-!
# the law `diag(t, L): J(v) ↦ t⁻² J(L⁻¹ v)` for the radical coordinate

For the bad line, `J(b) = Z α − Y β` (`radicalPairCoordinate`, `eq:radical-coordinate`) is the Bernoulli coordinate of a one-cocycle `b` of the line radical
`N_L = ⟨U₁₂, U₁₃⟩ ≅ ℤ²` with values in `E_{n,1}` (the coefficients `rationalCoefficientComponent n trivialCharacter`, `Sym^n ⊗ det⁻¹`).  Previously the library had the
covariance only for the concrete matrices `diag(1, A₀)`, `diag(1, R₀)`, `diag(1, B₀)` and an upper translation (`radicalPairCoordinate_binaryR`, ...).  Here:

* `leviInt t L`, `leviGL t L`: the Levi element `diag(t, L)` of `GL₃(ℤ)` and its image in `GL₃(ℚ)`, `t = ±1`, `L ∈ GL₂(ℤ)` arbitrary
  (`leviGL_mem_rationalLevel`: it lies in `K†` when `L ∈ Γ₂`);
* `leviGL_conjugate`: `g⁻¹ U(r) g = U(t r L)`;
* `radicalPair_leviLaw`: for every one-cocycle `b` of `N_L` (the family `values : ℤ × ℤ → E`) the coordinate of the transported cocycle
  `(g·b)(u) = g b(g⁻¹ u g)` is the substitution of the coordinate of `b`;
* `radicalPair_leviLaw_binary`: in the paper's form: `J(g·b)(v) = t⁻² J(b)(L⁻¹ v)`, where `J(b)` does not involve `X` (`radicalPair_pderiv_zero`);
* `radicalPair_lineSign`: the independent integral line sign acts trivially.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw

open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

/-- The Levi element `diag(t, L)` of `GL₃(ℤ)`. -/
def leviInt (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) : IntegralGL3 :=
  GeneralLinearGroup.mk'' !![t.val, 0, 0; 0, L.val 0 0, L.val 0 1; 0, L.val 1 0, L.val 1 1] (by
    have h : (!![t.val, 0, 0; 0, L.val 0 0, L.val 0 1; 0, L.val 1 0, L.val 1 1] :
        Matrix (Fin 3) (Fin 3) ℤ).det = t.val * L.val.det := by
      simp [Matrix.det_fin_three, Matrix.det_fin_two]
      ring
    rw [h]
    exact t.isUnit.mul ((Matrix.isUnit_iff_isUnit_det L.val).mp L.isUnit))

/-- The same element of `GL₃(ℚ)`. -/
def leviGL (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) : RationalGL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) (leviInt t L)

theorem leviGL_val (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) :
    (leviGL t L).val = !![(t.val : ℚ), 0, 0; 0, (L.val 0 0 : ℚ), (L.val 0 1 : ℚ);
      0, (L.val 1 0 : ℚ), (L.val 1 1 : ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviGL, leviInt, GeneralLinearGroup.map_apply]

/-- `diag(t, L)` lies in `K†` when `L ∈ Γ₂` (`(0,1) L ≡ (0,1) mod 3`). -/
theorem leviGL_mem_rationalLevel (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ)
    (hL : (L.val 1 0 : ZMod 3) = 0 ∧ (L.val 1 1 : ZMod 3) = 1) : leviGL t L ∈ rationalLevel := by
  apply rationalLevel_badLineLevi (leviInt t L)
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [arithmeticLevel_mem_iff]
  intro column
  fin_cases column <;> simp [leviInt, hL.1, hL.2]

theorem leviInt_inv (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) :
    (leviInt t L)⁻¹ = leviInt t⁻¹ L⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul]
  have hD : L.val * (L⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h00 := congrFun (congrFun hD 0) 0
  have h01 := congrFun (congrFun hD 0) 1
  have h10 := congrFun (congrFun hD 1) 0
  have h11 := congrFun (congrFun hD 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    one_ne_zero, Matrix.GeneralLinearGroup.coe_inv] at h00 h01 h10 h11
  ext i j
  rw [Matrix.mul_apply]
  rcases Int.units_eq_one_or t with rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp [leviInt, Fin.sum_univ_three] <;>
    assumption

/-- **Conjugation of the line radical by the Levi element**: `g⁻¹ U(s,u) g = U(t(s L₀₀ + u L₁₀), t(s L₀₁ + u L₁₁))`, i.e. `r ↦ t r L`. -/
theorem leviGL_conjugate (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) (s u : ℚ) :
    (leviGL t L)⁻¹ * Adelic.lineUnipotent s u * leviGL t L =
      Adelic.lineUnipotent (t.val * (s * L.val 0 0 + u * L.val 1 0) : ℚ)
        (t.val * (s * L.val 0 1 + u * L.val 1 1) : ℚ) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, leviGL_val]
  ext i j
  rcases Int.units_eq_one_or t with rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp [Adelic.lineUnipotent, Adelic.upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The substitution `(X, Y, Z) ↦ (t⁻¹ X, L⁻¹(Y,Z))` of the inverse of `diag(t, L)`. -/
def leviSubst (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) : Poly →ₐ[ℂ] Poly :=
  bind₁ ![C ((t⁻¹).val : ℂ) * X 0,
    C (((L⁻¹).val 0 0 : ℤ) : ℂ) * X 1 + C (((L⁻¹).val 0 1 : ℤ) : ℂ) * X 2,
    C (((L⁻¹).val 1 0 : ℤ) : ℂ) * X 1 + C (((L⁻¹).val 1 1 : ℤ) : ℂ) * X 2]

/-- The binary substitution `(X, Y, Z) ↦ (X, L'(Y,Z))`. -/
def binarySubst (L' : GeneralLinearGroup (Fin 2) ℤ) : Poly →ₐ[ℂ] Poly :=
  bind₁ ![X 0,
    C ((L'.val 0 0 : ℤ) : ℂ) * X 1 + C ((L'.val 0 1 : ℤ) : ℂ) * X 2,
    C ((L'.val 1 0 : ℤ) : ℂ) * X 1 + C ((L'.val 1 1 : ℤ) : ℂ) * X 2]

theorem det_ne_zero (L : GeneralLinearGroup (Fin 2) ℤ) : ((L.val.det : ℤ) : ℂ) ≠ 0 := by
  have hu : IsUnit L.val.det := (Matrix.isUnit_iff_isUnit_det L.val).mp L.isUnit
  exact_mod_cast hu.ne_zero

/-- The entries of the inverse: `det(L) · (L⁻¹)ᵢⱼ` is the adjugate. -/
theorem inv_entries (L : GeneralLinearGroup (Fin 2) ℤ) :
    (L.val.det : ℂ) * ((L⁻¹).val 0 0 : ℤ) = (L.val 1 1 : ℤ) ∧
    (L.val.det : ℂ) * ((L⁻¹).val 0 1 : ℤ) = -(L.val 0 1 : ℤ) ∧
    (L.val.det : ℂ) * ((L⁻¹).val 1 0 : ℤ) = -(L.val 1 0 : ℤ) ∧
    (L.val.det : ℂ) * ((L⁻¹).val 1 1 : ℤ) = (L.val 0 0 : ℤ) := by
  have hadj : L.val.adjugate = L.val.det • (L⁻¹).val := by
    have h1 : L.val * (L⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc L.val.adjugate = L.val.adjugate * (L.val * (L⁻¹).val) := by rw [h1, Matrix.mul_one]
      _ = (L.val.adjugate * L.val) * (L⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [Matrix.adjugate_fin_two] at hadj
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  have e10 := congrFun (congrFun hadj 1) 0
  have e11 := congrFun (congrFun hadj 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast e00.symm
  · exact_mod_cast e01.symm
  · exact_mod_cast e10.symm
  · exact_mod_cast e11.symm

theorem rationalCoefficient_levi (n : ℕ) (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) (p : HomogeneousPoly n) :
    (rationalCoefficientComponent n trivialCharacter (leviGL t L) p).val =
      (((t.val * L.val.det : ℤ) : ℂ)⁻¹) • leviSubst t L p.val := by
  rw [rationalCoefficient_trivial_coe, action_apply]
  let matrix := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (leviGL t L))
  have determinant_eq : determinantCharacter (-1) matrix = (((t.val * L.val.det : ℤ) : ℂ)⁻¹) := by
    simp only [matrix, determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one,
      GeneralLinearGroup.det]
    congr 1
    simp [Matrix.det_fin_three, Matrix.det_fin_two, leviGL_val]
    ring
  rw [determinant_eq]
  congr 1
  have forms : linearForm (matrix⁻¹).val = ![C ((t⁻¹).val : ℂ) * X 0,
      C (((L⁻¹).val 0 0 : ℤ) : ℂ) * X 1 + C (((L⁻¹).val 0 1 : ℤ) : ℂ) * X 2,
      C (((L⁻¹).val 1 0 : ℤ) : ℂ) * X 1 + C (((L⁻¹).val 1 1 : ℤ) : ℂ) * X 2] := by
    dsimp only [matrix]
    unfold leviGL
    rw [← map_inv, ← map_inv, ← map_inv, leviInt_inv]
    funext i
    fin_cases i <;>
      simp [linearForm, GeneralLinearGroup.map_apply, leviInt, Fin.sum_univ_three]
  change substitute (matrix⁻¹).val p.val = leviSubst t L p.val
  rw [substitute, forms]
  rfl

theorem leviSubst_X1 (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) :
    leviSubst t L (X 1) = C (((L⁻¹).val 0 0 : ℤ) : ℂ) * X 1 + C (((L⁻¹).val 0 1 : ℤ) : ℂ) * X 2 := by
  simp [leviSubst]

theorem leviSubst_X2 (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) :
    leviSubst t L (X 2) = C (((L⁻¹).val 1 0 : ℤ) : ℂ) * X 1 + C (((L⁻¹).val 1 1 : ℤ) : ℂ) * X 2 := by
  simp [leviSubst]

theorem leviSubst_preserves (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) (p : Poly)
    (independent : pderiv 0 p = 0) : pderiv 0 (leviSubst t L p) = 0 := by
  rw [← removeFirstVariable_eq_of_pderiv_zero p independent]
  change pderiv 0 (bind₁ _ (removeFirstVariable p)) = 0
  rw [bind_removeFirstVariable]
  apply pderiv_bind_eq_zero
  intro i
  fin_cases i <;> simp

/-- The scalar identities behind the covariance: with `c = (t det L)⁻¹`, `c t L = ±L⁻¹`. -/
theorem levi_scalars (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) :
    (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * (t.val * L.val 0 0 : ℤ) = ((L⁻¹).val 1 1 : ℤ) ∧
    (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * (t.val * L.val 1 0 : ℤ) = -((L⁻¹).val 1 0 : ℤ) ∧
    (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * (t.val * L.val 0 1 : ℤ) = -((L⁻¹).val 0 1 : ℤ) ∧
    (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * (t.val * L.val 1 1 : ℤ) = ((L⁻¹).val 0 0 : ℤ) := by
  obtain ⟨h00, h01, h10, h11⟩ := inv_entries L
  have hD := det_ne_zero L
  have ht : ((t.val : ℤ) : ℂ) ≠ 0 := by exact_mod_cast t.ne_zero
  simp only [Int.cast_mul]
  generalize ((L.val.det : ℤ) : ℂ) = D at hD h00 h01 h10 h11 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    linear_combination (-1 : ℂ) * h11
  · field_simp
    linear_combination h10
  · field_simp
    linear_combination h01
  · field_simp
    linear_combination (-1 : ℂ) * h00

/-- **The law for the radical coordinate under `diag(t, L)`**, in the form of a substitution: the coordinate of the transported cocycle
`(g·b)(u) = g b(g⁻¹ u g)` on the basis `U₁₂, U₁₃` of `N_L` (`g⁻¹ U₁₂ g = U(t L₀₀, t L₀₁)`, `g⁻¹ U₁₃ g = U(t L₁₀, t L₁₁)`) is the image of the coordinate
of `b` under the substitution of `g⁻¹`.  Coefficients `E_{n,1} = Sym^n ⊗ det⁻¹`. -/
theorem radicalPair_leviLaw (n : ℕ) (positive : 0 < n) (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    radicalPairCoordinate n
      (rationalCoefficientComponent n trivialCharacter (leviGL t L)
        (values (t.val * L.val 0 0, t.val * L.val 0 1)))
      (rationalCoefficientComponent n trivialCharacter (leviGL t L)
        (values (t.val * L.val 1 0, t.val * L.val 1 1))) =
      leviSubst t L (radicalPairCoordinate n (values (1,0)) (values (0,1))) := by
  obtain ⟨c1, c2, c3, c4⟩ := levi_scalars t L
  apply radicalPairCoordinate_covariant n positive (leviGL t L) (t.val * L.val 0 0)
    (t.val * L.val 0 1) (t.val * L.val 1 0) (t.val * L.val 1 1) (leviSubst t L)
    (by simpa using leviGL_conjugate t L 1 0) (by simpa using leviGL_conjugate t L 0 1) ?_ ?_
    values relation
  · intro q hq
    rw [rationalCoefficient_levi, Derivation.map_smul, leviSubst_preserves t L q.val hq, smul_zero]
  · intro q r
    have e1 := rationalCoefficient_levi n t L q
    have e2 := rationalCoefficient_levi n t L r
    have lift : ∀ z : ℤ, (z : Poly) = C (z : ℂ) := fun z => (map_intCast (C : ℂ →+* Poly) z).symm
    have hP1 : C (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * ((t.val * L.val 0 0 : ℤ) : Poly) =
        C (((L⁻¹).val 1 1 : ℤ) : ℂ) := by rw [lift, ← map_mul, c1]
    have hP2 : C (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * ((t.val * L.val 1 0 : ℤ) : Poly) =
        -C (((L⁻¹).val 1 0 : ℤ) : ℂ) := by rw [lift, ← map_mul, c2, map_neg]
    have hP3 : C (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * ((t.val * L.val 0 1 : ℤ) : Poly) =
        -C (((L⁻¹).val 0 1 : ℤ) : ℂ) := by rw [lift, ← map_mul, c3, map_neg]
    have hP4 : C (((t.val * L.val.det : ℤ) : ℂ)⁻¹) * ((t.val * L.val 1 1 : ℤ) : Poly) =
        C (((L⁻¹).val 0 0 : ℤ) : ℂ) := by rw [lift, ← map_mul, c4]
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, e1, e2, map_sub, map_mul,
      leviSubst_X1, leviSubst_X2]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    linear_combination (X 2 * leviSubst t L q.val) * hP1 + (X 2 * leviSubst t L r.val) * hP3
      - (X 1 * leviSubst t L q.val) * hP2 - (X 1 * leviSubst t L r.val) * hP4

/-- The radical coordinate of a cocycle of `N_L` does not involve `X` (`∂_X J = 0`). -/
theorem radicalPair_pderiv_zero (n : ℕ) (positive : 0 < n)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    pderiv 0 (radicalPairCoordinate n (values (1,0)) (values (0,1))) = 0 := by
  obtain ⟨primitive, a, b, ha, hb, normal_form⟩ := radical_cocycle_normal_form n positive values relation
  have first_original : values (1,0) = primitive - rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 1 0) primitive + a := by simpa [integralRadicalHom] using normal_form (1,0)
  have second_original : values (0,1) = primitive - rationalCoefficientComponent n trivialCharacter
      (Adelic.lineUnipotent 0 1) primitive + b := by simpa [integralRadicalHom] using normal_form (0,1)
  rw [first_original, second_original]
  simp only [radicalPairCoordinate]
  rw [radicalCoordinate_normal_form n positive primitive a b ha hb]
  simp only [map_sub, pderiv_mul, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0),
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0), zero_mul, zero_add, ha, hb, mul_zero, sub_zero]

/-- On polynomials not involving `X`, the substitution of `g⁻¹` is the binary substitution `(Y, Z) ↦ L⁻¹ (Y, Z)`. -/
theorem leviSubst_eq_binarySubst (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ) (p : Poly)
    (independent : pderiv 0 p = 0) : leviSubst t L p = binarySubst L⁻¹ p := by
  rw [← removeFirstVariable_eq_of_pderiv_zero p independent]
  unfold leviSubst binarySubst
  rw [bind_removeFirstVariable, bind_removeFirstVariable]
  simp

/-- **`diag(t, L): J(v) ↦ t⁻² J(L⁻¹ v)`.**  For every one-cocycle `b` of the line radical (`values`) with coefficients in
`E_{n,1}`, the radical coordinate of the transported cocycle `g·b` is `t⁻²` times the coordinate of `b` evaluated at `L⁻¹ (Y, Z)`; here `t = ±1`
(`t⁻² = 1`) and `L ∈ GL₂(ℤ)` is arbitrary (not only `Γ₂`). -/
theorem radicalPair_leviLaw_binary (n : ℕ) (positive : 0 < n) (t : ℤˣ) (L : GeneralLinearGroup (Fin 2) ℤ)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    radicalPairCoordinate n
      (rationalCoefficientComponent n trivialCharacter (leviGL t L)
        (values (t.val * L.val 0 0, t.val * L.val 0 1)))
      (rationalCoefficientComponent n trivialCharacter (leviGL t L)
        (values (t.val * L.val 1 0, t.val * L.val 1 1))) =
      (((t.val : ℂ) ^ 2)⁻¹) • binarySubst L⁻¹ (radicalPairCoordinate n (values (1,0)) (values (0,1))) := by
  rw [radicalPair_leviLaw n positive t L values relation,
    leviSubst_eq_binarySubst t L _ (radicalPair_pderiv_zero n positive values relation)]
  have h : ((t.val : ℂ) ^ 2)⁻¹ = 1 := by
    rcases Int.units_eq_one_or t with rfl | rfl <;> simp
  rw [h, one_smul]

/-- **The independent integral line sign acts trivially**: `diag(t, 1)` with `t = ±1` fixes the radical coordinate. -/
theorem radicalPair_lineSign (n : ℕ) (positive : 0 < n) (t : ℤˣ)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y)) :
    radicalPairCoordinate n
      (rationalCoefficientComponent n trivialCharacter (leviGL t 1) (values (t.val, 0)))
      (rationalCoefficientComponent n trivialCharacter (leviGL t 1) (values (0, t.val))) =
      radicalPairCoordinate n (values (1,0)) (values (0,1)) := by
  have h := radicalPair_leviLaw_binary n positive t 1 values relation
  have e : binarySubst (1 : GeneralLinearGroup (Fin 2) ℤ) = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [binarySubst]
  simp only [inv_one, e] at h
  have h2 : ((t.val : ℂ) ^ 2)⁻¹ = 1 := by
    rcases Int.units_eq_one_or t with rfl | rfl <;> simp
  simpa [h2] using h

end TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw
