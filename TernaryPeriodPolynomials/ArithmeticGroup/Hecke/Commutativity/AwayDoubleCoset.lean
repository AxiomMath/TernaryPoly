module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.Involution
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.IntegerSmith
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.CongruenceLift
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.ShimuraCount

@[expose] public section


/-!
# `ι x ∈ Γ x Γ` for every `x` whose local component at three lies in `K₁(3)`

`Good x` says that some integral multiple `m x` (with `3 ∤ m`) is an integer
matrix of determinant prime to three whose last row is `m e₃*` modulo three.
Such elements form a monoid containing the level.  For them an elementary
divisor decomposition `x = γ₁ δ γ₂` with `γᵢ ∈ rationalLevel` and `δ` diagonal
exists, whence `ι x = ι γ₂ δ ι γ₁ ∈ Γ x Γ`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- Rational matrices that are, up to a scalar prime to three, integral with
determinant prime to three and last row `e₃*` modulo three. -/
def Good (x : RationalGL3) : Prop :=
  ∃ m : ℤ, (m : ZMod 3) ≠ 0 ∧ ∃ X : Matrix (Fin 3) (Fin 3) ℤ,
    (m : ℚ) • x.val = X.map (Int.cast : ℤ → ℚ) ∧ (X.det : ZMod 3) ≠ 0 ∧
    ∀ j, ((X 2 j : ℤ) : ZMod 3) = if j = 2 then (m : ZMod 3) else 0

theorem intCast_map_mul (M N : Matrix (Fin 3) (Fin 3) ℤ) :
    (M * N).map (Int.cast : ℤ → ℚ) = M.map (Int.cast : ℤ → ℚ) * N.map (Int.cast : ℤ → ℚ) := by
  have := Matrix.map_mul (L := M) (M := N) (f := Int.castRingHom ℚ)
  simpa only [Int.coe_castRingHom] using this

theorem row_mul_three (M N : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3) :
    (((M * N) 2 j : ℤ) : ZMod 3) =
      (M 2 0 : ZMod 3) * N 0 j + (M 2 1 : ZMod 3) * N 1 j + (M 2 2 : ZMod 3) * N 2 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem good_mul {x y : RationalGL3} (hx : Good x) (hy : Good y) : Good (x * y) := by
  obtain ⟨m, hm, X, hX, hXd, hXr⟩ := hx
  obtain ⟨n, hn, Y, hY, hYd, hYr⟩ := hy
  refine ⟨m * n, by push_cast; exact mul_ne_zero hm hn, X * Y, ?_, ?_, ?_⟩
  · rw [Units.val_mul, Int.cast_mul, mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, hX, hY,
      intCast_map_mul]
  · rw [Matrix.det_mul, Int.cast_mul]
    exact mul_ne_zero hXd hYd
  · intro j
    rw [row_mul_three, hXr 0, hXr 1, hXr 2, hYr j]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ite_false,
      ite_true, zero_mul, zero_add]
    split_ifs <;> push_cast <;> ring

theorem good_of_mem {x : RationalGL3} (hx : x ∈ rationalLevel) : Good x := by
  obtain ⟨M, hM, hdet, hrow⟩ := int_of_mem_rationalLevel hx
  refine ⟨1, by simp, M, by rw [hM]; simp, ?_, by simpa using hrow⟩
  rcases Int.isUnit_iff.mp hdet with h | h <;> rw [h] <;> simp

/-- An invertible integer matrix as a rational matrix. -/
def ofInt (M : Matrix (Fin 3) (Fin 3) ℤ) (h : IsUnit M.det) : RationalGL3 where
  val := M.map (Int.cast : ℤ → ℚ)
  inv := M⁻¹.map (Int.cast : ℤ → ℚ)
  val_inv := by
    rw [← intCast_map_mul, Matrix.mul_nonsing_inv M h, Matrix.map_one _ Int.cast_zero Int.cast_one]
  inv_val := by
    rw [← intCast_map_mul, Matrix.nonsing_inv_mul M h, Matrix.map_one _ Int.cast_zero Int.cast_one]

@[simp] theorem ofInt_val (M : Matrix (Fin 3) (Fin 3) ℤ) (h : IsUnit M.det) :
    (ofInt M h).val = M.map (Int.cast : ℤ → ℚ) := rfl

theorem zmod_three_eq_neg_one {z : ZMod 3} (h0 : z ≠ 0) (h1 : z ≠ 1) : z = -1 := by
  revert z
  decide

theorem red_entry_eq {M N : Matrix (Fin 3) (Fin 3) ℤ} (h : ∀ i j, (3 : ℤ) ∣ M i j - N i j)
    (i j : Fin 3) : ((M i j : ℤ) : ZMod 3) = N i j :=
  ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mpr (by exact_mod_cast dvd_sub_comm.mp (h i j)))

/-- **Elementary divisors at the level.**  Every `Good` element is
`γ₁ δ γ₂` with `γ₁, γ₂ ∈ rationalLevel` and `δ` diagonal. -/
theorem exists_level_diagonal {x : RationalGL3} (hx : Good x) :
    ∃ γ₁ ∈ rationalLevel, ∃ γ₂ ∈ rationalLevel, ∃ d : Fin 3 → ℚ,
      (γ₁⁻¹ * x * γ₂⁻¹).val = diagonal d := by
  classical
  obtain ⟨m, hm, X, hX, hXd, hXr⟩ := hx
  have hX0 : X.det ≠ 0 := by intro h; apply hXd; rw [h]; simp
  obtain ⟨A, Q, A', Q', a, hAA', hA'A, hQQ', hQ'Q, hXeq⟩ := exists_eq_mul_diagonal_mul X hX0
  have hdetA : A.det * A'.det = 1 := by rw [← Matrix.det_mul, hAA', Matrix.det_one]
  have hdetQ : Q.det * Q'.det = 1 := by rw [← Matrix.det_mul, hQQ', Matrix.det_one]
  set dA := A.det with hdA
  have hdA1 : dA * dA = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetA with h | h <;> rw [h] <;> norm_num
  let E : Matrix (Fin 3) (Fin 3) ℤ := diagonal ![1, 1, dA]
  have hE : E * E = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hdA1]
  have hdetE : E.det = dA := by simp [E, det_diagonal, Fin.prod_univ_three]
  have hA'E : (A' * E).det = 1 := by rw [det_mul, hdetE, mul_comm, hdetA]
  set dp := ∏ i, a i with hdp
  have hdetX : X.det = dA * dp * Q.det := by rw [hXeq, det_mul, det_mul, det_diagonal]
  have hdp3 : ¬ (3 : ℤ) ∣ dp := by
    intro h
    apply hXd
    rw [hdetX]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast (h.mul_left dA).mul_right _)
  have hdp0 : dp ≠ 0 := by rintro h; exact hdp3 (h ▸ dvd_zero _)
  obtain ⟨σ, hσ3, hσd⟩ := exists_sl_lift (A' * E) hA'E dp hdp3
  choose Y hY using hσd
  set S : Matrix (Fin 3) (Fin 3) ℤ :=
    ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) with hS
  set Sv : Matrix (Fin 3) (Fin 3) ℤ := (σ : Matrix (Fin 3) (Fin 3) ℤ) with hSv
  have hSmat : S = 1 + dp • Matrix.of Y := by
    apply Matrix.ext
    intro i j
    have := hY i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linarith
  have hσS : Sv * S = 1 := by
    rw [hSv, hS, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hdetS : S.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hdetSv : Sv.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  let e : Fin 3 → ℤ := fun i => ∏ j ∈ Finset.univ.erase i, a j
  have hae : ∀ i, a i * e i = dp := fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  let B : Matrix (Fin 3) (Fin 3) ℤ := (1 + diagonal e * Matrix.of Y * diagonal a) * Q
  have hDB : diagonal a * B = S * diagonal a * Q := by
    have hdiag : diagonal a * diagonal e = dp • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
      rw [diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      exact hae i
    calc diagonal a * B = (diagonal a + (diagonal a * diagonal e) * Matrix.of Y * diagonal a) * Q := by
          simp only [B, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc, Matrix.add_mul]
      _ = S * diagonal a * Q := by
          rw [hdiag, hSmat]
          simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]
  let P : Matrix (Fin 3) (Fin 3) ℤ := A * Sv
  have hXPB : X = P * diagonal a * B := by
    calc X = A * diagonal a * Q := hXeq
      _ = A * (Sv * S) * diagonal a * Q := by rw [hσS, Matrix.mul_one]
      _ = P * (diagonal a * B) := by rw [hDB]; simp only [P, Matrix.mul_assoc]
      _ = P * diagonal a * B := (Matrix.mul_assoc P _ _).symm
  -- last row of `P` modulo three
  have hSv3 : ∀ i j, ((Sv i j : ℤ) : ZMod 3) = (A' * E) i j := red_entry_eq hσ3
  have hProw : ∀ j, ((P 2 j : ℤ) : ZMod 3) = if j = 2 then (dA : ZMod 3) else 0 := by
    have hred : (Int.castRingHom (ZMod 3)).mapMatrix P = (Int.castRingHom (ZMod 3)).mapMatrix E := by
      have h1 : (Int.castRingHom (ZMod 3)).mapMatrix Sv =
          (Int.castRingHom (ZMod 3)).mapMatrix (A' * E) := by
        apply Matrix.ext; intro i j; simpa using hSv3 i j
      simp only [P, map_mul, h1]
      rw [← map_mul, ← map_mul, ← Matrix.mul_assoc, hAA', Matrix.one_mul]
    intro j
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod 3) => M 2 j) hred
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] at this
    rw [this]
    fin_cases j <;> simp [E]
  -- last row of `B` modulo three
  have ha2 : (a 2 : ZMod 3) ≠ 0 := by
    intro h
    apply hdp3
    have h' : (3 : ℤ) ∣ a 2 := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h
    rw [hdp, Fin.prod_univ_three]
    exact h'.mul_left _
  have hdA3 : (dA : ZMod 3) * dA = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) hdA1
  have hBrow0 : ∀ j, ((X 2 j : ℤ) : ZMod 3) = (dA : ZMod 3) * a 2 * B 2 j := by
    intro j
    rw [hXPB, Matrix.mul_assoc, row_mul_three, hProw 0, hProw 1, hProw 2]
    simp [Matrix.diagonal_mul, mul_assoc]
  have hBrow : ∀ j, j ≠ 2 → ((B 2 j : ℤ) : ZMod 3) = 0 := by
    intro j hj
    have h := hBrow0 j
    rw [hXr j, ite_eq_right hj] at h
    have hu : (dA : ZMod 3) * a 2 ≠ 0 := mul_ne_zero (by intro h0; rw [h0] at hdA3; simp at hdA3) ha2
    exact (mul_eq_zero.mp h.symm).resolve_left hu
  have hB22 : ((B 2 2 : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    have h := hBrow0 2
    rw [hXr 2, ite_eq_left rfl, h0, mul_zero] at h
    exact hm h
  let qi : ℤ := if ((B 2 2 : ℤ) : ZMod 3) = 1 then 1 else -1
  have hqi : ((qi : ℤ) : ZMod 3) = B 2 2 := by
    simp only [qi]
    split_ifs with h
    · rw [h]; simp
    · rw [zmod_three_eq_neg_one hB22 h]; simp
      rfl
  have hqi1 : qi * qi = 1 := by simp only [qi]; split_ifs <;> norm_num
  -- the normalized decomposition
  let Ep : Matrix (Fin 3) (Fin 3) ℤ := diagonal ![1, 1, dA]
  let Eq : Matrix (Fin 3) (Fin 3) ℤ := diagonal ![1, 1, qi]
  have hEp : Ep * Ep = 1 := hE
  have hEq : Eq * Eq = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hqi1]
  let P₁ := P * Ep
  let B₁ := Eq * B
  let d₁ : Fin 3 → ℤ := fun i => ![1, 1, dA] i * a i * ![1, 1, qi] i
  have hD₁ : Ep * diagonal a * Eq = diagonal d₁ := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  have hX₁ : X = P₁ * diagonal d₁ * B₁ := by
    rw [← hD₁]
    calc X = P * (Ep * Ep) * diagonal a * (Eq * Eq) * B := by
          rw [hEp, hEq, Matrix.mul_one, Matrix.mul_one, hXPB]
      _ = P₁ * (Ep * diagonal a * Eq) * B₁ := by simp only [P₁, B₁, Matrix.mul_assoc]
  have hP₁unit : IsUnit P₁.det := by
    have : P₁.det = 1 := by
      have h1 : P₁ = A * Sv * E := rfl
      rw [h1, det_mul, det_mul, hdetSv, hdetE, mul_one]
      exact hdA1
    rw [this]; exact isUnit_one
  have hdetB : B.det = Q.det := by
    have h : (diagonal a).det * B.det = S.det * (diagonal a).det * Q.det := by
      rw [← det_mul, hDB, det_mul, det_mul]
    rw [hdetS, one_mul, det_diagonal] at h
    exact mul_left_cancel₀ hdp0 h
  have hB₁unit : IsUnit B₁.det := by
    have hq : IsUnit qi := by
      simp only [qi]; split_ifs
      · exact isUnit_one
      · exact isUnit_one.neg
    have hQ : IsUnit Q.det := isUnit_iff_exists_inv.mpr ⟨_, hdetQ⟩
    simp only [B₁, Eq, det_mul, det_diagonal, Fin.prod_univ_three, hdetB]
    simpa using hq.mul hQ
  have hP₁row : ∀ j, ((P₁ 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j
    simp only [P₁, Ep, Matrix.mul_diagonal]
    push_cast
    rw [hProw j]
    fin_cases j <;> simp [hdA3]
  have hB₁row : ∀ j, ((B₁ 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j
    simp only [B₁, Eq, Matrix.diagonal_mul]
    push_cast
    fin_cases j
    · simp [hBrow 0 (by decide)]
    · simp [hBrow 1 (by decide)]
    · rw [hqi]
      have : ((qi * qi : ℤ) : ZMod 3) = 1 := by rw [hqi1]; simp
      push_cast at this
      rw [hqi] at this
      simpa using this
  let γ₁ := ofInt P₁ hP₁unit
  let γ₂ := ofInt B₁ hB₁unit
  have hγ₁ : γ₁ ∈ rationalLevel := mem_rationalLevel_of_int γ₁ P₁ rfl hP₁unit hP₁row
  have hγ₂ : γ₂ ∈ rationalLevel := mem_rationalLevel_of_int γ₂ B₁ rfl hB₁unit hB₁row
  have hmQ : (m : ℚ) ≠ 0 := by
    intro h
    apply hm
    have : m = 0 := by exact_mod_cast h
    rw [this]; simp
  refine ⟨γ₁, hγ₁, γ₂, hγ₂, fun i => (m : ℚ)⁻¹ * (d₁ i : ℚ), ?_⟩
  have hxval : x.val = (m : ℚ)⁻¹ • (γ₁.val * (diagonal d₁).map (Int.cast : ℤ → ℚ) * γ₂.val) := by
    rw [ofInt_val, ofInt_val, ← intCast_map_mul, ← intCast_map_mul, ← hX₁, ← hX, smul_smul,
      inv_mul_cancel₀ hmQ, one_smul]
  have h1 : (γ₁⁻¹ : RationalGL3).val * γ₁.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : γ₂.val * (γ₂⁻¹ : RationalGL3).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, hxval, Matrix.mul_smul, Matrix.smul_mul]
  rw [show (γ₁⁻¹ : RationalGL3).val * (γ₁.val * (diagonal d₁).map (Int.cast : ℤ → ℚ) * γ₂.val) *
      (γ₂⁻¹ : RationalGL3).val = ((γ₁⁻¹ : RationalGL3).val * γ₁.val) *
        (diagonal d₁).map (Int.cast : ℤ → ℚ) * (γ₂.val * (γ₂⁻¹ : RationalGL3).val) by
      simp only [Matrix.mul_assoc]]
  rw [h1, h2, Matrix.one_mul, Matrix.mul_one, Matrix.diagonal_map (Int.cast_zero), ← diagonal_smul]
  rfl

/-- **Gelfand's hypothesis** for the level: `ι x ∈ Γ x Γ` for every `Good` element. -/
theorem ι_mem_dcoset_of_good {x : RationalGL3} (hx : Good x) : ι x ∈ dcoset rationalLevel x := by
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, d, hd⟩ := exists_level_diagonal hx
  set δ := γ₁⁻¹ * x * γ₂⁻¹ with hδ
  have hιδ : ι δ = δ := ι_of_diagonal δ d hd
  have hx' : x = γ₁ * δ * γ₂ := by rw [hδ]; group
  refine ⟨ι γ₂ * γ₁⁻¹, mul_mem (ι_mem_rationalLevel hγ₂) (inv_mem hγ₁),
    γ₂⁻¹ * ι γ₁, mul_mem (inv_mem hγ₂) (ι_mem_rationalLevel hγ₁), ?_⟩
  conv_lhs => rw [hx']
  rw [ι_mul, ι_mul, hιδ]
  conv_rhs => rw [hx']
  group

end TernaryPeriodPolynomials.HeckeCommutativity
