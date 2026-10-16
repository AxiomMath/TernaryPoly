module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.AdelicApproximation

@[expose] public section


/-!
# Membership criteria for `finiteLevel` and adapted dilations

`exists_dilation`: for a rational matrix `r` and a unit `β` of `Ẑ` with `β ≡ 1 (mod 3)`, there is `u ∈ GL₃(Ẑ)` with `det u = β`, trivial reduction modulo three,
whose conjugate `r⁻¹ u r` is again in `GL₃(Ẑ)` with trivial reduction. It is the dilation
`1 + (β - 1) V wᵀ` along a column `V` of a primitive integral multiple of `r`, chosen
place by place.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.HeckeStability.AdelicApproximation

noncomputable section

namespace TernaryPeriodPolynomials.HeckeStability.Dilation

/-- Integral adelic `3 × 3` matrices. -/
abbrev IntMat := Matrix (Fin 3) (Fin 3) IntegralAdeles

theorem integralReduction_congr {x y : IntegralAdeles} (h : x placeThree = y placeThree) :
    integralReduction x = integralReduction y := by
  simp only [integralReduction, integralThree, RingHom.comp_apply, Pi.evalRingHom_apply, h]

theorem integralReduction_natCast_mul (x : IntegralAdeles) (M : ℕ) (h : 3 ∣ M) :
    integralReduction ((M : IntegralAdeles) * x) = 0 := by
  rw [map_mul, map_natCast, (ZMod.natCast_eq_zero_iff M 3).mpr h, zero_mul]

/-- A finite-adelic group element whose matrix and inverse matrix are integral, with
integral matrix reducing into the row stabilizer, lies in `finiteLevel`. -/
theorem mem_finiteLevel_of_integral (g : FiniteGL) (A B : IntMat)
    (hA : g.val = A.map integralEmbedding) (hB : (g⁻¹).val = B.map integralEmbedding)
    (hred : lastRow ᵥ* A.map integralReduction = lastRow) : g ∈ finiteLevel := by
  have hinj : Function.Injective (fun X : IntMat => X.map integralEmbedding) :=
    Matrix.map_injective integralEmbedding_injective
  have hone : (1 : IntMat).map integralEmbedding = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hAB : A * B = 1 := by
    apply hinj
    change (A * B).map integralEmbedding = (1 : IntMat).map integralEmbedding
    rw [Matrix.map_mul, ← hA, ← hB, Units.mul_inv, hone]
  have hBA : B * A = 1 := by
    apply hinj
    change (B * A).map integralEmbedding = (1 : IntMat).map integralEmbedding
    rw [Matrix.map_mul, ← hA, ← hB, Units.inv_mul, hone]
  let κ : GeneralLinearGroup (Fin 3) IntegralAdeles := ⟨A, B, hAB, hBA⟩
  refine Subgroup.mem_map.mpr ⟨κ, ?_, ?_⟩
  · change lastRow ᵥ* (GeneralLinearGroup.map integralReduction κ).val = lastRow
    exact hred
  · apply Units.ext
    rw [hA]
    rfl

/-- Elements of `GL₃(Ẑ)` with trivial reduction modulo three lie in `finiteLevel`. -/
theorem map_mem_finiteLevel_of_reduction_one (κ : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (h : κ.val.map integralReduction = 1) :
    GeneralLinearGroup.map integralEmbedding κ ∈ finiteLevel := by
  refine mem_finiteLevel_of_integral _ κ.val (κ⁻¹).val rfl ?_ ?_
  · rw [← map_inv]; rfl
  · rw [h, vecMul_one]

/-- `rationalFinite` of an integer matrix is the image of the integral adelic matrix. -/
theorem rationalFinite_intCast (γ : IntegralGL3) :
    rationalFinite (GeneralLinearGroup.map (Int.castRingHom ℚ) γ) =
      GeneralLinearGroup.map integralEmbedding
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp [rationalFinite, GeneralLinearGroup.map_apply]

theorem one_add_vecMulVec_mul {V : Fin 3 → IntegralAdeles} (x y : Fin 3 → IntegralAdeles) :
    (1 + vecMulVec V x) * (1 + vecMulVec V y) = 1 + vecMulVec V (x + y + (x ⬝ᵥ V) • y) := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec,
    vecMulVec_add, vecMulVec_add]
  abel

theorem one_add_vecMulVec_inverse {V w : Fin 3 → IntegralAdeles} (hwV : w ⬝ᵥ V = 1)
    {a b : IntegralAdeles} (hab : a + b + a * b = 0) :
    (1 + vecMulVec V (a • w)) * (1 + vecMulVec V (b • w)) = 1 := by
  rw [one_add_vecMulVec_mul, smul_dotProduct, hwV, smul_eq_mul, mul_one, smul_smul, ← add_smul,
    ← add_smul, hab, zero_smul, vecMulVec_zero, add_zero]

theorem reduction_one_add_vecMulVec (V w : Fin 3 → IntegralAdeles) {a : IntegralAdeles}
    (ha : integralReduction a = 0) :
    (1 + vecMulVec V (a • w)).map integralReduction = 1 := by
  ext i j
  rw [Matrix.map_apply, Matrix.add_apply, map_add, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    map_mul, map_mul, ha, zero_mul, mul_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem exists_dilation (r : RationalGL3) (d : ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (hd : (d : ℚ) ≠ 0) (hN : ∀ i j, (d : ℚ) * r.val i j = N i j)
    (β : IntegralAdelesˣ) (hβ : integralReduction (β : IntegralAdeles) = 1) :
    ∃ u : GeneralLinearGroup (Fin 3) IntegralAdeles,
      u.val.det = β ∧ u.val.map integralReduction = 1 ∧
      ∃ U : GeneralLinearGroup (Fin 3) IntegralAdeles, U.val.map integralReduction = 1 ∧
        (rationalFinite r)⁻¹ * GeneralLinearGroup.map integralEmbedding u * rationalFinite r =
          GeneralLinearGroup.map integralEmbedding U := by
  classical
  obtain ⟨X, hNX, hX1⟩ := Finset.extract_gcd (fun ij : Fin 3 × Fin 3 => N ij.1 ij.2)
    (Finset.univ_nonempty (α := Fin 3 × Fin 3))
  set c : ℤ := Finset.univ.gcd (fun ij : Fin 3 × Fin 3 => N ij.1 ij.2) with hc
  have hprim : ∀ v : FinitePlace, ∃ ij : Fin 3 × Fin 3, ¬ (placePrime v : ℤ) ∣ X ij := by
    intro v
    by_contra h
    push Not at h
    have hdvd : (placePrime v : ℤ) ∣ Finset.univ.gcd X := Finset.dvd_gcd (fun b _ => h b)
    rw [hX1] at hdvd
    have hp := (placePrime_fact v).out
    have : (placePrime v : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
    have : 1 < (placePrime v : ℤ) := by exact_mod_cast hp.one_lt
    omega
  choose ij hij using hprim
  have hunit : ∀ v : FinitePlace, IsUnit (((X (ij v) : ℤ) : v.adicCompletionIntegers ℚ)) :=
    fun v => isUnit_intCast_of_not_dvd v _ (hij v)
  choose ε hε using hunit
  let Xa : IntMat := Matrix.of fun i j => ((X (i, j) : ℤ) : IntegralAdeles)
  let E : Fin 3 → IntegralAdeles := fun k v => if k = (ij v).2 then 1 else 0
  let w : Fin 3 → IntegralAdeles := fun k v => if k = (ij v).1 then ((ε v)⁻¹ : _) else 0
  have hV : ∀ k (v : FinitePlace), (Xa *ᵥ E) k v = ((X (k, (ij v).2) : ℤ) : v.adicCompletionIntegers ℚ) := by
    intro k v
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply, Xa, E, Matrix.of_apply]
    rw [Finset.sum_eq_single (ij v).2]
    · simp
    · intro l _ hl
      simp [hl]
    · simp
  have hwV : w ⬝ᵥ (Xa *ᵥ E) = 1 := by
    funext v
    simp only [dotProduct, Finset.sum_apply, Pi.mul_apply, hV, Pi.one_apply]
    rw [Finset.sum_eq_single (ij v).1]
    · simp only [w, ite_true]
      rw [Prod.mk.eta, ← hε v, Units.inv_mul]
    · intro l _ hl
      simp [w, hl]
    · simp
  have hwXE : (w ᵥ* Xa) ⬝ᵥ E = 1 := by rw [← dotProduct_mulVec, hwV]
  set V := Xa *ᵥ E with hVdef
  set a : IntegralAdeles := (β : IntegralAdeles) - 1 with ha
  set b : IntegralAdeles := ((β⁻¹ : IntegralAdelesˣ) : IntegralAdeles) - 1 with hb
  have hab : a + b + a * b = 0 := by
    have h := β.mul_inv
    rw [ha, hb]
    linear_combination h
  have hba : b + a + b * a = 0 := by rw [← hab]; ring
  have hred_a : integralReduction a = 0 := by
    rw [ha, map_sub, map_one, hβ, sub_self]
  let u : GeneralLinearGroup (Fin 3) IntegralAdeles :=
    ⟨1 + vecMulVec V (a • w), 1 + vecMulVec V (b • w),
      one_add_vecMulVec_inverse hwV hab, one_add_vecMulVec_inverse hwV hba⟩
  let U : GeneralLinearGroup (Fin 3) IntegralAdeles :=
    ⟨1 + vecMulVec E (a • (w ᵥ* Xa)), 1 + vecMulVec E (b • (w ᵥ* Xa)),
      one_add_vecMulVec_inverse hwXE hab, one_add_vecMulVec_inverse hwXE hba⟩
  refine ⟨u, ?_, reduction_one_add_vecMulVec _ _ hred_a, U,
    reduction_one_add_vecMulVec _ _ hred_a, ?_⟩
  · change (1 + vecMulVec V (a • w)).det = β
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, hwV,
      smul_eq_mul, mul_one, ha]
    ring
  · -- conjugation identity
    have hkey : Xa * U.val = u.val * Xa := by
      change Xa * (1 + vecMulVec E (a • (w ᵥ* Xa))) = (1 + vecMulVec V (a • w)) * Xa
      rw [mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, smul_vecMul]
    have hR : (rationalFinite r).val =
        (algebraMap ℚ FiniteAdeles ((c : ℚ) / d)) • Xa.map integralEmbedding := by
      apply Matrix.ext
      intro i j
      have hij := hN i j
      have hNij := hNX (i, j) (Finset.mem_univ _)
      simp only at hNij
      have hr : r.val i j = (c : ℚ) / d * (X (i, j) : ℚ) := by
        rw [div_mul_eq_mul_div, eq_div_iff hd, mul_comm, hij, hNij]
        push_cast
        ring
      simp only [rationalFinite, GeneralLinearGroup.map_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, Xa, Matrix.of_apply, map_intCast]
      rw [hr, map_mul]
      simp
    have hmul : GeneralLinearGroup.map integralEmbedding u * rationalFinite r =
        rationalFinite r * GeneralLinearGroup.map integralEmbedding U := by
      apply Units.ext
      change u.val.map integralEmbedding * (rationalFinite r).val =
        (rationalFinite r).val * U.val.map integralEmbedding
      rw [hR, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, hkey]
    rw [mul_assoc, hmul, ← mul_assoc, inv_mul_cancel, one_mul]

end TernaryPeriodPolynomials.HeckeStability.Dilation
