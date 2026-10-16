module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.Dilation
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.StrongApproximation

@[expose] public section



/-!
# Single-coset decomposition of the finite level

For every `r ∈ GL₃(ℚ)`, every `k ∈ finiteLevel`
factors as `k = rf(γ) · u` with `γ ∈ rationalLevel` and `u ∈ finiteLevel ∩ R finiteLevel R⁻¹`
(`R = rf r`). The proof uses three ingredients:
1. a dilation of determinant `det k` adapted to `r` (`Dilation.exists_dilation`);
2. integer approximation modulo `M = 3 |d d'|`, where `d r` and `d' r⁻¹` are integral (`AdelicApproximation`);
3. strong approximation `SL₃(ℤ) → SL₃(ℤ/M)` (`StrongApproximation`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.HeckeStability.AdelicApproximation
open TernaryPeriodPolynomials.HeckeStability.Dilation

noncomputable section

namespace TernaryPeriodPolynomials.HeckeStability.CosetDecomposition

theorem exists_matrix_approx (M : ℕ) (hM : M ≠ 0) (A : IntMat) :
    ∃ Z : Matrix (Fin 3) (Fin 3) ℤ, ∃ Y : IntMat,
      A = Z.map (Int.castRingHom IntegralAdeles) + (M : IntegralAdeles) • Y := by
  choose Z Y hZY using fun i j => exists_int_add_mul M hM (A i j)
  refine ⟨Matrix.of Z, Matrix.of Y, ?_⟩
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    eq_intCast]
  exact hZY i j

theorem det_congr (M : ℕ) (Z : Matrix (Fin 3) (Fin 3) ℤ) (Y : IntMat) :
    ∃ y : IntegralAdeles, (Z.map (Int.castRingHom IntegralAdeles) + (M : IntegralAdeles) • Y).det =
      ((Z.det : ℤ) : IntegralAdeles) + (M : IntegralAdeles) * y := by
  let I : Ideal IntegralAdeles := Ideal.span {(M : IntegralAdeles)}
  let π := Ideal.Quotient.mk I
  have hM0 : π (M : IntegralAdeles) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hmat : π.mapMatrix (Z.map (Int.castRingHom IntegralAdeles) + (M : IntegralAdeles) • Y) =
      π.mapMatrix (Z.map (Int.castRingHom IntegralAdeles)) := by
    apply Matrix.ext
    intro i j
    show π ((Z.map (Int.castRingHom IntegralAdeles) + (M : IntegralAdeles) • Y) i j) =
      π ((Z.map (Int.castRingHom IntegralAdeles)) i j)
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, hM0,
      zero_mul, add_zero]
  have h1 : π (Z.map (Int.castRingHom IntegralAdeles) + (M : IntegralAdeles) • Y).det =
      π ((Z.det : ℤ) : IntegralAdeles) := by
    rw [RingHom.map_det, hmat, ← RingHom.map_det]
    congr 1
    have := (Int.castRingHom IntegralAdeles).map_det Z
    simpa using this.symm
  rw [Ideal.Quotient.eq] at h1
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h1
  exact ⟨y, by rw [mul_comm, hy]; ring⟩

/-- `N' * N = (d d') • 1` for integral multiples `N = d r`, `N' = d' r⁻¹`. -/
theorem int_mul_eq (r : RationalGL3) (d d' : ℤ) (N N' : Matrix (Fin 3) (Fin 3) ℤ)
    (hN : ∀ i j, (d : ℚ) * r.val i j = N i j) (hN' : ∀ i j, (d' : ℚ) * (r⁻¹).val i j = N' i j) :
    N' * N = (d * d') • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
  change (N' * N).map (Int.castRingHom ℚ) = ((d * d') • (1 : Matrix (Fin 3) (Fin 3) ℤ)).map
    (Int.castRingHom ℚ)
  have hNq : N.map (Int.castRingHom ℚ) = (d : ℚ) • r.val := by
    apply Matrix.ext; intro i j; simp [← hN i j]
  have hN'q : N'.map (Int.castRingHom ℚ) = (d' : ℚ) • (r⁻¹).val := by
    apply Matrix.ext; intro i j; simp [← hN' i j]
  rw [Matrix.map_mul, hNq, hN'q, Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, smul_smul]
  apply Matrix.ext; intro i j
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [mul_comm]


/-- `N * N' = (d d') • 1` for integral multiples `N = d r`, `N' = d' r⁻¹`. -/
theorem int_mul_eq' (r : RationalGL3) (d d' : ℤ) (N N' : Matrix (Fin 3) (Fin 3) ℤ)
    (hN : ∀ i j, (d : ℚ) * r.val i j = N i j) (hN' : ∀ i j, (d' : ℚ) * (r⁻¹).val i j = N' i j) :
    N * N' = (d * d') • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
  change (N * N').map (Int.castRingHom ℚ) = ((d * d') • (1 : Matrix (Fin 3) (Fin 3) ℤ)).map
    (Int.castRingHom ℚ)
  have hNq : N.map (Int.castRingHom ℚ) = (d : ℚ) • r.val := by
    apply Matrix.ext; intro i j; simp [← hN i j]
  have hN'q : N'.map (Int.castRingHom ℚ) = (d' : ℚ) • (r⁻¹).val := by
    apply Matrix.ext; intro i j; simp [← hN' i j]
  rw [Matrix.map_mul, hNq, hN'q, Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, smul_smul]
  apply Matrix.ext; intro i j
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem rationalFinite_val_eq (r : RationalGL3) (d : ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (hd : (d : ℚ) ≠ 0) (hN : ∀ i j, (d : ℚ) * r.val i j = N i j) :
    (rationalFinite r).val = (algebraMap ℚ FiniteAdeles (1 / d)) •
      (N.map (Int.castRingHom IntegralAdeles)).map integralEmbedding := by
  apply Matrix.ext
  intro i j
  have hr : r.val i j = 1 / d * (N i j : ℚ) := by
    rw [← hN i j]; field_simp
  simp only [rationalFinite, GeneralLinearGroup.map_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, eq_intCast, map_intCast]
  rw [hr, map_mul]
  simp

theorem conj_val (r : RationalGL3) (d : ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (hd : (d : ℚ) ≠ 0) (hN : ∀ i j, (d : ℚ) * r.val i j = N i j)
    (g : FiniteGL) (Gm W : IntMat) (hg : g.val = Gm.map integralEmbedding)
    (hkey : N.map (Int.castRingHom IntegralAdeles) * W = Gm * N.map (Int.castRingHom IntegralAdeles)) :
    ((rationalFinite r)⁻¹ * g * rationalFinite r).val = W.map integralEmbedding := by
  have hR := rationalFinite_val_eq r d N hd hN
  have h1 : (rationalFinite r).val * W.map integralEmbedding = g.val * (rationalFinite r).val := by
    rw [hR, hg, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hkey]
  rw [Units.val_mul, Units.val_mul, mul_assoc, ← h1, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

theorem key_identity (N N' : Matrix (Fin 3) (Fin 3) ℤ) (k : ℤ)
    (hNN : N * N' = k • (1 : Matrix (Fin 3) (Fin 3) ℤ)) (s3 : ℤ) (Mn : ℕ)
    (hMn : (Mn : ℤ) = k * s3) (P : IntMat) :
    N.map (Int.castRingHom IntegralAdeles) *
        (1 + ((s3 : ℤ) : IntegralAdeles) • (N'.map (Int.castRingHom IntegralAdeles) * P *
          N.map (Int.castRingHom IntegralAdeles))) =
      (1 + (Mn : IntegralAdeles) • P) * N.map (Int.castRingHom IntegralAdeles) := by
  set Nz := N.map (Int.castRingHom IntegralAdeles)
  set N'z := N'.map (Int.castRingHom IntegralAdeles)
  have hNNz : Nz * N'z = ((k : ℤ) : IntegralAdeles) • (1 : IntMat) := by
    rw [← Matrix.map_mul, hNN]
    apply Matrix.ext; intro i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hMz : (Mn : IntegralAdeles) = ((s3 : ℤ) : IntegralAdeles) * ((k : ℤ) : IntegralAdeles) := by
    have : ((Mn : ℤ) : IntegralAdeles) = ((k * s3 : ℤ) : IntegralAdeles) := by rw [hMn]
    push_cast at this
    rw [this, mul_comm]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hNNz, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, Matrix.add_mul,
    Matrix.one_mul, Matrix.smul_mul, hMz]


theorem placePrime_placeThree : placePrime placeThree = 3 :=
  placePrime_symm primeThree

theorem reduction_one_add_smul (z : ℤ) (hz : (3 : ℤ) ∣ z) (P : IntMat) :
    (1 + ((z : ℤ) : IntegralAdeles) • P).map integralReduction = 1 := by
  apply Matrix.ext
  intro i j
  have hz0 : integralReduction ((z : ℤ) : IntegralAdeles) = 0 := by
    rw [map_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mpr (by exact_mod_cast hz)
  rw [Matrix.map_apply, Matrix.add_apply, map_add, Matrix.smul_apply, smul_eq_mul, map_mul, hz0,
    zero_mul, add_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem reduction_one_add_natSmul (M : ℕ) (hM : 3 ∣ M) (P : IntMat) :
    (1 + (M : IntegralAdeles) • P).map integralReduction = 1 := by
  have := reduction_one_add_smul (M : ℤ) (by exact_mod_cast hM) P
  simpa using this

/-- Matrix of `g⁻¹ κ` when `κ = g + M • Y`. -/
theorem inv_mul_val_of_add_smul (g κ : GeneralLinearGroup (Fin 3) IntegralAdeles) (M : ℕ)
    (Y : IntMat) (h : κ.val = g.val + (M : IntegralAdeles) • Y) :
    (g⁻¹ * κ).val = 1 + (M : IntegralAdeles) • ((g⁻¹).val * Y) := by
  rw [Units.val_mul, h, Matrix.mul_add, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_smul]

/-- Matrix of `(g⁻¹ κ)⁻¹` when `κ = g + M • Y`. -/
theorem inv_mul_inv_val_of_add_smul (g κ : GeneralLinearGroup (Fin 3) IntegralAdeles) (M : ℕ)
    (Y : IntMat) (h : κ.val = g.val + (M : IntegralAdeles) • Y) :
    ((g⁻¹ * κ)⁻¹).val = 1 + (M : IntegralAdeles) • (-((κ⁻¹).val * Y)) := by
  have hg : g.val = κ.val - (M : IntegralAdeles) • Y := by rw [h]; abel
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hg, Matrix.mul_sub, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_smul, smul_neg, sub_eq_add_neg]

/-- Reduction modulo three of the integral matrix `γ'` agrees with that of `κ1`, so `γ'` lies in
the arithmetic level when `κ1 = δ κ u⁻¹` with `δ`, `κ` in the level and `u ≡ 1`. -/
theorem mem_arithmeticLevel_of_congruent (γ' δ : IntegralGL3)
    (κ u κ1 : GeneralLinearGroup (Fin 3) IntegralAdeles) (Y1 : IntMat) (Mn : ℕ) (h3Mn : 3 ∣ Mn)
    (hκ1 : κ1.val = (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ').val +
      (Mn : IntegralAdeles) • Y1)
    (hκ1def : κ1 = GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) δ * κ * u⁻¹)
    (hredu1 : GeneralLinearGroup.map integralReduction u = 1) (hδ : δ ∈ arithmeticLevel)
    (hκ : GeneralLinearGroup.map integralReduction κ ∈ rowStabilizer) : γ' ∈ arithmeticLevel := by
  let red : GeneralLinearGroup (Fin 3) IntegralAdeles →* GeneralLinearGroup (Fin 3) (ZMod 3) :=
    GeneralLinearGroup.map integralReduction
  let g' := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ'
  let δZ := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) δ
  change reductionThree γ' ∈ rowStabilizer
  have h1 : reductionThree γ' = red g' := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    simp [reductionThree, red, g', GeneralLinearGroup.map_apply]
  have h2 : red g' = red κ1 := by
    apply Units.ext
    change g'.val.map integralReduction = κ1.val.map integralReduction
    rw [hκ1]
    apply Matrix.ext
    intro i j
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.add_apply, map_add, Matrix.smul_apply,
      smul_eq_mul, integralReduction_natCast_mul _ _ h3Mn, add_zero]
  have h3 : red κ1 = red δZ * red κ := by
    rw [hκ1def, map_mul, map_mul, map_inv, hredu1, inv_one, mul_one]
  have h4 : red δZ = reductionThree δ := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    simp [reductionThree, red, δZ, GeneralLinearGroup.map_apply]
  rw [h1, h2, h3, h4]
  exact rowStabilizer.mul_mem hδ hκ

/-- If `w ≡ 1 mod 3dd'` with `w` and `w⁻¹` of the form `1 + Mn • P`, `1 + Mn • Q`, then the
conjugate of `w` by `rf r` lies in the finite level. -/
theorem conj_mem_finiteLevel_of_add_smul (r : RationalGL3) (d : ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (hd : (d : ℚ) ≠ 0) (hN : ∀ i j, (d : ℚ) * r.val i j = N i j)
    (d' : ℤ) (N' : Matrix (Fin 3) (Fin 3) ℤ)
    (hN' : ∀ i j, (d' : ℚ) * (r⁻¹).val i j = N' i j)
    (w : GeneralLinearGroup (Fin 3) IntegralAdeles) (P Q : IntMat) (Mn : ℕ)
    (hMn : Mn = 3 * d.natAbs * d'.natAbs)
    (hw : w.val = 1 + (Mn : IntegralAdeles) • P)
    (hwinv : (w⁻¹).val = 1 + (Mn : IntegralAdeles) • Q) :
    (rationalFinite r)⁻¹ * GeneralLinearGroup.map integralEmbedding w * rationalFinite r ∈
      finiteLevel := by
  let s3 : ℤ := 3 * d.sign * d'.sign
  have hMn_eq : (Mn : ℤ) = (d * d') * s3 := by
    have e1 : (|d| : ℤ) = d * d.sign := by rw [Int.mul_sign_self, Int.natCast_natAbs]
    have e2 : (|d'| : ℤ) = d' * d'.sign := by rw [Int.mul_sign_self, Int.natCast_natAbs]
    rw [hMn]
    push_cast
    rw [e1, e2]
    ring
  have hNN := int_mul_eq' r d d' N N' hN hN'
  have hs3 : (3 : ℤ) ∣ s3 := ⟨d.sign * d'.sign, by ring⟩
  refine mem_finiteLevel_of_integral _
    (1 + ((s3 : ℤ) : IntegralAdeles) • (N'.map (Int.castRingHom IntegralAdeles) *
      (P) * N.map (Int.castRingHom IntegralAdeles)))
    (1 + ((s3 : ℤ) : IntegralAdeles) • (N'.map (Int.castRingHom IntegralAdeles) *
      (Q) * N.map (Int.castRingHom IntegralAdeles))) ?_ ?_ ?_
  · refine conj_val r d N hd hN _ _ _ ?_ (key_identity N N' (d * d') hNN s3 Mn hMn_eq _)
    change w.val.map integralEmbedding = _
    rw [hw]
  · rw [show ((rationalFinite r)⁻¹ * GeneralLinearGroup.map integralEmbedding w *
        rationalFinite r)⁻¹ = (rationalFinite r)⁻¹ * GeneralLinearGroup.map integralEmbedding w⁻¹ *
        rationalFinite r by rw [map_inv]; group]
    refine conj_val r d N hd hN _ _ _ ?_ (key_identity N N' (d * d') hNN s3 Mn hMn_eq _)
    change (w⁻¹).val.map integralEmbedding = _
    rw [hwinv]
  · rw [reduction_one_add_smul s3 hs3, vecMul_one]

/-- Strong approximation for an integral matrix of determinant `≡ 1 mod Mn`: it is the sum of
the image of an element of `GL₃(ℤ)` and `Mn` times an integral matrix. -/
theorem exists_integral_approx (κ1 : GeneralLinearGroup (Fin 3) IntegralAdeles) (Mn : ℕ)
    (hMn0 : Mn ≠ 0) (y2 : IntegralAdeles)
    (hy2 : κ1.val.det = 1 + (Mn : IntegralAdeles) * y2) :
    ∃ (γ' : IntegralGL3) (Y1 : IntMat),
      κ1.val = (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ').val +
        (Mn : IntegralAdeles) • Y1 := by
  classical
  obtain ⟨Z, Y0, hZY⟩ := exists_matrix_approx Mn hMn0 κ1.val
  obtain ⟨y1, hy1⟩ := det_congr Mn Z Y0
  rw [← hZY] at hy1
  have hdvd : (Mn : ℤ) ∣ Z.det - 1 := by
    apply int_dvd_of_eq_mul Mn hMn0 (Z.det - 1) (y2 - y1)
    rw [Int.cast_sub, Int.cast_one]
    linear_combination hy2 - hy1
  have : NeZero Mn := ⟨hMn0⟩
  let Zbar : Matrix.SpecialLinearGroup (Fin 3) (ZMod Mn) :=
    ⟨Z.map (Int.castRingHom (ZMod Mn)), by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
      have h := (ZMod.intCast_eq_intCast_iff_dvd_sub Z.det 1 Mn).mpr (by
        rw [← neg_sub]; exact (dvd_neg).mpr hdvd)
      simpa using h⟩
  obtain ⟨γs, hγs⟩ := StrongApproximation.map_intCast_surjective Mn 3 Zbar
  have hentry : ∀ i j, (Mn : ℤ) ∣ Z i j - (γs : Matrix (Fin 3) (Fin 3) ℤ) i j := by
    intro i j
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (ZMod Mn) =>
      (A : Matrix (Fin 3) (Fin 3) (ZMod Mn)) i j) hγs
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Zbar] at h
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h)
  choose q hq using hentry
  let γ' : IntegralGL3 := ⟨(γs : Matrix (Fin 3) (Fin 3) ℤ),
    ((γs⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ),
    by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one],
    by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]⟩
  let g' := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ'
  let Y1 : IntMat := Y0 + (Matrix.of q).map (Int.castRingHom IntegralAdeles)
  have hκ1 : κ1.val = g'.val + (Mn : IntegralAdeles) • Y1 := by
    rw [hZY]
    apply Matrix.ext
    intro i j
    have hqij : (Z i j : IntegralAdeles) = ((γs : Matrix (Fin 3) (Fin 3) ℤ) i j : IntegralAdeles) +
        (Mn : IntegralAdeles) * (q i j : IntegralAdeles) := by
      have : Z i j = (γs : Matrix (Fin 3) (Fin 3) ℤ) i j + Mn * q i j := by linarith [hq i j]
      rw [this]; push_cast; ring
    have hg'ij : g'.val i j = (((γs : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : IntegralAdeles) := rfl
    have hY1 : Y1 i j = Y0 i j + ((q i j : ℤ) : IntegralAdeles) := rfl
    have hZij : (Z.map (Int.castRingHom IntegralAdeles)) i j = ((Z i j : ℤ) : IntegralAdeles) := rfl
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul, hg'ij, hY1, hZij, hqij]
    ring
  exact ⟨γ', Y1, hκ1⟩

/-- A sign correction in the arithmetic level: for every integral `κ` there is an involution
`δ` of the arithmetic level with `δ κ` of determinant `≡ 1 mod 3`. -/
theorem exists_sign_correction (κ : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    ∃ δ : IntegralGL3, δ ∈ arithmeticLevel ∧ δ * δ = 1 ∧
      integralReduction (GeneralLinearGroup.det
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) δ * κ) : IntegralAdeles) = 1 := by
  classical
  have hunit3 : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  set ρ : ZMod 3 := integralReduction (GeneralLinearGroup.det κ : IntegralAdeles) with hρ
  have hρ0 : ρ ≠ 0 := ((GeneralLinearGroup.det κ).isUnit.map integralReduction).ne_zero
  let ε : ℤ := if ρ = 1 then 1 else -1
  have hε2 : ε * ε = 1 := by
    by_cases h : ρ = 1 <;> simp [ε, h]
  have hερ : (ε : ZMod 3) * ρ = 1 := by
    rcases hunit3 ρ hρ0 with h | h
    · simp [ε, h]
    · have hne : ρ ≠ 1 := by rw [h]; decide
      rw [show ε = -1 from ite_eq_right hne, h]
      norm_num
      rfl
  have hdiag : Matrix.diagonal ![ε, 1, 1] * Matrix.diagonal ![ε, 1, 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hε2]
  let δ : IntegralGL3 := ⟨Matrix.diagonal ![ε, 1, 1], Matrix.diagonal ![ε, 1, 1], hdiag, hdiag⟩
  have hδδ : δ * δ = 1 := Units.ext hdiag
  have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδδ
  have hδ : δ ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree δ).val = lastRow
    funext j
    fin_cases j <;>
      simp [lastRow, reductionThree, δ, vecMul, dotProduct,
        GeneralLinearGroup.map_apply, Matrix.diagonal_apply]
  let δZ := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) δ
  have hδZinv : δZ⁻¹ = δZ := by rw [← map_inv, hδinv]
  let κ0 := δZ * κ
  have hdetκ0 : integralReduction (GeneralLinearGroup.det κ0 : IntegralAdeles) = 1 := by
    have hdetδ : (GeneralLinearGroup.det δZ : IntegralAdeles) = ((ε : ℤ) : IntegralAdeles) := by
      change (δ.val.map (Int.castRingHom IntegralAdeles)).det = _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simp [δ, Matrix.det_diagonal, Fin.prod_univ_three]
    rw [map_mul, Units.val_mul, map_mul, hdetδ, map_intCast, ← hρ, hερ]
  exact ⟨δ, hδ, hδδ, hdetκ0⟩

/-- **Single-coset decomposition.** For every `r ∈ GL₃(ℚ)` (given integral multiples
`N = d r`, `N' = d' r⁻¹`), every element of `finiteLevel` is `rf(γ) · u` with
`γ ∈ rationalLevel`, `u ∈ finiteLevel` and `(rf r)⁻¹ u (rf r) ∈ finiteLevel`. -/
theorem cosetDecomposition_of_multiples (r : RationalGL3)
    (d : ℤ) (hd0 : d ≠ 0) (N : Matrix (Fin 3) (Fin 3) ℤ) (hN : ∀ i j, (d : ℚ) * r.val i j = N i j)
    (d' : ℤ) (hd0' : d' ≠ 0) (N' : Matrix (Fin 3) (Fin 3) ℤ)
    (hN' : ∀ i j, (d' : ℚ) * (r⁻¹).val i j = N' i j)
    (k : FiniteGL) (hk : k ∈ finiteLevel) :
    ∃ γ ∈ rationalLevel, (rationalFinite γ)⁻¹ * k ∈ finiteLevel ∧
      (rationalFinite r)⁻¹ * ((rationalFinite γ)⁻¹ * k) * rationalFinite r ∈ finiteLevel := by
  classical
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.mp hk
  let red : GeneralLinearGroup (Fin 3) IntegralAdeles →* GeneralLinearGroup (Fin 3) (ZMod 3) :=
    GeneralLinearGroup.map integralReduction
  obtain ⟨δ, hδ, hδδ, hdetκ0⟩ := exists_sign_correction κ
  have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδδ
  let δZ := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) δ
  have hδZinv : δZ⁻¹ = δZ := by rw [← map_inv, hδinv]
  let κ0 := δZ * κ
  -- the determinant correction `β`
  let β : IntegralAdelesˣ := GeneralLinearGroup.det κ0
  have hβ3 : integralReduction (β : IntegralAdeles) = 1 := hdetκ0
  obtain ⟨u, hdetu, hredu, U, hredU, hconj⟩ := Dilation.exists_dilation r d N hd hN β hβ3
  let κ1 := κ0 * u⁻¹
  set Mn : ℕ := 3 * d.natAbs * d'.natAbs with hMn
  have hMn0 : Mn ≠ 0 := by
    simp [Mn, hd0, hd0']
  have h3Mn : 3 ∣ Mn := ⟨d.natAbs * d'.natAbs, by rw [hMn]; ring⟩
  -- the determinant of `κ1` is `1`
  have hdet1 : ∃ y2 : IntegralAdeles, κ1.val.det = 1 + (Mn : IntegralAdeles) * y2 := by
    have hdetu' : GeneralLinearGroup.det u = β := Units.ext hdetu
    refine ⟨0, ?_⟩
    rw [mul_zero, add_zero]
    change (GeneralLinearGroup.det κ1 : IntegralAdeles) = 1
    rw [map_mul, map_inv, hdetu', mul_inv_cancel, Units.val_one]
  -- approximation modulo `Mn`
  obtain ⟨y2, hy2⟩ := hdet1
  have approx := exists_integral_approx κ1 Mn hMn0 y2 hy2
  obtain ⟨γ', Y1, hκ1⟩ := approx
  let g' := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ'
  let w0 := g'⁻¹ * κ1
  have hw0 : w0.val = 1 + (Mn : IntegralAdeles) • ((g'⁻¹).val * Y1) :=
    inv_mul_val_of_add_smul g' κ1 Mn Y1 hκ1
  have hw0inv : (w0⁻¹).val = 1 + (Mn : IntegralAdeles) • (-((κ1⁻¹).val * Y1)) :=
    inv_mul_inv_val_of_add_smul g' κ1 Mn Y1 hκ1
  have hγ'lev : γ' ∈ arithmeticLevel :=
    mem_arithmeticLevel_of_congruent γ' δ κ u κ1 Y1 Mn h3Mn hκ1 rfl (Units.ext hredu) hδ hκ
  let γfull : arithmeticLevel := ⟨δ * γ', arithmeticLevel.mul_mem hδ hγ'lev⟩
  refine ⟨rationalInclusion γfull, ⟨γfull, rfl⟩, ?_⟩
  have hrf : rationalFinite (rationalInclusion γfull) =
      GeneralLinearGroup.map integralEmbedding (δZ * g') := by
    rw [show rationalInclusion γfull = GeneralLinearGroup.map (Int.castRingHom ℚ) (δ * γ') from rfl,
      rationalFinite_intCast, map_mul]
  have hfac : (rationalFinite (rationalInclusion γfull))⁻¹ * GeneralLinearGroup.map integralEmbedding κ =
      GeneralLinearGroup.map integralEmbedding (w0 * u) := by
    rw [hrf, ← map_inv, ← map_mul]
    congr 1
    change (δZ * g')⁻¹ * κ = g'⁻¹ * (δZ * κ * u⁻¹) * u
    rw [_root_.mul_inv_rev, hδZinv]
    group
  rw [hfac]
  constructor
  · apply map_mem_finiteLevel_of_reduction_one
    rw [Units.val_mul, Matrix.map_mul, hw0, reduction_one_add_natSmul Mn h3Mn, hredu, one_mul]
  · have hsplit : (rationalFinite r)⁻¹ * GeneralLinearGroup.map integralEmbedding (w0 * u) *
          rationalFinite r =
        ((rationalFinite r)⁻¹ * GeneralLinearGroup.map integralEmbedding w0 * rationalFinite r) *
          GeneralLinearGroup.map integralEmbedding U := by
      rw [← hconj, map_mul]; group
    rw [hsplit]
    refine finiteLevel.mul_mem ?_ (map_mem_finiteLevel_of_reduction_one U hredU)
    exact conj_mem_finiteLevel_of_add_smul r d N hd hN d' N' hN' w0 ((g'⁻¹).val * Y1)
      (-((κ1⁻¹).val * Y1)) Mn hMn hw0 hw0inv

/-- Every rational matrix has a nonzero integral multiple. -/
theorem exists_integral_multiple (A : Matrix (Fin 3) (Fin 3) ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ N : Matrix (Fin 3) (Fin 3) ℤ, ∀ i j, (d : ℚ) * A i j = N i j := by
  classical
  refine ⟨∏ ij : Fin 3 × Fin 3, ((A ij.1 ij.2).den : ℤ), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro ij _
    exact_mod_cast (A ij.1 ij.2).den_nz
  · refine ⟨fun i j => (A i j).num * ∏ ij ∈ Finset.univ.erase (i, j), ((A ij.1 ij.2).den : ℤ),
      fun i j => ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun ij : Fin 3 × Fin 3 => ((A ij.1 ij.2).den : ℤ))
      (Finset.mem_univ (i, j))]
    push_cast
    have h := Rat.mul_den_eq_num (A i j)
    linear_combination (∏ x ∈ Finset.univ.erase (i, j), ((A x.1 x.2).den : ℚ)) * h

/-- The single-coset decomposition for every rational matrix. -/
theorem cosetDecomposition_all (r : RationalGL3) (k : FiniteGL) (hk : k ∈ finiteLevel) :
    ∃ γ ∈ rationalLevel, (rationalFinite γ)⁻¹ * k ∈ finiteLevel ∧
      (rationalFinite r)⁻¹ * ((rationalFinite γ)⁻¹ * k) * rationalFinite r ∈ finiteLevel := by
  obtain ⟨d, hd, N, hN⟩ := exists_integral_multiple r.val
  obtain ⟨d', hd', N', hN'⟩ := exists_integral_multiple (r⁻¹).val
  exact cosetDecomposition_of_multiples r d hd N hN d' hd' N' hN' k hk

end TernaryPeriodPolynomials.HeckeStability.CosetDecomposition
