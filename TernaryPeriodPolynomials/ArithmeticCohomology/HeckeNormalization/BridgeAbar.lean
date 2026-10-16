module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeSign
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeInterface

@[expose] public section


/-!
# Orientation functionals on the dual Farey tree (L4)

Formalized by Claude Sonnet 5.5.

For a vector `ξ ∈ ℝ²` not parallel to any rational vector (`Adm ξ`), the linear functional `abarL ξ : ℚ[OTE] → ℝ` of the
sign of the position of `ξ` relative to the two cusps of an oriented dual edge.  `abarL_bdryV`: it takes the value `-2` on the
boundary of every Farey triangle.  `delta_formula`: the difference of two such functionals is a functional of the symbol
(`Hlin`), by the Plücker identity of `BridgeSign.core`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeAbar

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeSign (sg sg_mul sg_neg sg_sq_eq sg_pos triangle_sum core Hv dt2)

/-- The real matrix of an element of `GL₂(ℚ)`. -/
def Mq (h : GL2) : Matrix (Fin 2) (Fin 2) ℝ := (Rat.castHom ℝ).mapMatrix h.val

/-- The action of `GL₂(ℚ)` on `ℝ²`. -/
def actG (h : GL2) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ := (Mq h).mulVec ξ

theorem Mq_mul (h k : GL2) : Mq (h * k) = Mq h * Mq k := by
  simp [Mq, Units.val_mul, map_mul]

theorem Mq_one : Mq 1 = 1 := by simp [Mq]

theorem actG_mul (h k : GL2) (ξ : Fin 2 → ℝ) : actG (h * k) ξ = actG h (actG k ξ) := by
  simp only [actG, Mq_mul, Matrix.mulVec_mulVec]

theorem actG_one (ξ : Fin 2 → ℝ) : actG 1 ξ = ξ := by simp [actG, Mq_one]

theorem actG_inv (h : GL2) (ξ : Fin 2 → ℝ) : actG h (actG h⁻¹ ξ) = ξ := by
  rw [← actG_mul, mul_inv_cancel, actG_one]

theorem actG_inv' (h : GL2) (ξ : Fin 2 → ℝ) : actG h⁻¹ (actG h ξ) = ξ := by
  rw [← actG_mul, inv_mul_cancel, actG_one]

theorem det_Mq (h : GL2) : (Mq h).det = ((h.val.det : ℚ) : ℝ) := by
  simp only [Mq]; exact (RingHom.map_det (Rat.castHom ℝ) h.val).symm

theorem dt2_actG (h : GL2) (u v : Fin 2 → ℝ) :
    dt2 (actG h u) (actG h v) = ((h.val.det : ℚ) : ℝ) * dt2 u v := by
  simp only [dt2, actG, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Mq,
    Matrix.det_fin_two] at *
  push_cast
  simp
  ring

/-- Real vector from a rational vector. -/
def castV (v : Fin 2 → ℚ) : Fin 2 → ℝ := fun i => (v i : ℝ)

theorem actG_cast (h : GL2) (u : Fin 2 → ℚ) : actG h (castV u) = castV (h.val.mulVec u) := by
  ext i
  simp [actG, Mq, castV, Matrix.mulVec, dotProduct]

theorem det_ne_zero_real (h : GL2) : ((h.val.det : ℚ) : ℝ) ≠ 0 := by
  have : h.val.det ≠ 0 := by
    have := h.det.ne_zero
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  exact_mod_cast this

/-- Admissible reference vectors: nonparallel to every nonzero rational vector. -/
def Adm (ξ : Fin 2 → ℝ) : Prop :=
  ∀ v : Fin 2 → ℚ, v ≠ 0 → dt2 (castV v) ξ ≠ 0

theorem Adm.act {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (h : GL2) : Adm (actG h ξ) := by
  intro v hv
  set u := h⁻¹.val.mulVec v with hu
  have hvu : h.val.mulVec u = v := by
    rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv
    rw [← hvu, h0, Matrix.mulVec_zero]
  have : castV v = actG h (castV u) := by rw [actG_cast, hvu]
  rw [this, dt2_actG]
  exact mul_ne_zero (det_ne_zero_real h) (hξ u hu0)

/-- The `j`-th column of an integral matrix, as a real vector. -/
def colR (γ : IntegralGL) (j : Fin 2) : Fin 2 → ℝ := fun i => ((γ.val i j : ℤ) : ℝ)

theorem colR_mul (δ γ : IntegralGL) (j : Fin 2) :
    colR (δ * γ) j = actG (BinaryModularSymbol.integral δ) (colR γ j) := by
  ext i
  simp [colR, actG, Mq, BinaryModularSymbol.integral, Matrix.GeneralLinearGroup.map, Matrix.mulVec, dotProduct,
    Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_integral (δ : IntegralGL) :
    ((BinaryModularSymbol.integral δ).val.det : ℚ) = detQ δ := by
  have h : (BinaryModularSymbol.integral δ).val.det = (δ.val.det : ℚ) := by
    change (δ.val.map (Int.castRingHom ℚ)).det = _
    exact (RingHom.map_det (Int.castRingHom ℚ) δ.val).symm
  rw [h]
  simp [detQ, Matrix.GeneralLinearGroup.val_det_apply]

theorem detQ_real_sq (δ : IntegralGL) : ((detQ δ : ℚ) : ℝ) * ((detQ δ : ℚ) : ℝ) = 1 := by
  have := detQ_mul_self δ
  exact_mod_cast this

/-- The value of the orientation functional on an oriented dual edge. -/
def abarOTE (ξ : Fin 2 → ℝ) (q : OTE) : ℝ :=
  - sg (dt2 (colR (Classical.choose (ote_transitive q)) 0) ξ *
        dt2 (colR (Classical.choose (ote_transitive q)) 1) ξ)

theorem abarOTE_smul (ξ : Fin 2 → ℝ) (γ : IntegralGL) :
    abarOTE ξ (γ • p0) = - sg (dt2 (colR γ 0) ξ * dt2 (colR γ 1) ξ) := by
  set γ0 := Classical.choose (ote_transitive (γ • p0)) with hγ0
  have h0 : γ0 • p0 = γ • p0 := Classical.choose_spec (ote_transitive (γ • p0))
  have hs : γ0⁻¹ * γ ∈ MulAction.stabilizer IntegralGL p0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← h0, inv_smul_smul]
  have hγ : γ = γ0 * (γ0⁻¹ * γ) := by group
  unfold abarOTE
  rw [← hγ0]
  set s := γ0⁻¹ * γ with hs'
  rw [hγ]
  rcases stab_p0_entries s hs with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  all_goals
    congr 2
    simp only [dt2, colR, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d]
    push_cast
    ring

theorem colR_eq_castV (γ : IntegralGL) (j : Fin 2) :
    colR γ j = castV (fun i => ((γ.val i j : ℤ) : ℚ)) := by
  ext i; simp [colR, castV]

theorem col_ne_zero (γ : IntegralGL) (j : Fin 2) : (fun i => ((γ.val i j : ℤ) : ℚ)) ≠ 0 := by
  intro h
  have h0 : ∀ i, γ.val i j = 0 := fun i => by
    have := congrFun h i
    simpa using this
  have hdet : γ.val.det = 0 := by
    have a0 := h0 0
    have a1 := h0 1
    fin_cases j <;> simp_all [Matrix.det_fin_two]
  have := γ.det.ne_zero
  simp [Matrix.GeneralLinearGroup.val_det_apply, hdet] at this

theorem colR_adm' {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (γ : IntegralGL) (j : Fin 2) :
    dt2 (colR γ j) ξ ≠ 0 := by
  rw [colR_eq_castV]; exact hξ _ (col_ne_zero γ j)

theorem colR_adm {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (γ : IntegralGL) (j : Fin 2) :
    dt2 (colR γ j) ξ ≠ 0 := by
  rw [colR_eq_castV]; exact hξ _ (col_ne_zero γ j)

theorem abarOTE_equiv (ξ : Fin 2 → ℝ) (δ : IntegralGL) (q : OTE) :
    abarOTE ξ (δ • q) = abarOTE (actG (BinaryModularSymbol.integral δ⁻¹) ξ) q := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [← mul_smul, abarOTE_smul, abarOTE_smul, colR_mul, colR_mul]
  have key : ∀ j : Fin 2, dt2 (actG (BinaryModularSymbol.integral δ) (colR γ j)) ξ =
      ((detQ δ : ℚ) : ℝ) * dt2 (colR γ j) (actG (BinaryModularSymbol.integral δ⁻¹) ξ) := by
    intro j
    have h1 : ξ = actG (BinaryModularSymbol.integral δ) (actG (BinaryModularSymbol.integral δ⁻¹) ξ) := by
      rw [map_inv, actG_inv]
    conv_lhs => rw [h1]
    rw [dt2_actG, det_integral]
  rw [key 0, key 1]
  have : ((detQ δ : ℚ) : ℝ) * dt2 (colR γ 0) (actG (BinaryModularSymbol.integral δ⁻¹) ξ) *
      (((detQ δ : ℚ) : ℝ) * dt2 (colR γ 1) (actG (BinaryModularSymbol.integral δ⁻¹) ξ)) =
      dt2 (colR γ 0) (actG (BinaryModularSymbol.integral δ⁻¹) ξ) *
        dt2 (colR γ 1) (actG (BinaryModularSymbol.integral δ⁻¹) ξ) := by
    have := detQ_real_sq δ
    linear_combination (dt2 (colR γ 0) (actG (BinaryModularSymbol.integral δ⁻¹) ξ) *
        dt2 (colR γ 1) (actG (BinaryModularSymbol.integral δ⁻¹) ξ)) * this
  rw [this]

theorem colR_sOne0 (γ : IntegralGL) : colR (γ * sOne) 0 = colR γ 0 := by
  ext i
  simp [colR, sOne, colGL_val_zero, e1, e2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem colR_sOne1 (γ : IntegralGL) : colR (γ * sOne) 1 = - colR γ 1 := by
  ext i
  simp [colR, sOne, colGL_val_one, e1, e2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem dt2_neg_left (u v : Fin 2 → ℝ) : dt2 (-u) v = - dt2 u v := by simp [dt2]; ring

theorem abarOTE_swap {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (q : OTE) : abarOTE ξ q.swap = - abarOTE ξ q := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  have : (γ • p0).swap = (γ * sOne) • p0 := by rw [OTE.swap_smul, mul_smul, sOne_smul_p0]
  rw [this, abarOTE_smul, abarOTE_smul, colR_sOne0, colR_sOne1, dt2_neg_left]
  have h0 := colR_adm hξ γ 0
  have h1 := colR_adm hξ γ 1
  rw [mul_neg, sg_neg (mul_ne_zero h0 h1), neg_neg]

/-- The orientation functional, extended linearly to `ℚ[OTE]`. -/
def abarL (ξ : Fin 2 → ℝ) : PE →ₗ[ℚ] ℝ :=
  Finsupp.linearCombination ℚ (abarOTE ξ) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem abarL_single (ξ : Fin 2 → ℝ) (q : OTE) (r : ℚ) :
    abarL ξ (MonoidAlgebra.single q r) = r • abarOTE ξ q := by
  simp [abarL]

theorem abarL_equiv (ξ : Fin 2 → ℝ) (δ : IntegralGL) (x : PE) :
    abarL ξ (PE.ρ δ x) = abarL (actG (BinaryModularSymbol.integral δ⁻¹) ξ) x := by
  have key : (abarL ξ).comp (PE.ρ δ) = abarL (actG (BinaryModularSymbol.integral δ⁻¹) ξ) := by
    refine MonoidAlgebra.lhom_ext' fun q => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
    change abarL ξ (PE.ρ δ (MonoidAlgebra.single q 1)) = _
    rw [Representation.ofMulAction_single, abarL_single, abarL_single, abarOTE_equiv]
  exact LinearMap.congr_fun key x

theorem adm_e1 {ξ : Fin 2 → ℝ} (hξ : Adm ξ) : dt2 (castV ![1, 0]) ξ ≠ 0 :=
  hξ _ (by intro h; have := congrFun h 0; simp at this)

theorem adm_e2 {ξ : Fin 2 → ℝ} (hξ : Adm ξ) : dt2 (castV ![0, 1]) ξ ≠ 0 :=
  hξ _ (by intro h; have := congrFun h 1; simp at this)

theorem adm_e12 {ξ : Fin 2 → ℝ} (hξ : Adm ξ) : dt2 (castV ![1, 1]) ξ ≠ 0 :=
  hξ _ (by intro h; have := congrFun h 0; simp at this)

theorem prod_one (ξ : Fin 2 → ℝ) :
    dt2 (colR 1 0) ξ * dt2 (colR 1 1) ξ = -(ξ 0 * ξ 1) := by
  simp [dt2, colR]; ring

theorem prod_rho (ξ : Fin 2 → ℝ) :
    dt2 (colR rho 0) ξ * dt2 (colR rho 1) ξ = -(ξ 0 * (ξ 0 - ξ 1)) := by
  simp only [dt2, colR, rho, colGL_val_zero, colGL_val_one, e2, e12, Pi.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_neg, Int.cast_one, Int.cast_zero]
  ring

theorem prod_rho2 (ξ : Fin 2 → ℝ) :
    dt2 (colR rho2 0) ξ * dt2 (colR rho2 1) ξ = ξ 1 * (ξ 0 - ξ 1) := by
  simp only [dt2, colR, rho2, colGL_val_zero, colGL_val_one, e1, e12, Pi.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_neg, Int.cast_one, Int.cast_zero]
  ring

theorem abar_triplus {ξ : Fin 2 → ℝ} (hξ : Adm ξ) :
    abarOTE ξ p0 + abarOTE ξ (rho • p0) + abarOTE ξ (rho2 • p0) = 1 := by
  have h1 := adm_e1 hξ
  have h2 := adm_e2 hξ
  have h12 := adm_e12 hξ
  have a0 : abarOTE ξ p0 = - sg (dt2 (colR 1 0) ξ * dt2 (colR 1 1) ξ) := by
    simpa using abarOTE_smul ξ 1
  rw [a0, abarOTE_smul, abarOTE_smul, prod_one, prod_rho, prod_rho2]
  have x0 : (ξ 0) ≠ 0 := by
    intro h; apply h2; simp [dt2, castV, h]
  have y0 : (ξ 1) ≠ 0 := by
    intro h; apply h1; simp [dt2, castV, h]
  have xy : ξ 0 - ξ 1 ≠ 0 := by
    intro h; apply h12; simp [dt2, castV]; linarith
  have t := BridgeSign.triangle_sum (ξ 0) (ξ 1) x0 y0 xy
  have hxy1 : ξ 1 * (ξ 0 - ξ 1) = -(ξ 1 * (ξ 1 - ξ 0)) := by ring
  have s0 := sg_neg (mul_ne_zero x0 y0)
  have s1 := sg_neg (mul_ne_zero x0 xy)
  rw [s0, s1, neg_neg, neg_neg]
  have s2 : sg (ξ 1 * (ξ 0 - ξ 1)) = - sg (ξ 1 * (ξ 1 - ξ 0)) := by
    rw [hxy1]; exact sg_neg (mul_ne_zero y0 (by intro h; apply xy; linarith))
  rw [s2]
  linarith

theorem abarL_bdryV {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (t : Tri) : abarL ξ (bdryV t) = -2 := by
  obtain ⟨g, rfl⟩ := exists_smul_triPlus t
  unfold bdryV
  rw [sum_nbF (fun q => (MonoidAlgebra.single q.swap (1 : ℚ) - MonoidAlgebra.single q (1 : ℚ) : PE)) g]
  have hξ' := hξ.act (BinaryModularSymbol.integral g⁻¹)
  have key : ∀ x : OTE, abarL ξ (MonoidAlgebra.single (g • x).swap (1 : ℚ) - MonoidAlgebra.single (g • x) (1 : ℚ)) =
      -2 * abarOTE (actG (BinaryModularSymbol.integral g⁻¹) ξ) x := by
    intro x
    rw [map_sub, abarL_single, abarL_single, abarOTE_swap hξ, abarOTE_equiv]
    simp only [one_smul]
    ring
  have e1 : (g * rho) • p0 = g • (rho • p0) := mul_smul _ _ _
  have e2 : (g * rho2) • p0 = g • (rho2 • p0) := mul_smul _ _ _
  rw [map_add, map_add, e1, e2, key, key, key]
  have := abar_triplus hξ'
  linarith

/-- A fixed nonzero rational vector on a rational line. -/
def gen (L : RationalLine2) : Fin 2 → ℚ :=
  rationalVector (Classical.choose (rationalLine_primitive_generator L))

theorem gen_ne (L : RationalLine2) : gen L ≠ 0 :=
  (Classical.choose_spec (rationalLine_primitive_generator L)).2.1

theorem gen_mem (L : RationalLine2) : gen L ∈ L.val := by
  rw [← (Classical.choose_spec (rationalLine_primitive_generator L)).2.2]
  exact Submodule.subset_span rfl

/-- The side function `H_{a,b}` on a rational line. -/
def Hl (a b : Fin 2 → ℝ) (L : RationalLine2) : ℝ := Hv a b (castV (gen L))

theorem Hv_smul (a b c : Fin 2 → ℝ) (q : ℝ) (hq : q ≠ 0) (ha : dt2 c a ≠ 0) (hb : dt2 c b ≠ 0) :
    Hv a b (q • c) = Hv a b c := by
  have e1 : dt2 (q • c) a = q * dt2 c a := by simp [dt2]; ring
  have e2 : dt2 (q • c) b = q * dt2 c b := by simp [dt2]; ring
  unfold Hv
  rw [e1, e2, show q * dt2 c a * (q * dt2 c b) = (q * q) * (dt2 c a * dt2 c b) by ring,
    sg_mul (mul_ne_zero hq hq) (mul_ne_zero ha hb), sg_pos (mul_self_pos.mpr hq)]
  ring

theorem Hl_eq {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (L : RationalLine2) (w : Fin 2 → ℚ)
    (hw : w ∈ L.val) (hw0 : w ≠ 0) : Hl a b L = Hv a b (castV w) := by
  have hdim : Module.finrank ℚ L.val = 1 := L.property
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q • gen L = w := by
    have := (finrank_eq_one_iff_of_nonzero' (⟨gen L, gen_mem L⟩ : L.val) (by
      intro h; apply gen_ne L; simpa using congrArg Subtype.val h)).mp hdim ⟨w, hw⟩
    obtain ⟨q, hq⟩ := this
    exact ⟨q, by simpa using congrArg Subtype.val hq⟩
  have hq0 : q ≠ 0 := by
    intro h; apply hw0; rw [← hq, h, zero_smul]
  have hc : castV w = (q : ℝ) • castV (gen L) := by
    rw [← hq]; ext i; simp [castV]
  unfold Hl
  rw [hc]
  exact (Hv_smul a b _ (q : ℝ) (by exact_mod_cast hq0) (ha (gen L) (gen_ne L)) (hb (gen L) (gen_ne L))).symm
/-- Linear extension of `Hl` to divisors. -/
def Hlin (a b : Fin 2 → ℝ) : Divisors →ₗ[ℚ] ℝ := Finsupp.linearCombination ℚ (Hl a b)

theorem Hlin_single (a b : Fin 2 → ℝ) (L : RationalLine2) (r : ℚ) :
    Hlin a b (Finsupp.single L r) = r • Hl a b L := by
  simp [Hlin]

theorem Hl_gamma {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (γ : IntegralGL) (j : Fin 2) :
    Hl a b (augmentedLine γ j.castSucc) = Hv a b (colR γ j) := by
  have hg := col_isGen γ j
  have hmem : (fun i => ((γ.val i j : ℤ) : ℚ)) ∈ (augmentedLine γ j.castSucc).val := by
    rw [← hg.2]; exact Submodule.subset_span rfl
  rw [Hl_eq ha hb _ _ hmem (col_ne_zero γ j), colR_eq_castV]

theorem sg_detQ (γ : IntegralGL) : sg ((detQ γ : ℚ) : ℝ) = ((detQ γ : ℚ) : ℝ) := by
  have h := detQ_mul_self γ
  have : detQ γ = 1 ∨ detQ γ = -1 := by
    have : (detQ γ - 1) * (detQ γ + 1) = 0 := by linarith [h]
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  rcases this with h1 | h1
  · rw [h1]; simp [sg]
  · rw [h1]; simp [sg]

theorem dt2_cols (γ : IntegralGL) : dt2 (colR γ 0) (colR γ 1) = ((detQ γ : ℚ) : ℝ) := by
  have : (detQ γ : ℚ) = (γ.val.det : ℚ) := by
    simp [detQ, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this, Matrix.det_fin_two]
  simp [dt2, colR]; ring

/-- **The difference identity.** For admissible, nonparallel `a, b`: the difference of the orientation
functionals on an oriented dual edge is the `H_{a,b}`-boundary of its symbol. -/
theorem delta_formula {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (hab : dt2 a b ≠ 0) (q : OTE) :
    abarOTE a q - abarOTE b q = Hlin a b (edgeSym q).val := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [abarOTE_smul, abarOTE_smul, edgeSym_apply, reference_eq, stD_symbol]
  have e1 : (γ • cusp1) = augmentedLine γ (0 : Fin 2).castSucc := smul_cusp1 γ
  have e2 : (γ • cusp2) = augmentedLine γ (1 : Fin 2).castSucc := smul_cusp2 γ
  simp only [Submodule.coe_smul, symbol_val, map_smul, map_sub, Hlin_single, e1, e2]
  rw [Hl_gamma ha hb, Hl_gamma ha hb]
  have hc := core (colR γ 0) (colR γ 1) a b (by rw [dt2_cols]; exact_mod_cast detQ_ne_zero γ) hab
    (colR_adm' ha γ 0) (colR_adm' ha γ 1) (colR_adm' hb γ 0) (colR_adm' hb γ 1)
  rw [dt2_cols, sg_detQ] at hc
  simp only [one_smul]
  rw [Rat.smul_def]
  linear_combination hc

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeAbar
