module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeAbar

@[expose] public section


/-!
# Orientation functionals and the symbol map; covariance (L4)

Formalized by Claude Sonnet 5.5.

`abarL_sub`: `Ā_a x - Ā_b x = Hlin a b (piT x)` for all chains `x` (including the parallel case); `Hlin_act`: covariance of
`Hlin` under `GL₂(ℚ)` of positive determinant; `abarL_bdryMap`: `Ā_ξ ∘ ∂ = -2 ε`; `exists_adm`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeAbar

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeSign (sg sg_mul sg_neg sg_sq_eq sg_pos triangle_sum core Hv dt2)

theorem vectorAction_apply (h : GL2) (w : Fin 2 → ℚ) : (vectorAction h) w = h.val.mulVec w := by
  simp [vectorAction]

theorem sg_posmul {r : ℝ} (x : ℝ) (hr : 0 < r) : sg (r * x) = sg x := by
  by_cases hx : 0 < x
  · rw [sg_pos hx, sg_pos (mul_pos hr hx)]
  · have : ¬ 0 < r * x := fun h => hx (pos_of_mul_pos_right h hr.le)
    simp [sg, hx, this]

theorem Hv_act (h : GL2) (hd : 0 < ((h.val.det : ℚ) : ℝ)) (a b c : Fin 2 → ℝ) :
    Hv a b (actG h c) = Hv (actG h⁻¹ a) (actG h⁻¹ b) c := by
  obtain ⟨a', rfl⟩ : ∃ a', a = actG h a' := ⟨actG h⁻¹ a, (actG_inv h a).symm⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = actG h b' := ⟨actG h⁻¹ b, (actG_inv h b).symm⟩
  rw [actG_inv', actG_inv']
  unfold Hv
  rw [dt2_actG, dt2_actG, dt2_actG, sg_posmul _ hd,
    show ((h.val.det : ℚ) : ℝ) * dt2 c a' * (((h.val.det : ℚ) : ℝ) * dt2 c b') =
      (((h.val.det : ℚ) : ℝ) * ((h.val.det : ℚ) : ℝ)) * (dt2 c a' * dt2 c b') by ring,
    sg_posmul _ (mul_pos hd hd)]

theorem Hl_act {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (h : GL2) (hd : 0 < ((h.val.det : ℚ) : ℝ))
    (L : RationalLine2) :
    Hl a b (lineAction h L) = Hl (actG h⁻¹ a) (actG h⁻¹ b) L := by
  have hmem : h.val.mulVec (gen L) ∈ (lineAction h L).val := by
    show _ ∈ L.val.map (vectorAction h).toLinearMap
    refine ⟨gen L, gen_mem L, ?_⟩
    simp [vectorAction_apply]
  have hne : h.val.mulVec (gen L) ≠ 0 := by
    intro h0
    apply gen_ne L
    have := congrArg (fun v => h⁻¹.val.mulVec v) h0
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  rw [Hl_eq ha hb _ _ hmem hne, ← actG_cast, Hv_act h hd]
  rfl

theorem Hlin_act {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (h : GL2) (hd : 0 < ((h.val.det : ℚ) : ℝ))
    (c : Divisors) :
    Hlin a b (divisorAction h c) = Hlin (actG h⁻¹ a) (actG h⁻¹ b) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd' => simp only [map_add, hc, hd']
  | single L q => rw [divisorAction_single, Hlin_single, Hlin_single, Hl_act ha hb h hd]

theorem exists_smul_of_dt2 {a b : Fin 2 → ℝ} (hb : b ≠ 0) (h : dt2 a b = 0) : ∃ r : ℝ, a = r • b := by
  have h' : a 0 * b 1 = a 1 * b 0 := by simp [dt2] at h; linarith
  by_cases b0 : b 0 = 0
  · have b1 : b 1 ≠ 0 := by
      intro b1; apply hb; ext i; fin_cases i <;> simp [b0, b1]
    refine ⟨a 1 / b 1, ?_⟩
    ext i; fin_cases i
    · simp [b0] at h' ⊢
      rcases h' with h' | h'
      · exact h'
      · exact absurd h' b1
    · simp; field_simp
  · refine ⟨a 0 / b 0, ?_⟩
    ext i; fin_cases i
    · simp; field_simp
    · simp; field_simp; linarith

theorem Adm.ne_zero {a : Fin 2 → ℝ} (ha : Adm a) : a ≠ 0 := by
  intro h0
  have := ha ![1, 0] (by intro h; have := congrFun h 0; simp at this)
  apply this
  simp [dt2, h0]

theorem Hl_par {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (hab : dt2 a b = 0) :
    ∃ r : ℝ, ∀ L, Hl a b L = r := by
  obtain ⟨r, hr⟩ := exists_smul_of_dt2 hb.ne_zero hab
  have hr0 : r ≠ 0 := by
    intro h0; apply ha.ne_zero; rw [hr, h0, zero_smul]
  refine ⟨sg r, fun L => ?_⟩
  have hw := hb (gen L) (gen_ne L)
  unfold Hl Hv
  rw [hab, hr]
  have e : dt2 (castV (gen L)) (r • b) = r * dt2 (castV (gen L)) b := by simp [dt2]; ring
  rw [e, show r * dt2 (castV (gen L)) b * dt2 (castV (gen L)) b =
    r * (dt2 (castV (gen L)) b * dt2 (castV (gen L)) b) by ring,
    sg_mul hr0 (mul_self_ne_zero.mpr hw), sg_pos (mul_self_pos.mpr hw)]
  simp [sg]

theorem Hlin_par {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (hab : dt2 a b = 0) (c : Divisors)
    (hc : augmentation c = 0) : Hlin a b c = 0 := by
  obtain ⟨r, hr⟩ := Hl_par ha hb hab
  have key : ∀ c : Divisors, Hlin a b c = r * augmentation c := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]; push_cast; ring
    | single L q => rw [Hlin_single, hr, augmentation_single, Rat.smul_def]; ring
  rw [key, hc]; simp

theorem abarOTE_scale (ξ : Fin 2 → ℝ) {r : ℝ} (hr : r ≠ 0) (q : OTE) :
    abarOTE (r • ξ) q = abarOTE ξ q := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [abarOTE_smul, abarOTE_smul]
  have e : ∀ j : Fin 2, dt2 (colR γ j) (r • ξ) = r * dt2 (colR γ j) ξ := by
    intro j; simp [dt2]; ring
  rw [e 0, e 1, show r * dt2 (colR γ 0) ξ * (r * dt2 (colR γ 1) ξ) =
    (r * r) * (dt2 (colR γ 0) ξ * dt2 (colR γ 1) ξ) by ring, sg_posmul _ (mul_self_pos.mpr hr)]

theorem abarL_par {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (hab : dt2 a b = 0) : abarL a = abarL b := by
  obtain ⟨r, hr⟩ := exists_smul_of_dt2 hb.ne_zero hab
  have hr0 : r ≠ 0 := by
    intro h0; apply ha.ne_zero; rw [hr, h0, zero_smul]
  refine MonoidAlgebra.lhom_ext' fun q => LinearMap.ext_ring ?_
  change abarL a (MonoidAlgebra.single q 1) = abarL b (MonoidAlgebra.single q 1)
  rw [abarL_single, abarL_single, hr, abarOTE_scale _ hr0]

/-- **Difference of two orientation functionals is a symbol functional.** -/
theorem abarL_sub {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (x : PE) :
    abarL a x - abarL b x = Hlin a b (piT.hom x).val := by
  by_cases hab : dt2 a b = 0
  · rw [abarL_par ha hb hab, sub_self]
    exact (Hlin_par ha hb hab _ (piT.hom x).property).symm
  · have key : abarL a - abarL b = (Hlin a b).comp ((Submodule.subtype _).comp piT.hom.toLinearMap) := by
      refine MonoidAlgebra.lhom_ext' fun q => LinearMap.ext_ring ?_
      simp only [MonoidAlgebra.lsingle_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      rw [abarL_single, abarL_single]
      change _ = Hlin a b (piT.hom (MonoidAlgebra.single q 1)).val
      rw [piT_single]
      simp only [one_smul]
      rw [delta_formula ha hb hab]
    exact LinearMap.congr_fun key x

/-- The boundary map computes the augmentation through the orientation functional. -/
theorem abarL_bdryMap {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (u : P0) :
    abarL ξ (bdryMap.hom u) = -2 * ((epsMap.hom u : ℚ) : ℝ) := by
  induction u using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]; push_cast; ring
  | single t r =>
    rw [bdryMap_single, map_smul, abarL_bdryV hξ, epsMap_single, Rat.smul_def]
    ring

theorem exists_adm : ∃ ξ : Fin 2 → ℝ, Adm ξ := by
  refine ⟨![1, Real.sqrt 2], fun v hv h => ?_⟩
  have h' : (v 0 : ℝ) * Real.sqrt 2 = v 1 := by
    simp [dt2, castV] at h; linarith
  by_cases h0 : v 0 = 0
  · apply hv
    have : (v 1 : ℝ) = 0 := by rw [← h', h0]; simp
    ext i; fin_cases i
    · simpa using h0
    · simpa using this
  · apply irrational_sqrt_two
    refine ⟨v 1 / v 0, ?_⟩
    have : (v 0 : ℝ) ≠ 0 := by exact_mod_cast h0
    push_cast
    field_simp
    linarith

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeAbar
