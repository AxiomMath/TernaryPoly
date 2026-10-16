module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Basic
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralRationals

@[expose] public section


/-!
# Central character of the adelic lift: the sign homomorphism on ideles

Every idele `z` decomposes uniquely as `q · t · w` with `q ∈ ℚˣ`, `t ∈ ℝˣ`, `w ∈ Ẑˣ` and
`w ≡ 1 (mod 3)`.  The sign of `t` is a group homomorphism `𝔸ˣ → ℤˣ`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

section Scalar

variable {R : Type*} [CommRing R]

theorem scalar_val_apply (u : Rˣ) (i j : Fin 2) :
    (GeneralLinearGroup.scalar (Fin 2) u : GeneralLinearGroup (Fin 2) R).val i j =
      if i = j then u.val else 0 := by
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem scalar_injective :
    Function.Injective
      (⇑(GeneralLinearGroup.scalar (Fin 2) : Rˣ →* GeneralLinearGroup (Fin 2) R)) := by
  intro u v h
  apply Units.ext
  have := congrArg (fun g : GeneralLinearGroup (Fin 2) R => g.val 0 0) h
  simpa [scalar_val_apply] using this

theorem map_scalar {S : Type*} [CommRing S] (f : R →+* S) (u : Rˣ) :
    GeneralLinearGroup.map f (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom u) := by
  apply Units.ext
  ext i j
  change f ((GeneralLinearGroup.scalar (Fin 2) u).val i j) = _
  rw [scalar_val_apply, scalar_val_apply]
  by_cases h : i = j <;> simp [h]

end Scalar

/-- The rational scalar ideles. -/
def ratU : ℚˣ →* Adelesˣ := Units.map rationalAdele.toMonoidHom

/-- The archimedean scalar ideles. -/
def infU : ℝˣ →* Adelesˣ := Units.map (MonoidHom.inl ℝ FiniteAdeles)

/-- The finite scalar ideles. -/
def finU : FiniteAdelesˣ →* Adelesˣ := Units.map (MonoidHom.inr ℝ FiniteAdeles)

/-- Integral units as finite ideles. -/
def intU : IntegralAdelesˣ →* FiniteAdelesˣ := Units.map integralEmbedding.toMonoidHom

/-- The idele `q · t · w`. -/
def ideleOf (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ) : Adelesˣ :=
  ratU q * (infU t * finU (intU w))

theorem ratGL_scalar (q : ℚˣ) :
    ratGL (GeneralLinearGroup.scalar (Fin 2) q) =
      GeneralLinearGroup.scalar (Fin 2) (ratU q) :=
  map_scalar rationalAdele q

theorem infGL_scalar (t : ℝˣ) :
    infGL (GeneralLinearGroup.scalar (Fin 2) t) =
      GeneralLinearGroup.scalar (Fin 2) (infU t) := by
  rw [infGL_apply]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h1 : (atInfinity (GeneralLinearGroup.scalar (Fin 2) t)).val i j =
      ((GeneralLinearGroup.scalar (Fin 2) t).val i j, (1 : BinaryFiniteGL).val i j) := rfl
  rw [h1, scalar_val_apply, scalar_val_apply]
  by_cases h : i = j <;> simp [h, infU, Prod.ext_iff]

theorem finGL_scalar (v : FiniteAdelesˣ) :
    finGL (GeneralLinearGroup.scalar (Fin 2) v) =
      GeneralLinearGroup.scalar (Fin 2) (finU v) := by
  rw [finGL_apply]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h1 : (atFinite (GeneralLinearGroup.scalar (Fin 2) v)).val i j =
      ((1 : BinaryRealGL).val i j, (GeneralLinearGroup.scalar (Fin 2) v).val i j) := rfl
  rw [h1, scalar_val_apply, scalar_val_apply]
  by_cases h : i = j <;> simp [h, finU, Prod.ext_iff]

theorem intGL_scalar (w : IntegralAdelesˣ) :
    intGL (GeneralLinearGroup.scalar (Fin 2) w) =
      GeneralLinearGroup.scalar (Fin 2) (intU w) :=
  map_scalar integralEmbedding w

theorem scalar_ideleOf (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ) :
    ratGL (GeneralLinearGroup.scalar (Fin 2) q) *
      (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
        finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w))) =
      GeneralLinearGroup.scalar (Fin 2) (ideleOf q t w) := by
  rw [ratGL_scalar, infGL_scalar, intGL_scalar, finGL_scalar, ideleOf, map_mul, map_mul]

theorem scalar_intGL_mem_levelGroup (w : IntegralAdelesˣ)
    (hw : integralReduction w.val = 1) :
    intGL (GeneralLinearGroup.scalar (Fin 2) w) ∈ levelGroup := by
  rw [mem_levelGroup_iff]
  refine ⟨GeneralLinearGroup.scalar (Fin 2) w, rfl, ?_⟩
  have hred : redGL (GeneralLinearGroup.scalar (Fin 2) w) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map integralReduction.toMonoidHom w) :=
    map_scalar integralReduction w
  rw [hred]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, scalar_val_apply, hw]

/-! ### Existence and uniqueness of the decomposition -/

/-- `z = q · t · w` with `w ≡ 1 (mod 3)`. -/
abbrev IdeleDecomp (z : Adelesˣ) (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ) : Prop :=
  integralReduction w.val = 1 ∧ z = ideleOf q t w

theorem ideleOf_fst (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ) :
    (ideleOf q t w).val.1 = algebraMap ℚ ℝ q.val * t.val := by
  simp [ideleOf, ratU, infU, finU, intU]

theorem ideleOf_snd (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ) :
    (ideleOf q t w).val.2 = algebraMap ℚ FiniteAdeles q.val * integralEmbedding w.val := by
  simp [ideleOf, ratU, infU, finU, intU]

theorem rational_integral_aux (q q' : ℚ) (hq : q ≠ 0) (u : IntegralAdeles)
    (h : algebraMap ℚ FiniteAdeles q' = algebraMap ℚ FiniteAdeles q * integralEmbedding u) :
    ∃ n : ℤ, q' / q = n ∧ u = (n : IntegralAdeles) := by
  have h1 : algebraMap ℚ FiniteAdeles (q' / q) = integralEmbedding u := by
    rw [div_eq_inv_mul, map_mul, h, ← mul_assoc, ← map_mul (algebraMap ℚ FiniteAdeles),
      inv_mul_cancel₀ hq, map_one, one_mul]
  obtain ⟨n, hn⟩ := (IntegralRationals.integral_iff_integer (q' / q)).mp ⟨u, h1.symm⟩
  refine ⟨n, hn, integralEmbedding_injective ?_⟩
  rw [← h1, hn]
  simp

theorem ideleOf_unique {q q' : ℚˣ} {t t' : ℝˣ} {w w' : IntegralAdelesˣ}
    (hw : integralReduction w.val = 1) (hw' : integralReduction w'.val = 1)
    (h : ideleOf q t w = ideleOf q' t' w') : q = q' ∧ t = t' := by
  have h1 : algebraMap ℚ ℝ q.val * t.val = algebraMap ℚ ℝ q'.val * t'.val := by
    have := congrArg (fun a : Adelesˣ => a.val.1) h
    simpa only [ideleOf_fst] using this
  have h2 : algebraMap ℚ FiniteAdeles q.val * integralEmbedding w.val =
      algebraMap ℚ FiniteAdeles q'.val * integralEmbedding w'.val := by
    have := congrArg (fun a : Adelesˣ => a.val.2) h
    simpa only [ideleOf_snd] using this
  have hinv' : integralReduction w'.inv = 1 := by
    have : integralReduction w'.val * integralReduction w'.inv = 1 := by
      rw [← map_mul, w'.val_inv, map_one]
    rwa [hw', one_mul] at this
  -- `q' = q * (w w'⁻¹)`
  have h3 : algebraMap ℚ FiniteAdeles q'.val =
      algebraMap ℚ FiniteAdeles q.val * integralEmbedding (w.val * w'.inv) := by
    have e : integralEmbedding w'.val * integralEmbedding w'.inv = 1 := by
      rw [← map_mul, w'.val_inv, map_one]
    calc algebraMap ℚ FiniteAdeles q'.val
        = algebraMap ℚ FiniteAdeles q'.val * (integralEmbedding w'.val *
            integralEmbedding w'.inv) := by rw [e, mul_one]
      _ = (algebraMap ℚ FiniteAdeles q'.val * integralEmbedding w'.val) *
            integralEmbedding w'.inv := by rw [mul_assoc]
      _ = algebraMap ℚ FiniteAdeles q.val * integralEmbedding (w.val * w'.inv) := by
        rw [← h2, map_mul, mul_assoc]
  have h4 : algebraMap ℚ FiniteAdeles q.val =
      algebraMap ℚ FiniteAdeles q'.val * integralEmbedding (w'.val * w.inv) := by
    have e : integralEmbedding w.val * integralEmbedding w.inv = 1 := by
      rw [← map_mul, w.val_inv, map_one]
    calc algebraMap ℚ FiniteAdeles q.val
        = algebraMap ℚ FiniteAdeles q.val * (integralEmbedding w.val *
            integralEmbedding w.inv) := by rw [e, mul_one]
      _ = (algebraMap ℚ FiniteAdeles q.val * integralEmbedding w.val) *
            integralEmbedding w.inv := by rw [mul_assoc]
      _ = algebraMap ℚ FiniteAdeles q'.val * integralEmbedding (w'.val * w.inv) := by
        rw [h2, map_mul, mul_assoc]
  obtain ⟨n, hn, hu⟩ := rational_integral_aux q.val q'.val q.ne_zero _ h3
  obtain ⟨m, hm, -⟩ := rational_integral_aux q'.val q.val q'.ne_zero _ h4
  have hnm : (n : ℚ) * (m : ℚ) = 1 := by
    have hq0 := q.ne_zero
    have hq0' := q'.ne_zero
    rw [← hn, ← hm]
    field_simp
  have hnm' : n * m = 1 := by exact_mod_cast hnm
  have hq : q'.val = q.val := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm' with rfl | rfl
    · have : q'.val / q.val = 1 := by rw [hn]; simp
      exact (div_eq_one_iff_eq q.ne_zero).mp this
    · exfalso
      have hr : integralReduction (w.val * w'.inv) = 1 := by
        rw [map_mul, hw, hinv', one_mul]
      rw [hu, integralReduction_int] at hr
      have h3' : (((-1 : ℤ) : ZMod 3)) ≠ 1 := by decide
      exact h3' hr
  refine ⟨Units.ext hq.symm, Units.ext ?_⟩
  rw [hq] at h1
  exact mul_left_cancel₀ (by simp) h1

theorem ideleDecomp_unique {z : Adelesˣ} {q q' : ℚˣ} {t t' : ℝˣ} {w w' : IntegralAdelesˣ}
    (h : IdeleDecomp z q t w) (h' : IdeleDecomp z q' t' w') : q = q' ∧ t = t' :=
  ideleOf_unique h.1 h'.1 (h.2.symm.trans h'.2)

theorem ideleDecomp_exists (z : Adelesˣ) : ∃ (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ),
    IdeleDecomp z q t w := by
  obtain ⟨q, w, hqw⟩ := FiniteIdeleReduction.exists_rational_mul_integral
    (Units.map (MonoidHom.snd ℝ FiniteAdeles) z)
  have hred : ∃ (q : ℚˣ) (w : IntegralAdelesˣ), integralReduction w.val = 1 ∧
      Units.map (MonoidHom.snd ℝ FiniteAdeles) z =
        FiniteIdeleReduction.rationalUnit q * intU w := by
    have hcases : ∀ a b : ZMod 3, a * b = 1 → a = 1 ∨ a = -1 := by decide
    have hmul : integralReduction w.val * integralReduction w.inv = 1 := by
      rw [← map_mul, w.val_inv, map_one]
    rcases hcases _ _ hmul with h | h
    · exact ⟨q, w, h, hqw⟩
    · refine ⟨-q, -w, ?_, ?_⟩
      · erw [Units.val_neg, map_neg, h, neg_neg]
      · rw [hqw]
        apply Units.ext
        simp [FiniteIdeleReduction.rationalUnit, intU]
  obtain ⟨q, w, hw, hqw⟩ := hred
  let u : ℝˣ := Units.map (algebraMap ℚ ℝ).toMonoidHom q
  let t : ℝˣ := u⁻¹ * Units.map (MonoidHom.fst ℝ FiniteAdeles) z
  have hz : Units.map (MonoidHom.fst ℝ FiniteAdeles) z = u * t := (mul_inv_cancel_left u _).symm
  refine ⟨q, t, w, hw, Units.ext (Prod.ext ?_ ?_)⟩
  · rw [ideleOf_fst]
    exact congrArg Units.val hz
  · rw [ideleOf_snd]
    exact congrArg Units.val hqw

theorem ideleDecomp_mul {z z' : Adelesˣ} {q q' : ℚˣ} {t t' : ℝˣ} {w w' : IntegralAdelesˣ}
    (h : IdeleDecomp z q t w) (h' : IdeleDecomp z' q' t' w') :
    IdeleDecomp (z * z') (q * q') (t * t') (w * w') := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, map_mul, h.1, h'.1, one_mul]
  · rw [h.2, h'.2]
    simp only [ideleOf, map_mul]
    ac_rfl

/-- The sign of a real unit as an element of `ℤˣ`. -/
def signUnit (t : ℝˣ) : ℤˣ := if t.val < 0 then -1 else 1

theorem signUnit_mul (t t' : ℝˣ) : signUnit (t * t') = signUnit t * signUnit t' := by
  unfold signUnit
  rcases t.ne_zero.lt_or_gt with h | h <;>
    rcases t'.ne_zero.lt_or_gt with h' | h'
  · have : 0 < t.val * t'.val := mul_pos_of_neg_of_neg h h'
    simp [h, h', not_lt.mpr this.le]
  · have : t.val * t'.val < 0 := mul_neg_of_neg_of_pos h h'
    simp [h, not_lt.mpr h'.le, this]
  · have : t.val * t'.val < 0 := mul_neg_of_pos_of_neg h h'
    simp [h', not_lt.mpr h.le, this]
  · have : 0 < t.val * t'.val := mul_pos h h'
    simp [not_lt.mpr h.le, not_lt.mpr h'.le, not_lt.mpr this.le]

/-- The real unit part of the canonical decomposition of an idele. -/
def ideleReal (z : Adelesˣ) : ℝˣ := (ideleDecomp_exists z).choose_spec.choose

theorem ideleReal_spec (z : Adelesˣ) :
    ∃ (q : ℚˣ) (w : IntegralAdelesˣ), IdeleDecomp z q (ideleReal z) w :=
  ⟨_, _, (ideleDecomp_exists z).choose_spec.choose_spec.choose_spec⟩

theorem ideleReal_eq {z : Adelesˣ} {q : ℚˣ} {t : ℝˣ} {w : IntegralAdelesˣ}
    (h : IdeleDecomp z q t w) : ideleReal z = t := by
  obtain ⟨_, _, h'⟩ := ideleReal_spec z
  exact (ideleDecomp_unique h' h).2

/-- The sign character of an idele. -/
def ideleSign : Adelesˣ →* ℤˣ where
  toFun z := signUnit (ideleReal z)
  map_one' := by
    show signUnit (ideleReal 1) = 1
    have h : IdeleDecomp 1 1 1 1 := ⟨by simp, by simp [ideleOf]⟩
    rw [ideleReal_eq h]
    simp [signUnit]
  map_mul' z z' := by
    show signUnit (ideleReal (z * z')) = signUnit (ideleReal z) * signUnit (ideleReal z')
    obtain ⟨_, _, h⟩ := ideleReal_spec z
    obtain ⟨_, _, h'⟩ := ideleReal_spec z'
    rw [ideleReal_eq (ideleDecomp_mul h h'), signUnit_mul]

theorem exists_idele_decomp (z : Adelesˣ) :
    ∃ (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ), integralReduction w.val = 1 ∧
      GeneralLinearGroup.scalar (Fin 2) z =
        ratGL (GeneralLinearGroup.scalar (Fin 2) q) *
          (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
            finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w))) := by
  obtain ⟨q, t, w, h1, h2⟩ := ideleDecomp_exists z
  exact ⟨q, t, w, h1, by rw [scalar_ideleOf, ← h2]⟩

theorem exists_sign_character : ∃ ε : Adelesˣ →* ℤˣ, ∀ (z : Adelesˣ) (q : ℚˣ) (t : ℝˣ)
    (w : IntegralAdelesˣ), integralReduction w.val = 1 →
      GeneralLinearGroup.scalar (Fin 2) z =
        ratGL (GeneralLinearGroup.scalar (Fin 2) q) *
          (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
            finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w))) →
      ε z = if t.val < 0 then -1 else 1 := by
  refine ⟨ideleSign, fun z q t w hw h => ?_⟩
  rw [scalar_ideleOf] at h
  have hz : z = ideleOf q t w := scalar_injective h
  change signUnit (ideleReal z) = _
  exact congrArg signUnit (ideleReal_eq ⟨hw, hz⟩)

end TernaryPeriodPolynomials.CuspIntegral
