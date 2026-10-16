module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeSmallWeight

@[expose] public section


/-!
# A Sturm bound for cusp forms on `Γ₁(3)`

A cusp form `f` of weight `k` on `Γ₁(3)` whose `q`-expansion coefficients `a_1, …, a_J` vanish,
`J = ⌊k/3⌋ - 1`, is zero. Indeed `f = O(q^{J+1})` at `∞`, and each of the three translates `f ∣ S T^j`
(expansions at the cusp `0`, of width three) is `O(q^{1/3})`; hence the norm
`N(f) = f · f∣S · f∣ST · f∣ST²` (Sol's `gammaOneThreeProductCuspForm`, a level-one cusp form of
weight `4k`) is `O(q^{J+2})`. A level-one cusp form of weight `w` which is `O(q^r)` with `12 r > w`
vanishes (divide by the discriminant `r` times, `levelOne_eq_zero_of_isBigO`), and `N(f) = 0` forces
`f = 0`.

Consequently `S_k(Γ₁(3))` is finite-dimensional of dimension at most `⌊k/3⌋ - 1`
(`finrank_cuspForm_le`), the dimension `dim H¹_par(Γ₁'(3), Sym^{k-2} ⊗ det^e)` of `ExactLevel`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane ModularForm Filter Asymptotics Matrix
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.SturmBound

/-- The level-one group as a subgroup of `GL(2, ℝ)`. -/
abbrev levelOne : Subgroup (GL (Fin 2) ℝ) := (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range

/-- A level-one cusp form which vanishes at `∞` is a level-one cusp form (re-bundling a modular
form). -/
def toCusp {w : ℤ} (g : ModularForm levelOne w) (zero : IsZeroAtImInfty (g : ℍ → ℂ)) :
    CuspForm levelOne w where
  toFun := g
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq g
  holo' := g.holo'
  zero_at_cusps' := by
    intro cuspPoint is_cusp
    apply (OnePoint.isZeroAt_iff_forall_SL2Z is_cusp).mpr
    intro matrix _
    change IsZeroAtImInfty (SlashAction.map w (SpecialLinearGroup.mapGL ℝ matrix) (g : ℍ → ℂ))
    rw [SlashInvariantFormClass.slash_action_eq (Γ := levelOne) g
      (SpecialLinearGroup.mapGL ℝ matrix) ⟨matrix, rfl⟩]
    exact zero

theorem exp_mul_im (r : ℕ) (τ : ℍ) :
    Real.exp (-2 * Real.pi * ((r : ℝ) + 1) * τ.im) =
      Real.exp (-2 * Real.pi * r * τ.im) * Real.exp (-2 * Real.pi * τ.im) := by
  rw [← Real.exp_add]
  ring_nf

/-- **Level one.** A level-one cusp form of weight `w` which is `O(e^{-2π r y})` at `∞`, with
`w < 12 r`, vanishes. -/
theorem levelOne_eq_zero_of_isBigO (r : ℕ) :
    ∀ (w : ℤ) (g : CuspForm levelOne w), w < 12 * r →
      (g : ℍ → ℂ) =O[atImInfty] (fun τ => Real.exp (-2 * Real.pi * r * τ.im)) → g = 0 := by
  induction r with
  | zero =>
    intro w g hw _
    obtain ⟨scalar, scalar_nonzero, scalar_zero⟩ :=
      rank_eq_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega : w < 12)) g
    exact (smul_eq_zero.mp scalar_zero).resolve_left scalar_nonzero
  | succ r ih =>
    intro w g hw decay
    by_cases small : w < 12
    · obtain ⟨scalar, scalar_nonzero, scalar_zero⟩ :=
        rank_eq_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve small) g
      exact (smul_eq_zero.mp scalar_zero).resolve_left scalar_nonzero
    have hr : 1 ≤ r := by
      by_contra h
      push Not at h
      interval_cases r
      push_cast at hw
      omega
    -- the quotient by the discriminant
    set quotient := CuspForm.discriminantEquiv g
    have hquot : ∀ τ, quotient τ = g τ / ModularForm.discriminant τ := fun _ => rfl
    have hlower := ModularForm.exp_isBigO_discriminant
    obtain ⟨C, hC0, hCw⟩ := hlower.exists_pos
    have hC := hCw.bound
    have decay' : (quotient : ℍ → ℂ) =O[atImInfty]
        (fun τ => Real.exp (-2 * Real.pi * r * τ.im)) := by
      obtain ⟨D, hD0, hDw⟩ := decay.exists_pos
      have hD := hDw.bound
      refine IsBigO.of_bound (C * D) ?_
      filter_upwards [hC, hD] with τ hτC hτD
      rw [hquot, norm_div]
      have hΔ : 0 < ‖ModularForm.discriminant τ‖ :=
        norm_pos_iff.mpr (ModularForm.discriminant_ne_zero τ)
      rw [div_le_iff₀ hΔ]
      have he : 0 < Real.exp (-2 * Real.pi * τ.im) := Real.exp_pos _
      rw [Real.norm_of_nonneg he.le] at hτC
      rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hτD ⊢
      push_cast at hτD
      rw [exp_mul_im r τ] at hτD
      calc ‖g τ‖ ≤ D * (Real.exp (-2 * Real.pi * r * τ.im) * Real.exp (-2 * Real.pi * τ.im)) :=
            hτD
        _ ≤ D * (Real.exp (-2 * Real.pi * r * τ.im) * (C * ‖ModularForm.discriminant τ‖)) := by
            gcongr
        _ = C * D * Real.exp (-2 * Real.pi * r * τ.im) * ‖ModularForm.discriminant τ‖ := by ring
    have zero : IsZeroAtImInfty (quotient : ℍ → ℂ) := by
      apply decay'.trans_tendsto
      have height : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
      have hpos : 0 < 2 * Real.pi * r := by
        have : (0 : ℝ) < r := by exact_mod_cast hr
        positivity
      have := (height.const_mul_atTop hpos)
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp this
      convert this using 2 with τ
      simp only [Function.comp_apply]
      ring_nf
    have hq0 := ih (w - 12) (toCusp quotient zero) (by push_cast at hw; omega) decay'
    apply DFunLike.ext
    intro τ
    have hv := congrArg (fun f : CuspForm levelOne (w - 12) => f τ) hq0
    change g τ / ModularForm.discriminant τ = 0 at hv
    exact (div_eq_zero_iff.mp hv).resolve_right (ModularForm.discriminant_ne_zero τ)

/-! ### Level three -/

theorem one_mem_strictPeriods : (1 : ℝ) ∈ binaryRealGammaOneThree.strictPeriods := by
  have := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem gammaOneThree_T_mem
  unfold binaryRealGammaOneThree
  erw [this]
  exact AddSubgroup.mem_zmultiples 1

instance isCusp_infty : Fact (IsCusp OnePoint.infty binaryRealGammaOneThree) :=
  ⟨binaryRealGammaOneThree.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods⟩

/-- The `m`-th `q`-expansion coefficient (period one) of a function on `ℍ`. -/
abbrev coeff (f : ℍ → ℂ) (m : ℕ) : ℂ := (qExpansion 1 f).coeff m

/-- **Decay from vanishing coefficients.** A cusp form on `Γ₁(3)` whose `q`-expansion
coefficients `a_0, …, a_J` vanish is `O(e^{-2π (J+1) y})` at `∞`. -/
theorem isBigO_of_coeff_eq_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (J : ℕ)
    (vanish : ∀ m ≤ J, coeff f m = 0) :
    (f : ℍ → ℂ) =O[atImInfty] (fun τ => Real.exp (-2 * Real.pi * ((J : ℝ) + 1) * τ.im)) := by
  have hseries := UpperHalfPlane.hasFPowerSeries_cuspFunction f one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods)
    (fun τ => by simpa [smul_eq_mul] using
      ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods τ)
  have htaylor := hseries.hasFPowerSeriesAt.isBigO_sub_partialSum_pow (J + 1)
  have hpartial : ∀ y : ℂ,
      (qExpansionFormalMultilinearSeries 1 f).partialSum (J + 1) y = 0 := by
    intro y
    unfold FormalMultilinearSeries.partialSum
    apply Finset.sum_eq_zero
    intro m hm
    have hv := vanish m (by simpa [Nat.lt_succ_iff] using hm)
    rw [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.ofScalars_apply_eq]
    rw [coeff] at hv
    rw [hv, zero_smul]
  simp only [hpartial, sub_zero, zero_add] at htaylor
  have hcomp := htaylor.comp_tendsto (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  refine (IsBigO.congr' hcomp ?_ ?_)
  · filter_upwards with τ
    simp only [Function.comp_apply]
    exact SlashInvariantFormClass.eq_cuspFunction f τ one_mem_strictPeriods one_ne_zero
  · filter_upwards with τ
    simp only [Function.comp_apply]
    rw [Function.Periodic.norm_qParam, ← Real.exp_nat_mul]
    congr 1
    push_cast
    simp only [UpperHalfPlane.coe_im]
    ring

theorem coeff_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) : coeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods

/-- **Sturm bound on `Γ₁(3)`.** If `k < 3 (J + 2)` and the coefficients `a_1, …, a_J` of a cusp
form of weight `k` on `Γ₁(3)` vanish, the form is zero. -/
theorem eq_zero_of_coeff_eq_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (J : ℕ)
    (weight : k < 3 * ((J : ℤ) + 2)) (vanish : ∀ m, 1 ≤ m → m ≤ J → coeff f m = 0) : f = 0 := by
  have vanish' : ∀ m ≤ J, coeff f m = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h]
      exact coeff_zero f
    · exact vanish m h hm
  have first := isBigO_of_coeff_eq_zero f J vanish'
  have second := gammaOneThree_ST_exp_decay f 0
  have third := gammaOneThree_ST_exp_decay f 1
  have fourth := gammaOneThree_ST_exp_decay f 2
  have product := ((first.mul second).mul third).mul fourth
  have decay : (gammaOneThreeProductCuspForm f : ℍ → ℂ) =O[atImInfty]
      (fun τ => Real.exp (-2 * Real.pi * (((J + 2 : ℕ) : ℕ) : ℝ) * τ.im)) := by
    refine product.congr' ?_ ?_
    · filter_upwards with τ
      simp only [gammaOneThreeProductCuspForm, gammaOneThreeProduct, pow_zero, mul_one,
        pow_one]
      rfl
    · filter_upwards with τ
      simp only [← Real.exp_add]
      congr 1
      push_cast
      ring
  have hzero := levelOne_eq_zero_of_isBigO (J + 2) (4 * k) (gammaOneThreeProductCuspForm f)
    (by push_cast; omega) decay
  apply (gammaOneThreeProduct_eq_zero_iff f).mp
  exact congrArg (fun g : CuspForm levelOne (4 * k) => (g : ℍ → ℂ)) hzero

/-- The coefficients `a_1, …, a_J` as a linear map. -/
def coeffMap (k : ℤ) (J : ℕ) : CuspForm binaryRealGammaOneThree k →ₗ[ℂ] (Fin J → ℂ) where
  toFun f i := coeff f (i.val + 1)
  map_add' f g := by
    funext i
    have h : qExpansion 1 ⇑(f + g) = qExpansion 1 ⇑f + qExpansion 1 ⇑g :=
      map_add (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods k)
        (CuspForm.toModularFormₗ f) (CuspForm.toModularFormₗ g)
    simp only [Pi.add_apply, coeff, h, map_add]
  map_smul' a f := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, coeff, smul_eq_mul]
    have h := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods a f
    rw [FunLike.coe_smul, h]
    simp

theorem coeffMap_injective {k : ℤ} {J : ℕ} (weight : k < 3 * ((J : ℤ) + 2)) :
    Function.Injective (coeffMap k J) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  apply eq_zero_of_coeff_eq_zero f J weight
  intro m h1 hJ
  have := congrFun hf ⟨m - 1, by omega⟩
  simp only [coeffMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
  rwa [show m - 1 + 1 = m by omega] at this

/-- `S_k(Γ₁(3))` is finite-dimensional. -/
theorem cuspForm_finiteDimensional (k : ℤ) :
    FiniteDimensional ℂ (CuspForm binaryRealGammaOneThree k) := by
  have weight : k < 3 * (((k.toNat : ℕ) : ℤ) + 2) := by omega
  exact Module.Finite.of_injective _ (coeffMap_injective weight)

/-- **Dimension bound.** `dim S_k(Γ₁(3)) ≤ ⌊k/3⌋ - 1`. -/
theorem finrank_cuspForm_le (k : ℤ) :
    Module.finrank ℂ (CuspForm binaryRealGammaOneThree k) ≤ (k / 3 - 1).toNat := by
  have : FiniteDimensional ℂ (CuspForm binaryRealGammaOneThree k) := cuspForm_finiteDimensional k
  have weight : k < 3 * ((((k / 3 - 1).toNat : ℕ) : ℤ) + 2) := by omega
  have h := LinearMap.finrank_le_finrank_of_injective (coeffMap_injective weight)
  simpa using h

end TernaryPeriodPolynomials.LevelThree.SturmBound
