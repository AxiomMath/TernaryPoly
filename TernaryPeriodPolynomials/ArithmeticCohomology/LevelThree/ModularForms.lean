module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.GammaOneThreeCosets
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


/-!
# Constructing modular and cusp forms for `Γ₁(3)`

The level is Sol's `binaryRealGammaOneThree`, the image of `Γ₁(3) ⊆ SL₂(ℤ)` in `GL₂(ℝ)`.

* `slash_gammaOneThree`: a function invariant under `T` whose `S`-transform is invariant under
  `T³` is invariant under `Γ₁(3)` (because `L = S T⁻³ S⁻¹` and `Γ₁(3) ≤ ⟨T, L⟩`);
* `slash_property`: for such a function every `f ∣ γ`, `γ ∈ SL₂(ℤ)`, is a constant multiple of
  `f` or of `(f ∣ S) ∣ Tᵐ` (cusp representatives), so any property of functions stable under
  scalars and integer translations holds for all `f ∣ γ` once it holds for `f` and `f ∣ S`;
* **`mkForm`**: a holomorphic function, invariant under `T`, with `S`-transform invariant under
  `T³`, bounded at `∞` with `S`-transform bounded at `∞`, is a modular form for `Γ₁(3)`;
* **`toCusp`**: a modular form for `Γ₁(3)` vanishing at `∞` whose `S`-transform vanishes at `∞`
  is a cusp form;
* `HasLead f n L`: `f(z) / qⁿ → L` as `Im z → ∞` (`q = e^{2πiz}`), with the algebra of leading
  terms (products, powers, scalar multiples, differences).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeModularForms

open UpperHalfPlane ModularForm ModularGroup CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Manifold
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.LevelThree.GammaOneThreeCosets

/-- The stabilizer of a function under the weight-`k` slash action of `SL₂(ℤ)`. -/
def slashStabilizer (k : ℤ) (f : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | f ∣[k] γ = f}
  one_mem' := SlashAction.slash_one k f
  mul_mem' {a b} ha hb := by
    change f ∣[k] a = f at ha
    change f ∣[k] b = f at hb
    change f ∣[k] (a * b) = f
    rw [SlashAction.slash_mul, ha, hb]
  inv_mem' {a} ha := by
    change f ∣[k] a = f at ha
    change f ∣[k] a⁻¹ = f
    conv_lhs => rw [← ha]
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem slash_T_pow_neg {k : ℤ} {g : ℍ → ℂ} (hg : g ∣[k] (T ^ 3 : SL(2, ℤ)) = g) :
    g ∣[k] (T ^ (-3 : ℤ) : SL(2, ℤ)) = g := by
  conv_lhs => rw [← hg]
  rw [← SlashAction.slash_mul, show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg,
    zpow_natCast, mul_inv_cancel, SlashAction.slash_one]

/-- Invariance under `T` and `T³`-invariance of the `S`-transform give `Γ₁(3)`-invariance. -/
theorem slash_gammaOneThree {k : ℤ} {f : ℍ → ℂ} (hT : f ∣[k] T = f)
    (hS : (f ∣[k] S) ∣[k] (T ^ 3 : SL(2, ℤ)) = f ∣[k] S) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 3) :
    f ∣[k] γ = f := by
  have hle : Subgroup.closure ({T, lowerL} : Set SL(2, ℤ)) ≤ slashStabilizer k f := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hT
    · change f ∣[k] lowerL = f
      rw [lowerL_eq, SlashAction.slash_mul, SlashAction.slash_mul, slash_T_pow_neg hS,
        ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  exact hle (gammaOneThree_le_closure hγ)

theorem slash_one_eq_smul (k : ℤ) (f : ℍ → ℂ) : f ∣[k] (1 : SL(2, ℤ)) = (1 : ℂ) • f := by
  rw [SlashAction.slash_one, one_smul]

/-- **Cusp control.** If `f` is `Γ₁(3)`-invariant then any property stable under scalar
multiplication and integer translation `g ↦ g ∣ Tᵐ` that holds for `f` and `f ∣ S` holds for
every `f ∣ γ`. -/
theorem slash_property {k : ℤ} {f : ℍ → ℂ} (hΓ : ∀ γ ∈ Gamma1 3, f ∣[k] γ = f)
    (P : (ℍ → ℂ) → Prop) (hsmul : ∀ (c : ℂ) (g : ℍ → ℂ), P g → P (c • g))
    (htrans : ∀ (g : ℍ → ℂ) (m : ℤ), P g → P (g ∣[k] (T ^ m : SL(2, ℤ)))) (hinf : P f)
    (h0 : P (f ∣[k] S))
    (γ : SL(2, ℤ)) : P (f ∣[k] γ) := by
  obtain ⟨ε, h, hε, hh, hγ⟩ := exists_decomposition γ
  have hε' : ∃ c : ℂ, f ∣[k] ε = c • f := by
    rcases hε with rfl | rfl
    · exact ⟨1, slash_one_eq_smul k f⟩
    · exact ⟨_, scalar_slash_neg_one k f⟩
  obtain ⟨c, hc⟩ := hε'
  rcases hγ with rfl | ⟨m, rfl⟩
  · rw [SlashAction.slash_mul, hc, SL_smul_slash, hΓ h hh]
    exact hsmul c f hinf
  · rw [SlashAction.slash_mul, SlashAction.slash_mul, SlashAction.slash_mul, hc, SL_smul_slash,
      hΓ h hh, SL_smul_slash, SL_smul_slash]
    exact hsmul c _ (htrans _ m h0)

theorem isBoundedAtImInfty_slash_T_zpow {k : ℤ} {g : ℍ → ℂ} (hg : IsBoundedAtImInfty g)
    (m : ℤ) : IsBoundedAtImInfty (g ∣[k] (T ^ m : SL(2, ℤ))) := by
  rw [SL_slash]
  apply hg.slash
  change ((T ^ m : SL(2, ℤ)).1.map (Int.cast : ℤ → ℝ)) 1 0 = 0
  rw [coe_T_zpow]
  simp

theorem isZeroAtImInfty_slash_T_zpow {k : ℤ} {g : ℍ → ℂ} (hg : IsZeroAtImInfty g)
    (m : ℤ) : IsZeroAtImInfty (g ∣[k] (T ^ m : SL(2, ℤ))) := by
  rw [SL_slash]
  apply hg.slash
  change ((T ^ m : SL(2, ℤ)).1.map (Int.cast : ℤ → ℝ)) 1 0 = 0
  rw [coe_T_zpow]
  simp

theorem isBoundedAtImInfty_smul {g : ℍ → ℂ} (c : ℂ) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (c • g) :=
  Asymptotics.IsBigO.const_smul_left hg c

theorem isZeroAtImInfty_smul {g : ℍ → ℂ} (c : ℂ) (hg : IsZeroAtImInfty g) :
    IsZeroAtImInfty (c • g) := by
  have h := Tendsto.const_mul c hg
  rw [mul_zero] at h
  exact h

/-- **Modular forms for `Γ₁(3)` from the two cusps.** -/
def mkForm (k : ℤ) (f : ℍ → ℂ) (holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hT : f ∣[k] T = f)
    (hS : (f ∣[k] S) ∣[k] (T ^ 3 : SL(2, ℤ)) = f ∣[k] S) (hinf : IsBoundedAtImInfty f)
    (h0 : IsBoundedAtImInfty (f ∣[k] S)) : ModularForm binaryRealGammaOneThree k where
  toFun := f
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    exact slash_gammaOneThree hT hS hg
  holo' := holo
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    exact slash_property (fun γ hγ => slash_gammaOneThree hT hS hγ) IsBoundedAtImInfty
      (fun c _ hg => isBoundedAtImInfty_smul c hg) (fun g m hg => isBoundedAtImInfty_slash_T_zpow hg m) hinf h0 γ

@[simp]
theorem coe_mkForm (k : ℤ) (f : ℍ → ℂ) (holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hT : f ∣[k] T = f)
    (hS : (f ∣[k] S) ∣[k] (T ^ 3 : SL(2, ℤ)) = f ∣[k] S) (hinf : IsBoundedAtImInfty f)
    (h0 : IsBoundedAtImInfty (f ∣[k] S)) : ⇑(mkForm k f holo hT hS hinf h0) = f :=
  rfl

/-- Elements of `Γ₁(3)` act trivially on modular forms for `binaryRealGammaOneThree`. -/
theorem form_slash {k : ℤ} (F : ModularForm binaryRealGammaOneThree k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 3) : ⇑F ∣[k] γ = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, hγ, rfl⟩

/-- **Cusp forms for `Γ₁(3)` from the two cusps.** -/
def toCusp {k : ℤ} (F : ModularForm binaryRealGammaOneThree k) (hinf : IsZeroAtImInfty F)
    (h0 : IsZeroAtImInfty (⇑F ∣[k] S)) : CuspForm binaryRealGammaOneThree k where
  toSlashInvariantForm := F.toSlashInvariantForm
  holo' := F.holo'
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact slash_property (fun γ hγ => form_slash F hγ) IsZeroAtImInfty
      (fun c _ hg => isZeroAtImInfty_smul c hg) (fun g m hg => isZeroAtImInfty_slash_T_zpow hg m) hinf h0 γ

@[simp]
theorem coe_toCusp {k : ℤ} (F : ModularForm binaryRealGammaOneThree k) (hinf : IsZeroAtImInfty F)
    (h0 : IsZeroAtImInfty (⇑F ∣[k] S)) : ⇑(toCusp F hinf h0) = ⇑F :=
  rfl

theorem form_bdd_slash {k : ℤ} (F : ModularForm binaryRealGammaOneThree k) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (⇑F ∣[k] γ) :=
  ModularFormClass.bdd_at_infty_slash F γ

/-! ### Leading terms at `∞` -/

/-- `f(z) / qⁿ → L` as `Im z → ∞`, where `q = e^{2πiz}`. -/
def HasLead (f : ℍ → ℂ) (n : ℕ) (L : ℂ) : Prop :=
  Tendsto (fun z : ℍ => f z / Function.Periodic.qParam 1 z ^ n) atImInfty (𝓝 L)

theorem tendsto_qParam : Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z) atImInfty (𝓝 0) :=
  qParam_tendsto_atImInfty one_pos

theorem HasLead.mul {f g : ℍ → ℂ} {n m : ℕ} {L M : ℂ} (hf : HasLead f n L) (hg : HasLead g m M) :
    HasLead (f * g) (n + m) (L * M) := by
  refine Tendsto.congr (fun z => ?_) (Tendsto.mul hf hg)
  have hq := Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  simp only [Pi.mul_apply, pow_add]
  field_simp

theorem HasLead.pow {f : ℍ → ℂ} {n : ℕ} {L : ℂ} (hf : HasLead f n L) (j : ℕ) :
    HasLead (f ^ j) (j * n) (L ^ j) := by
  induction j with
  | zero =>
    refine Tendsto.congr (fun z => ?_) tendsto_const_nhds
    simp
  | succ j ih =>
    have h := ih.mul hf
    rw [pow_succ, pow_succ, show (j + 1) * n = j * n + n by ring]
    exact h

theorem HasLead.const_smul {f : ℍ → ℂ} {n : ℕ} {L : ℂ} (hf : HasLead f n L) (c : ℂ) :
    HasLead (c • f) n (c * L) := by
  refine Tendsto.congr (fun z => ?_) (Tendsto.const_mul c hf)
  simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc]

theorem HasLead.sub {f g : ℍ → ℂ} {n : ℕ} {L M : ℂ} (hf : HasLead f n L) (hg : HasLead g n M) :
    HasLead (f - g) n (L - M) := by
  refine Tendsto.congr (fun z => ?_) (Tendsto.sub hf hg)
  simp only [Pi.sub_apply, sub_div]

theorem HasLead.of_eq {f g : ℍ → ℂ} {n : ℕ} {L : ℂ} (hf : HasLead f n L) (h : f = g) :
    HasLead g n L :=
  h ▸ hf

/-- A function with leading term of order `n ≥ 1` vanishes at `∞`. -/
theorem HasLead.isZeroAtImInfty {f : ℍ → ℂ} {n : ℕ} {L : ℂ} (hf : HasLead f n L) (hn : 1 ≤ n) :
    IsZeroAtImInfty f := by
  have h := Tendsto.mul hf (tendsto_qParam.pow n)
  rw [zero_pow (show n ≠ 0 by omega), mul_zero] at h
  refine Tendsto.congr (fun z => ?_) h
  have hq := Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  field_simp

/-- A function with a leading term of order `0` tends to it. -/
theorem HasLead.tendsto {f : ℍ → ℂ} {L : ℂ} (hf : HasLead f 0 L) :
    Tendsto f atImInfty (𝓝 L) := by
  refine Tendsto.congr (fun z => ?_) hf
  simp

theorem hasLead_zero_iff {f : ℍ → ℂ} {L : ℂ} :
    HasLead f 0 L ↔ Tendsto f atImInfty (𝓝 L) := by
  unfold HasLead
  simp only [pow_zero, div_one]

end TernaryPeriodPolynomials.LevelThree.LevelThreeModularForms
