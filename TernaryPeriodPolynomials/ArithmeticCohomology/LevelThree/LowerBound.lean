module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ModularForms
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SturmBound

@[expose] public section


/-!
# A lower bound for `dim S_k(Γ₁(3))` (stage 1: independence from distinct leading exponents)

Culminates in `finrank_cuspForm_eq : finrank ℂ (CuspForm binaryRealGammaOneThree k) = (k / 3 - 1).toNat`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeLowerBound

open UpperHalfPlane ModularForm Filter Topology
open scoped MatrixGroups ModularForm Manifold
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreeModularForms

/-- A function with leading term of order `m` has a zero leading term of every smaller order. -/
theorem hasLead_lower {f : ℍ → ℂ} {n m : ℕ} {L : ℂ} (hf : HasLead f m L) (h : n < m) :
    HasLead f n 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  have h1 : Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z ^ (d + 1) *
      (f z / Function.Periodic.qParam 1 z ^ (n + d + 1))) atImInfty (𝓝 0) := by
    have := (tendsto_qParam.pow (d + 1)).mul hf
    rw [zero_pow (by omega), zero_mul] at this
    exact this
  refine Tendsto.congr (fun z => ?_) h1
  have hq := Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  rw [show n + d + 1 = (d + 1) + n by ring, pow_add]
  field_simp
  ring

theorem cusp_sum_apply {k : ℤ} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm binaryRealGammaOneThree k) (z : ℍ) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Forms with pairwise distinct nonzero leading exponents at `∞` are linearly independent. -/
theorem linearIndependent_of_leads {k : ℤ} {N : ℕ}
    (C : Fin N → CuspForm binaryRealGammaOneThree k) (n : Fin N → ℕ) (L : Fin N → ℂ)
    (hlead : ∀ i, HasLead (C i) (n i) (L i)) (hL : ∀ i, L i ≠ 0)
    (hn : Function.Injective n) : LinearIndependent ℂ C := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hne
  have hsne : (Finset.univ.filter (fun i => c i ≠ 0)).Nonempty := ⟨j, by simp [hj]⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ n hsne
  have hci0 : c i0 ≠ 0 := by simpa using hi0
  have hsum : ∀ z : ℍ, ∑ i, c i * (C i z) = 0 := by
    intro z
    have := congrArg (fun F : CuspForm binaryRealGammaOneThree k => (F : ℍ → ℂ) z) hc
    simp only [cusp_sum_apply] at this
    simpa using this
  have hterm : ∀ i, Tendsto (fun z : ℍ => c i * C i z / Function.Periodic.qParam 1 z ^ (n i0))
      atImInfty (𝓝 (if i = i0 then c i0 * L i0 else 0)) := by
    intro i
    by_cases hi : i = i0
    · rw [ite_eq_left hi, ← hi]
      refine Tendsto.congr (fun z => ?_) (Tendsto.const_mul (c i) (hlead i))
      simp [mul_div_assoc]
    · rw [ite_eq_right hi]
      by_cases hci : c i = 0
      · simp [hci]
      · have hlt : n i0 < n i := by
          have hle := hmin i (by simpa using hci)
          exact lt_of_le_of_ne hle (fun h => hi (hn h).symm)
        have h2 := Tendsto.const_mul (c i) (hasLead_lower (hlead i) hlt)
        rw [mul_zero] at h2
        refine Tendsto.congr (fun z => ?_) h2
        simp [mul_div_assoc]
  have hall := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hall
  have hzero : Tendsto (fun z : ℍ => (∑ i, c i * C i z) / Function.Periodic.qParam 1 z ^ (n i0))
      atImInfty (𝓝 0) := by
    refine Tendsto.congr (fun z => ?_) tendsto_const_nhds
    simp [hsum z]
  have hall' : Tendsto (fun z : ℍ => (∑ i, c i * C i z) / Function.Periodic.qParam 1 z ^ (n i0))
      atImInfty (𝓝 (c i0 * L i0)) := by
    refine Tendsto.congr (fun z => ?_) hall
    simp [Finset.sum_div]
  exact mul_ne_zero hci0 (hL i0) (tendsto_nhds_unique hall' hzero)

theorem le_finrank_of_leads {k : ℤ} {N : ℕ}
    (C : Fin N → CuspForm binaryRealGammaOneThree k) (n : Fin N → ℕ) (L : Fin N → ℂ)
    (hlead : ∀ i, HasLead (C i) (n i) (L i)) (hL : ∀ i, L i ≠ 0)
    (hn : Function.Injective n) :
    N ≤ Module.finrank ℂ (CuspForm binaryRealGammaOneThree k) := by
  have := SturmBound.cuspForm_finiteDimensional k
  simpa using (linearIndependent_of_leads C n L hlead hL hn).fintype_card_le_finrank


/-! ### Dedekind eta: periodicity and asymptotics -/

local notation "𝔮" => Function.Periodic.qParam

/-- The product `∏ (1 - qⁿ)` in the definition of `η`. -/
def etaProd (z : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n z)

theorem eta_eq_exp (z : ℂ) :
    ModularForm.eta z = Complex.exp (2 * Real.pi * Complex.I * z / 24) * etaProd z := by
  simp [ModularForm.eta, etaProd, Function.Periodic.qParam]

theorem qParam_one_add_int (z : ℂ) (m : ℤ) : 𝔮 1 (z + m) = 𝔮 1 z := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [mul_add, Complex.exp_add]
  have : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem qParam_three_add_int (z : ℂ) : 𝔮 3 (z + 3) = 𝔮 3 z := by
  simp only [Function.Periodic.qParam]
  rw [mul_add, add_div, Complex.exp_add]
  have : 2 * (Real.pi : ℂ) * Complex.I * 3 / ((3 : ℝ) : ℂ) = (1 : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem etaProd_add_int (z : ℂ) (m : ℤ) : etaProd (z + m) = etaProd z := by
  simp only [etaProd, ModularForm.eta_q, qParam_one_add_int]

theorem tendsto_tprod_qParam {h : ℝ} (hh : 0 < h) :
    Tendsto (fun x : ℍ => ∏' n : ℕ, (1 - (𝔮 h x) ^ (n + 1))) atImInfty (𝓝 1) := by
  have htprod : Tendsto (fun q : ℂ ↦ ∏' (n : ℕ), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
    simp_rw [sub_eq_add_neg]
    refine this
      (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
      (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  exact htprod.comp (UpperHalfPlane.qParam_tendsto_atImInfty hh)

theorem qParam_one_mul (c : ℝ) (hc : c ≠ 0) (z : ℂ) : 𝔮 1 ((c : ℂ) * z) = 𝔮 (1 / c) z := by
  simp only [Function.Periodic.qParam]
  congr 1
  push_cast
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp

theorem tendsto_etaProd_smul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℍ => etaProd ((c : ℂ) * x)) atImInfty (𝓝 1) := by
  have h := tendsto_tprod_qParam (h := 1 / c) (by positivity)
  refine Tendsto.congr (fun x => ?_) h
  unfold etaProd
  refine tprod_congr (fun n => ?_)
  simp only [ModularForm.eta_q, qParam_one_mul c hc.ne']

theorem tendsto_etaProd_one : Tendsto (fun x : ℍ => etaProd x) atImInfty (𝓝 1) := by
  simpa using tendsto_etaProd_smul 1 one_pos

theorem tendsto_etaProd_three : Tendsto (fun x : ℍ => etaProd (3 * x)) atImInfty (𝓝 1) := by
  simpa using tendsto_etaProd_smul 3 (by norm_num)

theorem tendsto_etaProd_third : Tendsto (fun x : ℍ => etaProd ((x : ℂ) / 3)) atImInfty (𝓝 1) := by
  have := tendsto_etaProd_smul (1 / 3) (by norm_num)
  refine Tendsto.congr (fun x => ?_) this
  congr 1
  push_cast
  ring

/-! ### The eta quotients `Φ_{n,N} = η(z)^(9N-3n) η(3z)^(9n-3N)` -/

/-- `η(z)^(9N-3n) η(3z)^(9n-3N)`: weight `3(n+N)`, order `n` at `∞` and order `N` (in the local
parameter `q^{1/3}`) at the cusp `0`. -/
def phi (n N : ℕ) (z : ℂ) : ℂ :=
  ModularForm.eta z ^ (9 * (N : ℤ) - 3 * n) * ModularForm.eta (3 * z) ^ (9 * (n : ℤ) - 3 * N)

theorem phi_eq (n N : ℕ) (z : ℂ) :
    phi n N z = 𝔮 1 z ^ n *
      (etaProd z ^ (9 * (N : ℤ) - 3 * n) * etaProd (3 * z) ^ (9 * (n : ℤ) - 3 * N)) := by
  unfold phi
  rw [eta_eq_exp, eta_eq_exp, mul_zpow, mul_zpow, ← Complex.exp_int_mul, ← Complex.exp_int_mul]
  have key : Complex.exp (((9 * (N : ℤ) - 3 * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I * z / 24)) *
      Complex.exp (((9 * (n : ℤ) - 3 * N : ℤ) : ℂ) * (2 * Real.pi * Complex.I * (3 * z) / 24)) =
        𝔮 1 z ^ n := by
    rw [← Complex.exp_add]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← key]
  ring

theorem phi_add_one (n N : ℕ) (z : ℂ) : phi n N (z + 1) = phi n N z := by
  rw [phi_eq, phi_eq]
  have h1 : 𝔮 1 (z + 1) = 𝔮 1 z := by simpa using qParam_one_add_int z 1
  have h2 : etaProd (z + 1) = etaProd z := by simpa using etaProd_add_int z 1
  have h3 : etaProd (3 * (z + 1)) = etaProd (3 * z) := by
    have := etaProd_add_int (3 * z) 3
    rw [mul_add]
    simpa using this
  rw [h1, h2, h3]

theorem hasLead_phi (n N : ℕ) : HasLead (fun z : ℍ => phi n N z) n 1 := by
  have h1 := (tendsto_etaProd_one.zpow₀ (9 * (N : ℤ) - 3 * n) (Or.inl one_ne_zero))
  have h3 := (tendsto_etaProd_three.zpow₀ (9 * (n : ℤ) - 3 * N) (Or.inl one_ne_zero))
  have := h1.mul h3
  rw [one_zpow, one_zpow, one_mul] at this
  unfold HasLead
  refine Tendsto.congr (fun z => ?_) this
  have hq := Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  simp only [phi_eq]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero n hq)).symm

/-! ### Slash computations -/

theorem slash_T_apply (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] (ModularGroup.T : SL(2, ℤ))) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul]
  simp [UpperHalfPlane.denom, ModularGroup.coe_T]

theorem slash_T3_apply (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] (ModularGroup.T ^ 3 : SL(2, ℤ))) z =
      f ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z))) := by
  rw [pow_three', SlashAction.slash_mul, SlashAction.slash_mul, slash_T_apply, slash_T_apply,
    slash_T_apply]

theorem slash_S_apply' (k : ℤ) (g : ℂ → ℂ) (z : ℍ) :
    ((fun w : ℍ => g (w : ℂ)) ∣[k] (ModularGroup.S : SL(2, ℤ))) z =
      g (-(z : ℂ)⁻¹) * (z : ℂ) ^ (-k) := by
  simp [SlashInvariantForm.slash_S_apply]

theorem isBounded_of_hasLead {f : ℍ → ℂ} {n : ℕ} {L : ℂ} (hf : HasLead f n L) :
    IsBoundedAtImInfty f := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (hasLead_zero_iff.mp hf).isBigO_one ℝ
  · exact (hf.isZeroAtImInfty hn).isBigO_one ℝ

/-! ### The square root of `z` and the `S`-transform of `η` -/

theorem csqrt_ne_zero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  rw [sqrt_eq_exp hz]
  exact Complex.exp_ne_zero _

theorem csqrt_sq {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * (Complex.log z / 2) = Complex.log z := by push_cast; ring
  rw [this, Complex.exp_log hz]

theorem csqrt_zpow_two_mul {z : ℂ} (hz : z ≠ 0) (k : ℤ) : Complex.sqrt z ^ (2 * k) = z ^ k := by
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, csqrt_sq hz]

theorem csqrt_div_three : ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℍ, Complex.sqrt ((z : ℂ) / 3) = c * Complex.sqrt z := by
  refine ⟨Complex.exp ((Real.log (1 / 3) : ℂ) / 2), Complex.exp_ne_zero _, fun z => ?_⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hz3 : (z : ℂ) / 3 ≠ 0 := div_ne_zero hz (by norm_num)
  have hlog : Complex.log ((z : ℂ) / 3) = (Real.log (1 / 3) : ℂ) + Complex.log z := by
    have : (z : ℂ) / 3 = ((1 / 3 : ℝ) : ℂ) * z := by push_cast; ring
    rw [this, Complex.log_ofReal_mul (by norm_num) hz]
  rw [sqrt_eq_exp hz3, sqrt_eq_exp hz, ← Complex.exp_add, hlog]
  congr 1
  ring

theorem eta_neg_inv {u : ℂ} (hu : 0 < u.im) :
    ModularForm.eta (-u⁻¹) =
      (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt u * ModularForm.eta u) := by
  have := ModularForm.eta_comp_eq_csqrt_I_inv (show u ∈ UpperHalfPlane.upperHalfPlaneSet from hu)
  simpa [neg_div] using this

/-- `η(z)^(9N-3n) η(z/3)^(9n-3N)`: the `S`-transform of `Φ_{n,N}` up to a constant. -/
def psi (n N : ℕ) (z : ℂ) : ℂ :=
  ModularForm.eta z ^ (9 * (N : ℤ) - 3 * n) * ModularForm.eta (z / 3) ^ (9 * (n : ℤ) - 3 * N)

theorem phi_slash_S (n N : ℕ) : ∃ K : ℂ, ∀ z : ℍ,
    ((fun w : ℍ => phi n N (w : ℂ)) ∣[(3 * ((n : ℤ) + N) : ℤ)] (ModularGroup.S : SL(2, ℤ))) z =
      K * psi n N z := by
  obtain ⟨c, hc0, hc⟩ := csqrt_div_three
  have hA : (Complex.sqrt Complex.I)⁻¹ ≠ 0 := inv_ne_zero (csqrt_ne_zero Complex.I_ne_zero)
  refine ⟨((Complex.sqrt Complex.I)⁻¹) ^ (6 * ((n : ℤ) + N)) * c ^ (9 * (n : ℤ) - 3 * N),
    fun z => ?_⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hzim : 0 < ((z : ℂ) / 3).im := by
    have h : 0 < (z : ℂ).im := z.2
    simp only [Complex.div_ofNat_im]
    positivity
  rw [slash_S_apply' _ (phi n N)]
  unfold phi psi
  have e1 : ModularForm.eta (-(z : ℂ)⁻¹) =
      (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * ModularForm.eta z) := eta_neg_inv z.2
  have e2 : ModularForm.eta (3 * -(z : ℂ)⁻¹) =
      (Complex.sqrt Complex.I)⁻¹ * (c * Complex.sqrt z * ModularForm.eta ((z : ℂ) / 3)) := by
    have : 3 * -(z : ℂ)⁻¹ = -((z : ℂ) / 3)⁻¹ := by rw [inv_div]; ring
    rw [this, eta_neg_inv hzim, hc z]
  rw [e1, e2]
  have hs0 : Complex.sqrt z ≠ 0 := csqrt_ne_zero hz
  have hA2 : ((Complex.sqrt Complex.I)⁻¹) ^ (9 * (N : ℤ) - 3 * n) *
      ((Complex.sqrt Complex.I)⁻¹) ^ (9 * (n : ℤ) - 3 * N) =
        ((Complex.sqrt Complex.I)⁻¹) ^ (6 * ((n : ℤ) + N)) := by
    rw [← zpow_add₀ hA]
    congr 1
    ring
  have hs : Complex.sqrt z ^ (9 * (N : ℤ) - 3 * n) * Complex.sqrt z ^ (9 * (n : ℤ) - 3 * N) =
      (z : ℂ) ^ (3 * ((n : ℤ) + N)) := by
    rw [← zpow_add₀ hs0, show (9 * (N : ℤ) - 3 * n) + (9 * (n : ℤ) - 3 * N) =
      2 * (3 * ((n : ℤ) + N)) by ring, csqrt_zpow_two_mul hz]
  have hzz : (z : ℂ) ^ (3 * ((n : ℤ) + N)) * (z : ℂ) ^ (-(3 * ((n : ℤ) + N))) = 1 := by
    rw [← zpow_add₀ hz]
    simp
  simp only [mul_zpow]
  calc _ = (((Complex.sqrt Complex.I)⁻¹) ^ (9 * (N : ℤ) - 3 * n) *
      ((Complex.sqrt Complex.I)⁻¹) ^ (9 * (n : ℤ) - 3 * N)) * c ^ (9 * (n : ℤ) - 3 * N) *
      ((Complex.sqrt z ^ (9 * (N : ℤ) - 3 * n) * Complex.sqrt z ^ (9 * (n : ℤ) - 3 * N)) *
        (z : ℂ) ^ (-(3 * ((n : ℤ) + N)))) *
      (ModularForm.eta z ^ (9 * (N : ℤ) - 3 * n) *
        ModularForm.eta ((z : ℂ) / 3) ^ (9 * (n : ℤ) - 3 * N)) := by ring
    _ = _ := by rw [hA2, hs, hzz]; ring

theorem psi_eq (n N : ℕ) (z : ℂ) :
    psi n N z = 𝔮 3 z ^ N *
      (etaProd z ^ (9 * (N : ℤ) - 3 * n) * etaProd (z / 3) ^ (9 * (n : ℤ) - 3 * N)) := by
  unfold psi
  rw [eta_eq_exp, eta_eq_exp, mul_zpow, mul_zpow, ← Complex.exp_int_mul, ← Complex.exp_int_mul]
  have key : Complex.exp (((9 * (N : ℤ) - 3 * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I * z / 24)) *
      Complex.exp (((9 * (n : ℤ) - 3 * N : ℤ) : ℂ) * (2 * Real.pi * Complex.I * (z / 3) / 24)) =
        𝔮 3 z ^ N := by
    rw [← Complex.exp_add]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← key]
  ring

theorem psi_add_three (n N : ℕ) (z : ℂ) : psi n N (z + 3) = psi n N z := by
  rw [psi_eq, psi_eq]
  have h1 : 𝔮 3 (z + 3) = 𝔮 3 z := qParam_three_add_int z
  have h2 : etaProd (z + 3) = etaProd z := by simpa using etaProd_add_int z 3
  have h3 : etaProd ((z + 3) / 3) = etaProd (z / 3) := by
    have := etaProd_add_int (z / 3) 1
    rw [show (z + 3) / 3 = z / 3 + 1 by ring]
    simpa using this
  rw [h1, h2, h3]

theorem tendsto_psi (n N : ℕ) : ∃ L : ℂ,
    Tendsto (fun z : ℍ => psi n N (z : ℂ)) atImInfty (𝓝 L) ∧ (1 ≤ N → L = 0) := by
  have hq : Tendsto (fun z : ℍ => 𝔮 3 (z : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num)
  have h1 := tendsto_etaProd_one.zpow₀ (9 * (N : ℤ) - 3 * n) (Or.inl one_ne_zero)
  have h3 := tendsto_etaProd_third.zpow₀ (9 * (n : ℤ) - 3 * N) (Or.inl one_ne_zero)
  have h := (hq.pow N).mul (h1.mul h3)
  rw [one_zpow, one_zpow, one_mul, mul_one] at h
  refine ⟨0 ^ N, ?_, fun hN => zero_pow (by omega)⟩
  exact h.congr (fun z => (psi_eq n N z).symm)

theorem phi_mdifferentiable (n N : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => phi n N (z : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun w : ℂ => phi n N w) (fun w hw => ?_) fun w hw => ?_
  · have hw' : 0 < w.im := hw
    have h3 : 0 < (3 * w).im := by simp; positivity
    have d1 := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw
    have d3 := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h3).comp w
      ((differentiableAt_id.const_mul (3 : ℂ)))
    unfold phi
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (d1.zpow (Or.inl (ModularForm.eta_ne_zero hw))).mul
      (d3.zpow (Or.inl (ModularForm.eta_ne_zero h3)))
  · simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]

theorem exists_form_phi (n N : ℕ) :
    ∃ F : ModularForm binaryRealGammaOneThree (3 * ((n : ℤ) + N)),
      (F : ℍ → ℂ) = fun z : ℍ => phi n N (z : ℂ) := by
  obtain ⟨K, hK⟩ := phi_slash_S n N
  obtain ⟨L, hL, hL0⟩ := tendsto_psi n N
  have hT : (fun z : ℍ => phi n N (z : ℂ)) ∣[(3 * ((n : ℤ) + N) : ℤ)]
      (ModularGroup.T : SL(2, ℤ)) = fun z : ℍ => phi n N (z : ℂ) := by
    funext z
    rw [slash_T_apply]
    simp only [UpperHalfPlane.coe_vadd]
    simpa [add_comm] using phi_add_one n N z
  have hS : ((fun z : ℍ => phi n N (z : ℂ)) ∣[(3 * ((n : ℤ) + N) : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) ∣[(3 * ((n : ℤ) + N) : ℤ)] (ModularGroup.T ^ 3 : SL(2, ℤ)) =
      (fun z : ℍ => phi n N (z : ℂ)) ∣[(3 * ((n : ℤ) + N) : ℤ)] (ModularGroup.S : SL(2, ℤ)) := by
    funext z
    rw [slash_T3_apply, hK, hK]
    simp only [UpperHalfPlane.coe_vadd]
    congr 1
    have : ((1 : ℝ) : ℂ) + (((1 : ℝ) : ℂ) + (((1 : ℝ) : ℂ) + z)) = z + 3 := by push_cast; ring
    rw [this, psi_add_three]
  have h0 : IsBoundedAtImInfty ((fun z : ℍ => phi n N (z : ℂ)) ∣[(3 * ((n : ℤ) + N) : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) := by
    have : ((fun z : ℍ => phi n N (z : ℂ)) ∣[(3 * ((n : ℤ) + N) : ℤ)]
        (ModularGroup.S : SL(2, ℤ))) = fun z : ℍ => K * psi n N (z : ℂ) := funext hK
    rw [this]
    exact ((hL.const_mul K).isBigO_one ℝ)
  exact ⟨mkForm _ _ (phi_mdifferentiable n N) hT hS (isBounded_of_hasLead (hasLead_phi n N)) h0,
    rfl⟩

/-! ### Level one: `E₄` and its dilate `E₄(3z)` -/

theorem levelOne_slash {w : ℤ} (F : ModularForm SturmBound.levelOne w) (γ : SL(2, ℤ)) :
    (⇑F : ℍ → ℂ) ∣[w] γ = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩

theorem E4_T (x : ℍ) : ModularForm.E₄ ((1 : ℝ) +ᵥ x) = ModularForm.E₄ x :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods ModularForm.E₄ x one_mem_strictPeriods_SL

theorem E4_S (x : ℍ) : ModularForm.E₄ (ModularGroup.S • x) = (x : ℂ) ^ 4 * ModularForm.E₄ x := by
  have h := congrFun (levelOne_slash ModularForm.E₄ ModularGroup.S) x
  rw [SL_slash_apply, ModularGroup.denom_S] at h
  have hx : (x : ℂ) ≠ 0 := x.ne_zero
  rw [← h, zpow_neg, zpow_ofNat]
  field_simp

/-- The point `c z` of the upper half-plane. -/
def smulH (c : ℝ) (hc : 0 < c) (z : ℍ) : ℍ :=
  ⟨(c : ℂ) * z, by simpa [Complex.mul_im] using mul_pos hc z.2⟩

@[simp]
theorem coe_smulH (c : ℝ) (hc : 0 < c) (z : ℍ) : ((smulH c hc z : ℍ) : ℂ) = (c : ℂ) * z := rfl

theorem tendsto_smulH (c : ℝ) (hc : 0 < c) : Tendsto (smulH c hc) atImInfty atImInfty := by
  have h1 : Tendsto UpperHalfPlane.im atImInfty atTop := Filter.tendsto_comap
  have h2 : Tendsto (fun z : ℍ => c * z.im) atImInfty atTop := h1.const_mul_atTop hc
  show Tendsto (smulH c hc) atImInfty (Filter.comap UpperHalfPlane.im Filter.atTop)
  refine Filter.tendsto_comap_iff.mpr ?_
  refine h2.congr (fun z => ?_)
  show c * z.im = ((c : ℂ) * (z : ℂ)).im
  simp [Complex.mul_im, UpperHalfPlane.coe_im]

theorem smulH_three_T (z : ℍ) :
    smulH 3 (by norm_num) ((1 : ℝ) +ᵥ z) =
      (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ smulH 3 (by norm_num) z)) := by
  apply UpperHalfPlane.ext
  simp only [coe_smulH, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem smulH_three_S (z : ℍ) :
    smulH 3 (by norm_num) (ModularGroup.S • z) =
      ModularGroup.S • smulH (1 / 3) (by norm_num) z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  simp only [coe_smulH]
  push_cast
  field_simp

theorem smulH_third_T (z : ℍ) :
    smulH (1 / 3) (by norm_num) ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z))) =
      (1 : ℝ) +ᵥ smulH (1 / 3) (by norm_num) z := by
  apply UpperHalfPlane.ext
  simp only [coe_smulH, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem E4_coeff_zero : (qExpansion 1 (⇑ModularForm.E₄)).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩

theorem tendsto_E4_one : Tendsto (fun z : ℍ => ModularForm.E₄ z) atImInfty (𝓝 1) := by
  have han := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E₄) one_pos
    one_mem_strictPeriods_SL
  have hq : Tendsto (fun z : ℍ => Function.Periodic.qParam 1 (z : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hc := han.continuousAt.tendsto.comp hq
  have hval : (UpperHalfPlane.cuspFunction 1 ⇑ModularForm.E₄) 0 = 1 := by
    rw [← E4_coeff_zero]
    simp [UpperHalfPlane.qExpansion]
  rw [hval] at hc
  refine hc.congr (fun τ => ?_)
  simp only [Function.comp_apply]
  exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ one_mem_strictPeriods_SL
    one_ne_zero

/-- `α E₄(z) + β E₄(3z)`. -/
def dilFun (α β : ℂ) (z : ℍ) : ℂ :=
  α * ModularForm.E₄ z + β * ModularForm.E₄ (smulH 3 (by norm_num) z)

theorem dil_slash_S (α β : ℂ) (z : ℍ) :
    (dilFun α β ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ))) z =
      α * ModularForm.E₄ z + β / 81 * ModularForm.E₄ (smulH (1 / 3) (by norm_num) z) := by
  rw [SL_slash_apply, ModularGroup.denom_S]
  unfold dilFun
  rw [E4_S, smulH_three_S, E4_S]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [zpow_neg, zpow_ofNat]
  simp only [coe_smulH]
  push_cast
  field_simp
  ring

theorem dilFun_mdifferentiable (α β : ℂ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (dilFun α β) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(ModularForm.E₄)) := ModularForm.E₄.holo'
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ => ModularForm.E₄ (smulH 3 (by norm_num) z)) := by
    have h1' := (UpperHalfPlane.mdifferentiable_iff.mp h1)
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hc : DifferentiableOn ℂ (fun w : ℂ => 3 * w) {z : ℂ | 0 < z.im} := by fun_prop
    have hm : Set.MapsTo (fun w : ℂ => 3 * w) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
      intro w hw
      have : 0 < w.im := hw
      show 0 < (3 * w).im
      simp
      positivity
    refine DifferentiableOn.congr (f := fun w : ℂ =>
      ((⇑(ModularForm.E₄) : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) (3 * w)) (h1'.comp hc hm) ?_
    intro w hw
    have hw' : 0 < w.im := hw
    have h3 : 0 < (3 * w).im := by simp; positivity
    simp only [Function.comp_apply]
    congr 1
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos h3, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    simp [smulH]
  unfold dilFun
  exact (mdifferentiable_const.mul h1).add (mdifferentiable_const.mul h2)

theorem tendsto_dilFun (α β : ℂ) : Tendsto (dilFun α β) atImInfty (𝓝 (α + β)) := by
  have h1 := tendsto_E4_one
  have h2 := tendsto_E4_one.comp (tendsto_smulH 3 (by norm_num))
  have := (h1.const_mul α).add (h2.const_mul β)
  rw [mul_one, mul_one] at this
  exact this

theorem tendsto_dilFun_slash (α β : ℂ) :
    Tendsto (fun z : ℍ => α * ModularForm.E₄ z +
      β / 81 * ModularForm.E₄ (smulH (1 / 3) (by norm_num) z)) atImInfty (𝓝 (α + β / 81)) := by
  have h1 := tendsto_E4_one
  have h2 := tendsto_E4_one.comp (tendsto_smulH (1 / 3) (by norm_num))
  have := (h1.const_mul α).add (h2.const_mul (β / 81))
  rw [mul_one, mul_one] at this
  exact this

theorem exists_form_dil (α β : ℂ) :
    ∃ F : ModularForm binaryRealGammaOneThree 4, (F : ℍ → ℂ) = dilFun α β := by
  have hT : dilFun α β ∣[(4 : ℤ)] (ModularGroup.T : SL(2, ℤ)) = dilFun α β := by
    funext z
    rw [slash_T_apply]
    unfold dilFun
    rw [E4_T, smulH_three_T, E4_T, E4_T, E4_T]
  have hS : (dilFun α β ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ))) ∣[(4 : ℤ)]
      (ModularGroup.T ^ 3 : SL(2, ℤ)) = dilFun α β ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ)) := by
    funext z
    rw [slash_T3_apply, dil_slash_S, dil_slash_S, E4_T, E4_T, E4_T, smulH_third_T, E4_T]
  have hinf : IsBoundedAtImInfty (dilFun α β) := (tendsto_dilFun α β).isBigO_one ℝ
  have h0 : IsBoundedAtImInfty (dilFun α β ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ))) := by
    have : (dilFun α β ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ))) = fun z : ℍ =>
        α * ModularForm.E₄ z + β / 81 * ModularForm.E₄ (smulH (1 / 3) (by norm_num) z) :=
      funext (dil_slash_S α β)
    rw [this]
    exact (tendsto_dilFun_slash α β).isBigO_one ℝ
  exact ⟨mkForm 4 (dilFun α β) (dilFun_mdifferentiable α β) hT hS hinf h0, rfl⟩

/-! ### The leading term of `E₄(z) - E₄(3z)` -/

theorem E4_hasDerivAt : HasDerivAt (UpperHalfPlane.cuspFunction 1 (⇑ModularForm.E₄)) 240 0 := by
  have hd := (ModularFormClass.differentiableAt_cuspFunction (f := ModularForm.E₄) one_pos
    one_mem_strictPeriods_SL (q := 0) (by simp)).hasDerivAt
  have c1 := ModularForm.E₄_qExpansion_coeff_one
  rw [UpperHalfPlane.qExpansion_coeff] at c1
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedDeriv_one] at c1
  rwa [c1] at hd

theorem E4_cusp_zero : UpperHalfPlane.cuspFunction 1 (⇑ModularForm.E₄) 0 = 1 := by
  have c0 := E4_coeff_zero
  rw [UpperHalfPlane.qExpansion_coeff] at c0
  simpa using c0

theorem cusp_E4_qParam (z : ℍ) :
    UpperHalfPlane.cuspFunction 1 (⇑ModularForm.E₄) (𝔮 1 (z : ℂ)) = ModularForm.E₄ z :=
  SlashInvariantFormClass.eq_cuspFunction (f := ModularForm.E₄) z one_mem_strictPeriods_SL
    one_ne_zero

theorem qParam_smulH_three (z : ℍ) : 𝔮 1 ((smulH 3 (by norm_num) z : ℍ) : ℂ) = 𝔮 1 (z : ℂ) ^ 3 := by
  simp only [coe_smulH, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem cusp_E4_qParam_cube (z : ℍ) :
    UpperHalfPlane.cuspFunction 1 (⇑ModularForm.E₄) (𝔮 1 (z : ℂ) ^ 3) =
      ModularForm.E₄ (smulH 3 (by norm_num) z) := by
  rw [← qParam_smulH_three]
  exact cusp_E4_qParam _

theorem hasLead_A4 : HasLead (dilFun 1 (-1)) 1 240 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp E4_hasDerivAt
  have hq : Tendsto (fun z : ℍ => 𝔮 1 (z : ℂ)) atImInfty (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_qParam,
      Eventually.of_forall fun z => Set.mem_compl_singleton_iff.mpr
        (Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ))⟩
  have hq3 : Tendsto (fun z : ℍ => 𝔮 1 (z : ℂ) ^ 3) atImInfty (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using tendsto_qParam.pow 3,
      Eventually.of_forall fun z => Set.mem_compl_singleton_iff.mpr
        (pow_ne_zero 3 (Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ)))⟩
  have h1 := hs.comp hq
  have h2 := hs.comp hq3
  have h3 : Tendsto (fun z : ℍ => 𝔮 1 (z : ℂ) ^ 2) atImInfty (𝓝 0) := by
    simpa using tendsto_qParam.pow 2
  have h4 := h1.sub (h3.mul h2)
  rw [zero_mul, sub_zero] at h4
  refine h4.congr (fun z => ?_)
  have hq0 : 𝔮 1 (z : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  simp only [Function.comp_apply, slope_def_field, dilFun]
  rw [cusp_E4_qParam, cusp_E4_qParam_cube, E4_cusp_zero]
  field_simp
  ring

theorem hasLead_B4 : HasLead (dilFun (-1) 81) 0 80 := by
  rw [hasLead_zero_iff]
  have h := tendsto_dilFun (-1) 81
  have e : (-1 : ℂ) + 81 = 80 := by norm_num
  rw [e] at h
  exact h

theorem B4_slash_zero :
    IsZeroAtImInfty (dilFun (-1) 81 ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ))) := by
  have : (dilFun (-1) 81 ∣[(4 : ℤ)] (ModularGroup.S : SL(2, ℤ))) = fun z : ℍ =>
      (-1) * ModularForm.E₄ z + (81 : ℂ) / 81 * ModularForm.E₄ (smulH (1 / 3) (by norm_num) z) :=
    funext (dil_slash_S (-1) 81)
  rw [this]
  have h := tendsto_dilFun_slash (-1) 81
  have e : (-1 : ℂ) + 81 / 81 = 0 := by norm_num
  rw [e] at h
  exact h

/-! ### Bundled forms, products, cusp forms -/

/-- `f` is the underlying function of a modular form of weight `k` for `Γ₁(3)`. -/
def IsMF (k : ℤ) (f : ℍ → ℂ) : Prop :=
  ∃ F : ModularForm binaryRealGammaOneThree k, (F : ℍ → ℂ) = f

theorem IsMF.mul {k₁ k₂ k : ℤ} (h : k₁ + k₂ = k) {f g : ℍ → ℂ} (hf : IsMF k₁ f)
    (hg : IsMF k₂ g) : IsMF k (f * g) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨G, rfl⟩ := hg
  subst h
  exact ⟨F.mul G, ModularForm.coe_mul F G⟩

theorem IsMF.bdd_slash {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (f ∣[k] γ) := by
  obtain ⟨F, rfl⟩ := hf
  exact form_bdd_slash F γ

theorem isZero_mul_isBounded {f g : ℍ → ℂ} (hf : IsZeroAtImInfty f) (hg : IsBoundedAtImInfty g) :
    IsZeroAtImInfty (f * g) := by
  have hb : IsBoundedUnder (· ≤ ·) atImInfty (norm ∘ g) := (Asymptotics.isBigO_one_iff ℝ).mp hg
  exact Filter.Tendsto.zero_mul_isBoundedUnder_le hf hb

theorem isBounded_mul_isZero {f g : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (hg : IsZeroAtImInfty g) :
    IsZeroAtImInfty (f * g) := by
  rw [mul_comm]
  exact isZero_mul_isBounded hg hf

theorem phi_slash_bdd (a b : ℕ) :
    IsBoundedAtImInfty ((fun z : ℍ => phi a b (z : ℂ)) ∣[(3 * ((a : ℤ) + b) : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) := by
  obtain ⟨K, hK⟩ := phi_slash_S a b
  obtain ⟨L, hL, -⟩ := tendsto_psi a b
  have : ((fun z : ℍ => phi a b (z : ℂ)) ∣[(3 * ((a : ℤ) + b) : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) = fun z : ℍ => K * psi a b (z : ℂ) := funext hK
  rw [this]
  exact (hL.const_mul K).isBigO_one ℝ

theorem phi_slash_zero (a b : ℕ) (hb : 1 ≤ b) :
    IsZeroAtImInfty ((fun z : ℍ => phi a b (z : ℂ)) ∣[(3 * ((a : ℤ) + b) : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) := by
  obtain ⟨K, hK⟩ := phi_slash_S a b
  obtain ⟨L, hL, hL0⟩ := tendsto_psi a b
  have : ((fun z : ℍ => phi a b (z : ℂ)) ∣[(3 * ((a : ℤ) + b) : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) = fun z : ℍ => K * psi a b (z : ℂ) := funext hK
  rw [this]
  have := hL.const_mul K
  rw [hL0 hb, mul_zero] at this
  exact this

theorem exists_cusp_product {w k : ℤ} {e : ℕ} {s : ℍ → ℂ} {Ls : ℂ} (hs : IsMF w s)
    (hlead : HasLead s e Ls) (a b : ℕ) (hk : w + 3 * ((a : ℤ) + b) = k) (hInf : 1 ≤ e + a)
    (h0 : IsZeroAtImInfty (s ∣[w] (ModularGroup.S : SL(2, ℤ))) ∨ 1 ≤ b) :
    ∃ C : CuspForm binaryRealGammaOneThree k, HasLead (C : ℍ → ℂ) (e + a) (Ls * 1) := by
  subst hk
  obtain ⟨Fphi, hFphi⟩ := exists_form_phi a b
  have hmf : IsMF (w + 3 * ((a : ℤ) + b)) (s * fun z : ℍ => phi a b (z : ℂ)) :=
    hs.mul rfl ⟨Fphi, hFphi⟩
  have hl : HasLead (s * fun z : ℍ => phi a b (z : ℂ)) (e + a) (Ls * 1) :=
    hlead.mul (hasLead_phi a b)
  have hinf' : IsZeroAtImInfty (s * fun z : ℍ => phi a b (z : ℂ)) := hl.isZeroAtImInfty hInf
  have h0' : IsZeroAtImInfty ((s * fun z : ℍ => phi a b (z : ℂ)) ∣[w + 3 * ((a : ℤ) + b)]
      (ModularGroup.S : SL(2, ℤ))) := by
    rw [ModularForm.mul_slash_SL2]
    rcases h0 with h0 | hb
    · exact isZero_mul_isBounded h0 (phi_slash_bdd a b)
    · exact isBounded_mul_isZero (hs.bdd_slash _) (phi_slash_zero a b hb)
  obtain ⟨F, hF⟩ := hmf
  have hinf : IsZeroAtImInfty (F : ℍ → ℂ) := by rw [hF]; exact hinf'
  have h0F : IsZeroAtImInfty ((F : ℍ → ℂ) ∣[w + 3 * ((a : ℤ) + b)] (ModularGroup.S : SL(2, ℤ))) := by
    rw [hF]; exact h0'
  refine ⟨toCusp F hinf h0F, ?_⟩
  rw [coe_toCusp, hF]
  exact hl

theorem le_finrank_of_seed {k w : ℤ} {e : ℕ} {s : ℍ → ℂ} {Ls : ℂ} (hs : IsMF w s)
    (hlead : HasLead s e Ls) (hLs : Ls ≠ 0) (T M a0 : ℕ) (hk : w + 3 * (T : ℤ) = k)
    (hM : a0 + M ≤ T + 1) (hInf : 1 ≤ e + a0)
    (h0 : IsZeroAtImInfty (s ∣[w] (ModularGroup.S : SL(2, ℤ))) ∨ a0 + M ≤ T) :
    M ≤ Module.finrank ℂ (CuspForm binaryRealGammaOneThree k) := by
  have key : ∀ i : Fin M, ∃ C : CuspForm binaryRealGammaOneThree k,
      HasLead (C : ℍ → ℂ) (e + (a0 + i)) (Ls * 1) := by
    intro i
    have hi : a0 + (i : ℕ) ≤ T := by have := i.2; omega
    refine exists_cusp_product hs hlead (a0 + i) (T - (a0 + i)) ?_ (by omega) ?_
    · have h2 : ((a0 + i : ℕ) : ℤ) + ((T - (a0 + i) : ℕ) : ℤ) = T := by omega
      rw [h2]
      exact hk
    · rcases h0 with h0 | h0
      · exact Or.inl h0
      · right
        have := i.2
        omega
  choose C hC using key
  refine le_finrank_of_leads C (fun i => e + (a0 + i)) (fun _ => Ls * 1) hC
    (fun _ => by simpa using hLs) ?_
  intro i j hij
  apply Fin.ext
  simpa using hij

/-! ### The three seeds and the final bound -/

theorem isMF_one : IsMF 0 (1 : ℍ → ℂ) := ⟨1, rfl⟩

theorem hasLead_one : HasLead (1 : ℍ → ℂ) 0 1 := by
  rw [hasLead_zero_iff]
  exact tendsto_const_nhds

theorem isMF_B4 : IsMF 4 (dilFun (-1) 81) := exists_form_dil (-1) 81

theorem isMF_A4 : IsMF 4 (dilFun 1 (-1)) := exists_form_dil 1 (-1)

theorem isMF_AB : IsMF (4 + 4) (dilFun 1 (-1) * dilFun (-1) 81) :=
  isMF_A4.mul rfl isMF_B4

theorem hasLead_AB : HasLead (dilFun 1 (-1) * dilFun (-1) 81) 1 (240 * 80) := by
  have h := hasLead_A4.mul hasLead_B4
  exact h

theorem AB_slash_zero :
    IsZeroAtImInfty ((dilFun 1 (-1) * dilFun (-1) 81) ∣[(4 + 4 : ℤ)]
      (ModularGroup.S : SL(2, ℤ))) := by
  rw [ModularForm.mul_slash_SL2]
  exact isBounded_mul_isZero (isMF_A4.bdd_slash _) B4_slash_zero

/-- **Lower bound.** `⌊k/3⌋ - 1 ≤ dim S_k(Γ₁(3))`. -/
theorem finrank_cuspForm_ge (k : ℤ) :
    (k / 3 - 1).toNat ≤ Module.finrank ℂ (CuspForm binaryRealGammaOneThree k) := by
  by_cases hk : k < 6
  · have : (k / 3 - 1).toNat = 0 := by omega
    omega
  · push Not at hk
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k / 3 = m := ⟨(k / 3).toNat, by omega⟩
    have hm2 : 2 ≤ m := by omega
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have htoNat : (k / 3 - 1).toNat = m - 1 := by omega
    rw [htoNat]
    rcases hcases with h | h | h
    · exact le_finrank_of_seed (w := 0) (e := 0) (s := 1) (Ls := 1) isMF_one hasLead_one one_ne_zero
        m (m - 1) 1 (by omega) (by omega) (by omega) (Or.inr (by omega))
    · exact le_finrank_of_seed (w := 4) (e := 0) (s := dilFun (-1) 81) (Ls := 80) isMF_B4
        hasLead_B4 (by norm_num) (m - 1) (m - 1) 1 (by omega) (by omega) (by omega)
        (Or.inl B4_slash_zero)
    · exact le_finrank_of_seed (w := 4 + 4) (e := 1) (s := dilFun 1 (-1) * dilFun (-1) 81)
        (Ls := 240 * 80) isMF_AB hasLead_AB (by norm_num) (m - 2) (m - 1) 0 (by omega)
        (by omega) (by omega) (Or.inl AB_slash_zero)

theorem finrank_cuspForm_eq (k : ℤ) :
    Module.finrank ℂ (CuspForm binaryRealGammaOneThree k) = (k / 3 - 1).toNat :=
  le_antisymm (SturmBound.finrank_cuspForm_le k) (finrank_cuspForm_ge k)

end TernaryPeriodPolynomials.LevelThree.LevelThreeLowerBound
