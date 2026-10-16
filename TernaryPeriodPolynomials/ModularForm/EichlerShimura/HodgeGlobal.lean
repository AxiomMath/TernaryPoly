module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeGlobalTerm

@[expose] public section


/-!
# The global vanishing of the middle Hodge pairs

Foundation file of the unconditional Eichler--Shimura route.  Let `a, b` be smooth on the upper half plane, satisfying the pair system
`2iy ∂_z̄ a = (m-k) a - (k+1) b = 2iy ∂_z b` with `m = k + 1 + r` (`r ≥ 0`, i.e. `0 ≤ k < m`),
the automorphy laws of the Hodge frame components of an equivariant form under `Γ`, and
`∫ cutoff · y^m (|a|² + |b|²) < ∞` (the finite energy, expressed through the partition of unity).
Then `a = b = 0` (`middle_pair_vanish`).

Proof: with the truncated partition of unity `χ_T = cutoff · heightCutoff T`, the divergence
identity `HodgePair.pair_energy` gives `∫ χ_T Φ = ∫ ∂_z̄χ_T · W`; the term with `∂_z̄ cutoff`
cancels
(`HodgeGlobalTerm.integral_termF_eq_zero`), the term with `∂_z̄ heightCutoff` is `O(1/log T)` times
the energy, and `∫ χ_T Φ` is nondecreasing in `T` and nonnegative; hence it vanishes.

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory
open scoped ContDiff MatrixGroups
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.Height

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Global

variable {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}

/-- The (unweighted) Hodge energy density of a pair, `y^m ((m-k)|a|² + (k+1)|b|²)`. -/
def pairPhi (m k : ℕ) (a b : ℂ → ℂ) (z : ℂ) : ℝ :=
  z.im ^ m * (((m : ℝ) - k) * ‖a z‖ ^ 2 + ((k : ℝ) + 1) * ‖b z‖ ^ 2)

/-- The truncated cutoff-weighted energy integrand. -/
def truncEnergy (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (T : ℝ) (m k : ℕ) (a b : ℂ → ℂ)
    (z : ℂ) : ℝ :=
  if z ∈ U then cutoff Γ R z * heightCutoff T z * pairPhi m k a b z else 0

/-- The remaining term `cutoff · ∂_z̄ θ · W`. -/
def termG (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (T : ℝ) (m : ℕ) (a b : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  if z ∈ U then ((cutoff Γ R z : ℝ) : ℂ) * dbar (fun w => ((heightCutoff T w : ℝ) : ℂ)) z *
    pairW m a b z else 0

theorem pair_energy_trunc (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m k : ℕ} {a b : ℂ → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (h1 : ∀ z ∈ U, 2 * I * ht z * dbar a z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z)
    (h2 : ∀ z ∈ U, 2 * I * ht z * dz b z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z) :
    ((∫ z : ℂ, truncEnergy Γ R T m k a b z : ℝ) : ℂ) =
      ∫ z : ℂ, dbar (chi Γ R T) z * pairW m a b z := by
  obtain ⟨hχ, hcs, hsupp⟩ := chi_regular hR hT
  have h := pair_energy m k (ha.of_le (by simp)) (hb.of_le (by simp)) h1 h2
    (hχ.of_le (by simp)) hcs hsupp
  rw [← h, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ U
  · simp only [truncEnergy, chi, pairPhi, hz, ite_true, ht]
    push_cast
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  · simp [truncEnergy, chi, hz]

theorem dbar_eq_zero_of_notMem {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport f) : dbar f z = 0 := by
  have h : fderiv ℝ f z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fderiv ℝ f) (fun h => hz (tsupport_fderiv_subset ℝ h))
  simp [dbar, h]

theorem integrable_termF (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m : ℕ} {a b : ℂ → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    Integrable (termF Γ R T m a b) := by
  obtain ⟨Kc, hKc, hKU, hKs, -⟩ := termF_support (m := m) (a := a) (b := b) hR hT
  have h1 : IntegrableOn (termF Γ R T m a b) Kc :=
    (continuousOn_termF hR hT ha hb).mono hKU |>.integrableOn_compact hKc
  rwa [integrableOn_iff_integrable_of_support_subset] at h1

theorem integral_dbar_chi_mul (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m : ℕ} {a b : ℂ → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hF0 : ∫ z : ℂ, termF Γ R T m a b z = 0) :
    ∫ z : ℂ, dbar (chi Γ R T) z * pairW m a b z = ∫ z : ℂ, termG Γ R T m a b z := by
  obtain ⟨hχ, hcs, hsupp⟩ := chi_regular hR hT
  have hdc : Continuous (dbar (chi Γ R T)) := by
    unfold dbar
    have := hχ.continuous_fderiv (by simp)
    exact continuous_const.mul ((this.clm_apply continuous_const).add
      (continuous_const.mul (this.clm_apply continuous_const)))
  have hsub : Function.support (dbar (chi Γ R T)) ⊆ tsupport (chi Γ R T) := by
    intro z hz
    by_contra h
    exact hz (dbar_eq_zero_of_notMem h)
  have hdcs : HasCompactSupport (dbar (chi Γ R T)) :=
    HasCompactSupport.of_support_subset_isCompact hcs hsub
  have hdsupp : tsupport (dbar (chi Γ R T)) ⊆ U :=
    (closure_minimal hsub isClosed_closure).trans hsupp
  have hW : ContinuousOn (pairW m a b) U :=
    (contDiffOn_pairW m (ha.of_le (by simp)) (hb.of_le (by simp))).continuousOn
  have hint1 : Integrable (fun z => dbar (chi Γ R T) z * pairW m a b z) :=
    integrable_cs hdc hdcs hdsupp hW
  have hint2 := integrable_termF hR hT (m := m) ha hb
  have hpt : ∀ z, dbar (chi Γ R T) z * pairW m a b z =
      termF Γ R T m a b z + termG Γ R T m a b z := by
    intro z
    by_cases hz : z ∈ U
    · rw [dbar_chi hR hT hz]
      simp only [termF, termG, hz, ite_true]
      ring
    · have : dbar (chi Γ R T) z = 0 := dbar_eq_zero_of_notMem (fun h => hz (hsupp h))
      simp [this, termF, termG, hz]
  have hint3 : Integrable (termG Γ R T m a b) := by
    have := hint1.sub hint2
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, hpt z]
    ring
  simp_rw [hpt]
  rw [integral_add hint2 hint3, hF0, zero_add]

/-- The cutoff-weighted energy density `cutoff · y^m (|a|² + |b|²)`. -/
def energyDen (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (m : ℕ) (a b : ℂ → ℂ) (z : ℂ) : ℝ :=
  if z ∈ U then cutoff Γ R z * (z.im ^ m * (‖a z‖ ^ 2 + ‖b z‖ ^ 2)) else 0

theorem norm_termG_le {T : ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hT : 1 < T)
    (hC : ∀ z ∈ U, ‖(z.im : ℂ) * dbar (fun w => ((heightCutoff T w : ℝ) : ℂ)) z‖ ≤ C / Real.log T)
    (m : ℕ) (a b : ℂ → ℂ) (z : ℂ) :
    ‖termG Γ R T m a b z‖ ≤ (C / Real.log T) * energyDen Γ R m a b z := by
  by_cases hz : z ∈ U
  · simp only [termG, energyDen, hz, ite_true]
    have hy : 0 < z.im := hz
    have hlog : 0 < Real.log T := Real.log_pos hT
    have h1 := hC z hz
    have hW : ‖pairW m a b z‖ = 2 * z.im ^ (m + 1) * (‖a z‖ * ‖b z‖) := by
      simp [pairW, ht, norm_pow, abs_of_pos hy]
    rw [norm_mul, norm_mul, hW]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg Γ R z)]
    set D := ‖dbar (fun w => ((heightCutoff T w : ℝ) : ℂ)) z‖ with hD
    have hD' : z.im * D ≤ C / Real.log T := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy] at h1
      exact h1
    have hcut := cutoff_nonneg Γ R z
    have hym : 0 ≤ z.im ^ m := by positivity
    have hab : 2 * (‖a z‖ * ‖b z‖) ≤ ‖a z‖ ^ 2 + ‖b z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a z‖ - ‖b z‖)]
    have hCl : 0 ≤ C / Real.log T := div_nonneg hC0 hlog.le
    calc cutoff Γ R z * D * (2 * z.im ^ (m + 1) * (‖a z‖ * ‖b z‖))
        = cutoff Γ R z * (z.im * D) * (z.im ^ m * (2 * (‖a z‖ * ‖b z‖))) := by ring
      _ ≤ cutoff Γ R z * (C / Real.log T) * (z.im ^ m * (‖a z‖ ^ 2 + ‖b z‖ ^ 2)) := by
          gcongr
      _ = _ := by ring
  · simp [termG, energyDen, hz]

theorem continuousOn_pairPhi {m k : ℕ} {a b : ℂ → ℂ} (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b U) : ContinuousOn (pairPhi m k a b) U := by
  unfold pairPhi
  have h1 : ContinuousOn (fun z : ℂ => z.im ^ m) U := (Complex.continuous_im.pow m).continuousOn
  have h2 : ContinuousOn (fun z => ‖a z‖ ^ 2) U := (ha.continuousOn.norm).pow 2
  have h3 : ContinuousOn (fun z => ‖b z‖ ^ 2) U := (hb.continuousOn.norm).pow 2
  exact h1.mul ((continuousOn_const.mul h2).add (continuousOn_const.mul h3))

theorem pairPhi_nonneg {m k : ℕ} (hk : k < m) (a b : ℂ → ℂ) {z : ℂ} (hz : z ∈ U) :
    0 ≤ pairPhi m k a b z := by
  have hy : 0 < z.im := hz
  unfold pairPhi
  have : (0 : ℝ) ≤ (m : ℝ) - k := by
    have : (k : ℝ) < m := by exact_mod_cast hk
    linarith
  positivity

theorem truncEnergy_nonneg {m k : ℕ} (hk : k < m) (T : ℝ) (a b : ℂ → ℂ) (z : ℂ) :
    0 ≤ truncEnergy Γ R T m k a b z := by
  unfold truncEnergy
  split_ifs with hz
  · exact mul_nonneg (mul_nonneg (cutoff_nonneg Γ R z) (heightCutoff_nonneg T z))
      (pairPhi_nonneg hk a b hz)
  · exact le_rfl

theorem truncEnergy_mono {m k : ℕ} (hk : k < m) {T T' : ℝ} (hT : 1 < T) (hTT : T ≤ T') (a b : ℂ → ℂ)
    (z : ℂ) : truncEnergy Γ R T m k a b z ≤ truncEnergy Γ R T' m k a b z := by
  unfold truncEnergy
  split_ifs with hz
  · have h := heightCutoff_mono hT hTT z
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (cutoff_nonneg Γ R z))
      (pairPhi_nonneg hk a b hz)
  · exact le_rfl

theorem continuousOn_truncEnergy (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m k : ℕ}
    {a b : ℂ → ℂ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContinuousOn (truncEnergy Γ R T m k a b) U := by
  have h1 : ContinuousOn (cutoff Γ R) U := (contDiffOn_cutoff Γ R hR).continuousOn
  have h2 : ContinuousOn (heightCutoff T) U := (contDiffOn_heightCutoff hT).continuousOn
  have h3 := continuousOn_pairPhi (m := m) (k := k) ha hb
  refine ((h1.mul h2).mul h3).congr fun z hz => ?_
  simp [truncEnergy, hz]

theorem integrable_truncEnergy (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m k : ℕ}
    {a b : ℂ → ℂ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    Integrable (truncEnergy Γ R T m k a b) := by
  obtain ⟨Kc, hKc, hKU, hK⟩ := exists_compact_support Γ R hT
  have h1 : IntegrableOn (truncEnergy Γ R T m k a b) Kc :=
    ((continuousOn_truncEnergy hR hT ha hb).mono hKU).integrableOn_compact hKc
  rwa [integrableOn_iff_integrable_of_support_subset] at h1
  intro z hz
  by_cases hzU : z ∈ U
  · refine hK z hzU ?_
    intro h0
    apply hz
    simp [truncEnergy, hzU, h0]
  · exact absurd hz (by simp [truncEnergy, hzU])

theorem energyDen_nonneg (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (m : ℕ) (a b : ℂ → ℂ)
    (z : ℂ) : 0 ≤ energyDen Γ R m a b z := by
  unfold energyDen
  split_ifs with hz
  · have hy : 0 < z.im := hz
    exact mul_nonneg (cutoff_nonneg Γ R z) (by positivity)
  · exact le_rfl

theorem exists_cutoff_ne_zero (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U) :
    ∃ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 := by
  by_contra h
  have h' : ∀ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) = 0 := fun γ => by
    by_contra hne
    exact h ⟨γ, hne⟩
  have h1 := finsum_cutoff (Γ := Γ) (R := R) hR hz
  rw [finsum_eq_zero_of_forall_eq_zero h'] at h1
  exact zero_ne_one h1

/-- **The middle pairs vanish.** -/
theorem middle_pair_vanish (hR : IsCover Γ R) {m k r : ℕ} (hm : m = k + 1 + r)
    {a b : ℂ → ℂ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (h1 : ∀ z ∈ U, 2 * Complex.I * ht z * dbar a z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z)
    (h2 : ∀ z ∈ U, 2 * Complex.I * ht z * dz b z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z)
    (hA : ∀ γ ∈ Γ, ∀ z ∈ U, a (mob γ z) = den γ z ^ 2 *
      (den γ z ^ k * (starRingEnd ℂ (den γ z)) ^ (m - k)) * a z)
    (hB : ∀ γ ∈ Γ, ∀ z ∈ U, b (mob γ z) = starRingEnd ℂ (den γ z ^ 2) *
      (den γ z ^ (k + 1) * (starRingEnd ℂ (den γ z)) ^ (m - (k + 1))) * b z)
    (hE : Integrable (energyDen Γ R m a b)) :
    ∀ z ∈ U, a z = 0 ∧ b z = 0 := by
  have hk : k < m := by omega
  obtain ⟨C, hC0, hC⟩ := exists_norm_im_mul_dbar_le
  set E := ∫ z, energyDen Γ R m a b z with hEdef
  have hE0 : 0 ≤ E := integral_nonneg (energyDen_nonneg Γ R m a b)
  have hbound : ∀ T : ℝ, 1 < T →
      |∫ z, truncEnergy Γ R T m k a b z| ≤ C / Real.log T * E := by
    intro T hT
    have hen := pair_energy_trunc hR hT ha hb h1 h2
    rw [integral_dbar_chi_mul hR hT ha hb (integral_termF_eq_zero hR hT hm ha hb hA hB)] at hen
    have hnorm : ‖∫ z, termG Γ R T m a b z‖ ≤ ∫ z, C / Real.log T * energyDen Γ R m a b z :=
      norm_integral_le_of_norm_le (hE.const_mul _) (Filter.Eventually.of_forall fun z =>
        norm_termG_le hC0 hT (fun z hz => hC T hT z hz) m a b z)
    rw [integral_const_mul, ← hen] at hnorm
    simpa using hnorm
  have hnn : ∀ T : ℝ, 0 ≤ ∫ z, truncEnergy Γ R T m k a b z := fun T =>
    integral_nonneg (truncEnergy_nonneg hk T a b)
  have hzero : ∀ T0 : ℝ, 1 < T0 → ∫ z, truncEnergy Γ R T0 m k a b z = 0 := by
    intro T0 hT0
    by_contra hne
    have hpos : 0 < ∫ z, truncEnergy Γ R T0 m k a b z := lt_of_le_of_ne (hnn T0) (Ne.symm hne)
    have htend : Filter.Tendsto (fun T : ℝ => C / Real.log T * E) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := C)).div_atTop Real.tendsto_log_atTop
      simpa using this.mul_const E
    obtain ⟨T, hTlt, hTge⟩ := ((htend.eventually (gt_mem_nhds hpos)).and
      (Filter.eventually_ge_atTop (max T0 2))).exists
    have hT1 : 1 < T := by
      have := le_max_right T0 2
      linarith
    have hT0T : T0 ≤ T := le_trans (le_max_left _ _) hTge
    have hmono : ∫ z, truncEnergy Γ R T0 m k a b z ≤ ∫ z, truncEnergy Γ R T m k a b z :=
      integral_mono (integrable_truncEnergy (m := m) (k := k) hR hT0 ha hb)
        (integrable_truncEnergy (m := m) (k := k) hR hT1 ha hb)
        (fun z => truncEnergy_mono hk hT0 hT0T a b z)
    have := hbound T hT1
    have := le_abs_self (∫ z, truncEnergy Γ R T m k a b z)
    linarith
  intro z0 hz0
  obtain ⟨γ, hγ⟩ := exists_cutoff_ne_zero hR hz0
  set w := mob (γ : SL(2, ℤ))⁻¹ z0 with hw
  have hwU : w ∈ U := mob_mem _ _
  set T0 : ℝ := max 2 (height z0) with hT0def
  have hT0 : 1 < T0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hint := integrable_truncEnergy (m := m) (k := k) hR hT0 ha hb
  have hae : truncEnergy Γ R T0 m k a b =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (truncEnergy_nonneg hk T0 a b) hint).mp (hzero T0 hT0)
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_U
    (continuousOn_truncEnergy hR hT0 ha hb) continuousOn_const
  have hw0 : truncEnergy Γ R T0 m k a b w = 0 := heq hwU
  have hθ : heightCutoff T0 w = 1 := by
    apply heightCutoff_eq_one hT0
    rw [hw, height_mob]
    exact le_max_right _ _
  simp only [truncEnergy, hwU, ite_true, hθ, mul_one] at hw0
  have hcw : cutoff Γ R w ≠ 0 := hγ
  have hΦ : pairPhi m k a b w = 0 := (mul_eq_zero.mp hw0).resolve_left hcw
  have hy : 0 < w.im := hwU
  have hcoef1 : (0 : ℝ) < (m : ℝ) - k := by
    have : (k : ℝ) < m := by exact_mod_cast hk
    linarith
  have hcoef2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsum : ((m : ℝ) - k) * ‖a w‖ ^ 2 + ((k : ℝ) + 1) * ‖b w‖ ^ 2 = 0 := by
    unfold pairPhi at hΦ
    exact (mul_eq_zero.mp hΦ).resolve_left (by positivity)
  have haw : a w = 0 := by
    have : ‖a w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a w‖, sq_nonneg ‖b w‖]
    exact norm_eq_zero.mp (by simpa using this)
  have hbw : b w = 0 := by
    have : ‖b w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a w‖, sq_nonneg ‖b w‖]
    exact norm_eq_zero.mp (by simpa using this)
  have hz0eq : z0 = mob (γ : SL(2, ℤ)) w := by
    rw [hw, ← mob_mul, mul_inv_cancel, mob_one hz0]
  refine ⟨?_, ?_⟩
  · rw [hz0eq, hA γ γ.2 w hwU, haw, mul_zero]
  · rw [hz0eq, hB γ γ.2 w hwU, hbw, mul_zero]

end TernaryPeriodPolynomials.Argument.ESFoundations.Global
