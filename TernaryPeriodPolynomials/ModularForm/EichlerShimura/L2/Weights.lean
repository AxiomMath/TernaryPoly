module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Energy

@[expose] public section


/-!
# The weight and finite energy

`Weights Γ` packages a cover `R` and positive weights `a γ` summing to `1`; `θ` is the resulting
continuous weight.  For a function `G` whose hyperbolic version `Im² G` is `Γ`-invariant, integrating
`G` against `θ` over the upper half plane is the same as integrating it against the cutoff
(`lintegral_theta_flat`), and an equivariant continuous form with support compact modulo `Γ` has
finite `θ`-weighted energy (`lintegral_theta_edens_lt_top`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)

/-- A cover of `SL(2, ℤ)` by cosets of `Γ` together with positive weights on `Γ` summing to one. -/
structure Weights (Γ : Subgroup SL(2, ℤ)) where
  R : Finset SL(2, ℤ)
  hR : IsCover Γ R
  a : Γ → ℝ
  ha : ∀ γ, 0 < a γ
  hs : HasSum a 1

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

instance [Γ.FiniteIndex] : Nonempty (Weights Γ) := by
  obtain ⟨R, hR⟩ := Partition.exists_cosetReps Γ
  obtain ⟨a, ha, hs⟩ := exists_weights Γ
  exact ⟨⟨R, hR, a, ha, hs⟩⟩

namespace Weights

variable (W : Weights Γ)

/-- The weight `ϑ`. -/
def θ (z : ℂ) : ℝ := theta Γ W.R W.a z

/-- The cutoff of the cover. -/
def χ (z : ℂ) : ℝ := cutoff Γ W.R z

theorem θ_nonneg (z : ℂ) : 0 ≤ W.θ z := theta_nonneg W.ha z

theorem θ_pos {z : ℂ} (hz : z ∈ U) : 0 < W.θ z := theta_pos W.hR W.ha W.hs hz

theorem θ_le_one (z : ℂ) : W.θ z ≤ 1 := theta_le_one W.hR W.ha W.hs z

theorem continuousOn_θ : ContinuousOn W.θ U := continuousOn_theta W.hR W.ha W.hs

theorem χ_nonneg (z : ℂ) : 0 ≤ W.χ z := cutoff_nonneg Γ W.R z

theorem χ_le_one {z : ℂ} (hz : z ∈ U) : W.χ z ≤ 1 := cutoff_le_one Γ W.R W.hR hz

theorem continuousOn_χ : ContinuousOn W.χ U := (Partition.contDiffOn_cutoff Γ W.R W.hR).continuousOn

theorem tsum_θ_comp {w : ℂ} (hw : w ∈ U) :
    HasSum (fun γ : Γ => W.θ (mob (γ : SL(2, ℤ)) w)) 1 :=
  hasSum_theta_comp W.hR W.ha W.hs hw

theorem aemeasurable_ofReal_of_continuousOn {f : ℂ → ℝ} (hf : ContinuousOn f U) :
    AEMeasurable (fun z => ENNReal.ofReal (f z)) (volume.restrict U) :=
  (ENNReal.measurable_ofReal.comp_aemeasurable (hf.aemeasurable isOpen_U.measurableSet))

/-- Unfolding with the weight, in flat form: if `Im² G` is invariant then `θ` can be replaced by the
cutoff. -/
theorem lintegral_theta_flat {G : ℂ → ℝ} (hG : ContinuousOn G U)
    (hinv : ∀ γ : Γ, ∀ z ∈ U, (mob (γ : SL(2, ℤ)) z).im ^ 2 * G (mob (γ : SL(2, ℤ)) z) = z.im ^ 2 * G z) :
    ∫⁻ z in U, ENNReal.ofReal (W.θ z) * ENNReal.ofReal (G z) =
      ∫⁻ z in U, ENNReal.ofReal (W.χ z) * ENNReal.ofReal (G z) := by
  set n : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (z.im ^ 2 * G z) with hn
  have hGc : ContinuousOn (fun z : ℂ => z.im ^ 2 * G z) U :=
    ((Complex.continuous_im.pow 2).continuousOn).mul hG
  have hnm : AEMeasurable n hmeas :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_hmeas hGc)
  have key : ∀ f : ℂ → ℝ, ContinuousOn f U → (∀ z, 0 ≤ f z) →
      ∫⁻ z in U, ENNReal.ofReal (f z) * ENNReal.ofReal (G z) = ∫⁻ z, ENNReal.ofReal (f z) * n z ∂hmeas := by
    intro f hf hf0
    rw [lintegral_hmeas (f := fun z => ENNReal.ofReal (f z) * n z)
      ((aemeasurable_ofReal_of_continuousOn hf).mul (aemeasurable_ofReal_of_continuousOn hGc))]
    refine setLIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
    have hy : 0 < z.im := hz
    simp only [hn]
    have h1 : ENNReal.ofReal (1 / z.im ^ 2) * ENNReal.ofReal (z.im ^ 2 * G z) =
        ENNReal.ofReal (G z) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [mul_left_comm, h1]
  rw [key W.θ W.continuousOn_θ W.θ_nonneg, key W.χ W.continuousOn_χ W.χ_nonneg]
  exact lintegral_theta_mul W.hR W.ha W.hs hnm fun γ z hz => by
    simp only [hn]
    rw [hinv γ z hz]

theorem continuousOn_edens (D : HodgeDatum Γ d) {L : Form d} (hL : ContinuousOn L U) :
    ContinuousOn (D.edens L) U := by
  have h1 : ContinuousOn (fun z => D.S z (L z 1)) U :=
    D.S_smooth.continuousOn.clm_apply (hL.clm_apply continuousOn_const)
  have h2 : ContinuousOn (fun z => D.S z (L z Complex.I)) U :=
    D.S_smooth.continuousOn.clm_apply (hL.clm_apply continuousOn_const)
  exact (h1.norm.pow 2).add (h2.norm.pow 2)

theorem lintegral_theta_edens (D : HodgeDatum Γ d) {L : Form d} (hL : ContinuousOn L U)
    (hE : D.Eqv L) :
    ∫⁻ z in U, ENNReal.ofReal (W.θ z) * ENNReal.ofReal (D.edens L z) =
      ∫⁻ z in U, ENNReal.ofReal (W.χ z) * ENNReal.ofReal (D.edens L z) := by
  refine W.lintegral_theta_flat (continuousOn_edens D hL) fun γ z hz => ?_
  have h := D.Pinv_mob_of_eqv hE hE γ hz
  simpa only [HodgeDatum.Pinv, HodgeDatum.pairE_self] using h

theorem lintegral_χ_edens_lt_top (D : HodgeDatum Γ d) {L : Form d} (hL : ContinuousOn L U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hz0 : ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → L z = 0) :
    ∫⁻ z in U, ENNReal.ofReal (W.χ z) * ENNReal.ofReal (D.edens L z) < ⊤ := by
  have hfin := Partition.finite_translates_of_isCompact Γ W.R hK hKU
  set C : Set ℂ := ⋃ γ ∈ hfin.toFinset, (fun k => mob (γ : SL(2, ℤ))⁻¹ k) '' K with hC
  have hCc : IsCompact C := by
    refine (hfin.toFinset.finite_toSet).isCompact_biUnion fun γ _ => ?_
    exact hK.image_of_continuousOn
      ((Partition.contDiffOn_mob ((γ : SL(2, ℤ))⁻¹) (n := 0)).continuousOn.mono hKU)
  have hCU : C ⊆ U := by
    intro z hz
    obtain ⟨γ, -, k, -, rfl⟩ := Set.mem_iUnion₂.mp hz
    exact Partition.mob_mem _ _
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn ((continuousOn_edens D hL).mono hCU)
  have hsupp : ∀ z ∈ U, ENNReal.ofReal (W.χ z) * ENNReal.ofReal (D.edens L z) ≤
      C.indicator (fun _ => ENNReal.ofReal M) z := by
    intro z hz
    by_cases hzC : z ∈ C
    · rw [Set.indicator_of_mem hzC]
      calc ENNReal.ofReal (W.χ z) * ENNReal.ofReal (D.edens L z) ≤ 1 * ENNReal.ofReal M := by
            gcongr
            · exact ENNReal.ofReal_le_one.mpr (W.χ_le_one hz)
            · exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM z hzC)
        _ = _ := one_mul _
    · rw [Set.indicator_of_notMem hzC]
      by_cases hχ : W.χ z = 0
      · simp [hχ]
      · have hL0 : L z = 0 := by
          refine hz0 z hz fun γ hγ => hzC ?_
          have e : mob ((γ : SL(2, ℤ))⁻¹) (mob (γ : SL(2, ℤ)) z) = z := by
            rw [← mob_mul, inv_mul_cancel, mob_one hz]
          refine Set.mem_iUnion₂.mpr ⟨γ, ?_, mob (γ : SL(2, ℤ)) z, hγ, e⟩
          rw [Set.Finite.mem_toFinset]
          exact ⟨mob (γ : SL(2, ℤ)) z, hγ, by
            show cutoff Γ W.R _ ≠ 0
            rw [e]; exact hχ⟩
        simp [HodgeDatum.edens, hL0]
  calc ∫⁻ z in U, ENNReal.ofReal (W.χ z) * ENNReal.ofReal (D.edens L z)
      ≤ ∫⁻ z in U, C.indicator (fun _ => ENNReal.ofReal M) z :=
        setLIntegral_mono' isOpen_U.measurableSet hsupp
    _ ≤ ∫⁻ z, C.indicator (fun _ => ENNReal.ofReal M) z := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal M * volume C := by
        rw [lintegral_indicator_const hCc.isClosed.measurableSet]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCc.measure_lt_top

/-- **Finite energy**: an equivariant continuous form whose support is compact modulo `Γ` has
finite `θ`-weighted energy. -/
theorem lintegral_θ_edens_lt_top (D : HodgeDatum Γ d) {L : Form d} (hL : ContinuousOn L U)
    (hE : D.Eqv L) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hz0 : ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → L z = 0) :
    ∫⁻ z in U, ENNReal.ofReal (W.θ z) * ENNReal.ofReal (D.edens L z) < ⊤ := by
  rw [W.lintegral_theta_edens D hL hE]
  exact W.lintegral_χ_edens_lt_top D hL hK hKU hz0

end Weights

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
