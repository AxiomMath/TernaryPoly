module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Closed

@[expose] public section


/-!
# Weak closedness and co-closedness of harmonic vectors

A vector `u` of the Hilbert space which is equivariant, orthogonal to the exact forms and to the
closedness test vectors has coefficients `a, b = S⁻¹ (ϑ^{-1/2} u)` which are locally square
integrable and weakly closed and co-closed; Weyl's lemma makes them smooth.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP mkX dir IsTest)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

/-- A vector which is equivariant, orthogonal to the exact forms and closed. -/
structure Harmonic (u : Hs d) : Prop where
  eqv : u ∈ D.eqvSub W
  orth : u ∈ (D.bSub W)ᗮ
  closed : ∀ {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) (e : Wd d),
    ⟪D.ctestVec W hψ hψU e, u⟫_ℝ = 0

/-- The unweighted `S`-coordinates of a vector. -/
def ucoef (u : Hs d) (z : ℂ) : XP (Wd d) := (Real.sqrt (W.θ z))⁻¹ • (u : ℂ → XP (Wd d)) z

/-- The first coefficient `S⁻¹` of the unweighted coordinates. -/
def acoef (u : Hs d) (z : ℂ) : Wd d := D.Sinv z (ucoef W u z).fst

/-- The second coefficient. -/
def bcoef (u : Hs d) (z : ℂ) : Wd d := D.Sinv z (ucoef W u z).snd

theorem S_acoef (u : Hs d) {z : ℂ} (hz : z ∈ U) : D.S z (D.acoef W u z) = (ucoef W u z).fst :=
  D.S_Sinv hz _

theorem S_bcoef (u : Hs d) {z : ℂ} (hz : z ∈ U) : D.S z (D.bcoef W u z) = (ucoef W u z).snd :=
  D.S_Sinv hz _

theorem ucoef_eq (u : Hs d) {z : ℂ} (hz : z ∈ U) :
    ucoef W u z = mkX (D.S z (D.acoef W u z)) (D.S z (D.bcoef W u z)) := by
  rw [D.S_acoef W u hz, D.S_bcoef W u hz]
  rfl

/-- The pairing of the coordinates of a form `fderiv φ` with `ucoef`. -/
theorem inner_ucoord_fderiv (u : Hs d) (φ : ℂ → Wd d) {z : ℂ} (hz : z ∈ U) :
    ⟪D.ucoord W (fun w => fderiv ℝ φ w) z, (u : ℂ → XP (Wd d)) z⟫_ℝ =
      ⟪fderiv ℝ φ z (dir 0), D.H z (D.acoef W u z)⟫_ℝ +
        ⟪fderiv ℝ φ z (dir 1), D.H z (D.bcoef W u z)⟫_ℝ := by
  have h : 0 < Real.sqrt (W.θ z) := Real.sqrt_pos.mpr (W.θ_pos hz)
  have e1 : ⟪D.ucoord W (fun w => fderiv ℝ φ w) z, (u : ℂ → XP (Wd d)) z⟫_ℝ =
      ⟪D.coord (fun w => fderiv ℝ φ w) z, ucoef W u z⟫_ℝ := by
    unfold ucoord ucoef
    rw [real_inner_smul_left, real_inner_smul_right]
  rw [e1, ucoef_eq D W u hz]
  unfold coord
  rw [Weyl.inner_mkX, D.inner_H, D.inner_H]
  simp [dir]

theorem memLp_coef (u : Hs d) (P : XP (Wd d) →L[ℝ] Wd d) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : MemLp (fun z => D.Sinv z (P (ucoef W u z))) 2 (volume.restrict K) := by
  have hres : (volume.restrict U).restrict K = volume.restrict K := by
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hKU]
  have hu : MemLp (u : ℂ → XP (Wd d)) 2 (volume.restrict K) := by
    have := (Lp.memLp u).restrict K
    rwa [hres] at this
  obtain ⟨Cs, hCs⟩ := hK.exists_bound_of_continuousOn ((D.continuousOn_Sinv).mono hKU)
  have hinv : ContinuousOn (fun z => (Real.sqrt (W.θ z))⁻¹) U :=
    W.continuousOn_θ.sqrt.inv₀ fun z hz => (Real.sqrt_pos.mpr (W.θ_pos hz)).ne'
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (hinv.mono hKU)
  have hum : AEStronglyMeasurable (u : ℂ → XP (Wd d)) (volume.restrict K) := hu.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun z => D.Sinv z (P (ucoef W u z))) (volume.restrict K) := by
    have h1 : AEStronglyMeasurable (fun z => ucoef W u z) (volume.restrict K) :=
      ((hinv.mono hKU).aestronglyMeasurable hK.measurableSet).smul hum
    exact (continuous_fst.clm_apply continuous_snd : Continuous
      fun p : (Wd d →L[ℂ] Wd d) × Wd d => p.1 p.2).comp_aestronglyMeasurable₂
      ((D.continuousOn_Sinv.mono hKU).aestronglyMeasurable hK.measurableSet)
      (P.continuous.comp_aestronglyMeasurable h1)
  refine (hu.norm.const_mul (Cs * C2 * ‖P‖)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have h1 : ‖D.Sinv z (P (ucoef W u z))‖ ≤ ‖D.Sinv z‖ * ‖P (ucoef W u z)‖ := (D.Sinv z).le_opNorm _
  have h2 : ‖P (ucoef W u z)‖ ≤ ‖P‖ * ‖ucoef W u z‖ := P.le_opNorm _
  have h3 : ‖ucoef W u z‖ ≤ C2 * ‖(u : ℂ → XP (Wd d)) z‖ := by
    unfold ucoef
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC2 z hz) (norm_nonneg _)
  have h4 : ‖D.Sinv z‖ ≤ Cs := hCs z hz
  calc ‖D.Sinv z (P (ucoef W u z))‖ ≤ ‖D.Sinv z‖ * (‖P‖ * ‖ucoef W u z‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ ≤ Cs * (‖P‖ * (C2 * ‖(u : ℂ → XP (Wd d)) z‖)) := by
        apply mul_le_mul h4 _ (by positivity) ((norm_nonneg _).trans h4)
        exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = Cs * C2 * ‖P‖ * ‖(u : ℂ → XP (Wd d)) z‖ := by ring

theorem memLp_acoef (u : Hs d) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    MemLp (D.acoef W u) 2 (volume.restrict K) := D.memLp_coef W u Weyl.fstX hK hKU

theorem memLp_bcoef (u : Hs d) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    MemLp (D.bcoef W u) 2 (volume.restrict K) := D.memLp_coef W u Weyl.sndX hK hKU

theorem coclosed_weak {u : Hs d} (hu : Harmonic D W u) {φ : ℂ → Wd d} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hU : tsupport φ ⊆ U) :
    ∫ z, (⟪fderiv ℝ φ z (dir 0), D.H z (D.acoef W u z)⟫_ℝ +
      ⟪fderiv ℝ φ z (dir 1), D.H z (D.bcoef W u z)⟫_ℝ) = 0 := by
  have hψ : IsTestW φ := ⟨hφ, hc, hU⟩
  have hmem : D.xvec W (Approx.good D W (avg_approx D W.hR hψ)) ∈ D.bSub W :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨D.avg φ, avg_approx D W.hR hψ, rfl⟩)
  have h0 : ⟪D.xvec W (Approx.good D W (avg_approx D W.hR hψ)), u⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hmem hu.orth
  rw [inner_xvec_avg D hψ hu.eqv] at h0
  rw [← h0]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
  · refine setIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
    exact (D.inner_ucoord_fderiv W u φ hz).symm
  · intro z hz
    have : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ fun h => hz (hU h)
    simp [this]

theorem closed_weak {u : Hs d} (hu : Harmonic D W u) {ψ : ℂ → ℝ} (hψ : IsTest ψ)
    (hψU : tsupport ψ ⊆ U) :
    ∫ z, fderiv ℝ ψ z (dir 0) • D.bcoef W u z = ∫ z, fderiv ℝ ψ z (dir 1) • D.acoef W u z := by
  have hla : LocallyIntegrableOn (D.acoef W u) U volume :=
    Weyl.locInt_of_locL2 isOpen_U fun K hK hKU => D.memLp_acoef W u hK hKU
  have hlb : LocallyIntegrableOn (D.bcoef W u) U volume :=
    Weyl.locInt_of_locL2 isOpen_U fun K hK hKU => D.memLp_bcoef W u hK hKU
  have hcont : ∀ j : Fin 2, Continuous fun z => fderiv ℝ ψ z (dir j) := fun j =>
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : ∀ j : Fin 2, HasCompactSupport fun z => fderiv ℝ ψ z (dir j) := fun j =>
    Weyl.hasCompactSupport_fderiv_apply hψ.2 _
  have hts : ∀ j : Fin 2, tsupport (fun z => fderiv ℝ ψ z (dir j)) ⊆ U := fun j =>
    (Weyl.tsupport_fderiv_apply_subset _).trans hψU
  have i0 := Weyl.integrable_cutoff_smul hlb (hcont 0) (hcs 0) (hts 0)
  have i1 := Weyl.integrable_cutoff_smul hla (hcont 1) (hcs 1) (hts 1)
  refine ext_inner_left ℝ fun e => ?_
  rw [← integral_inner (𝕜 := ℝ) i0 e, ← integral_inner (𝕜 := ℝ) i1 e]
  simp only [real_inner_smul_right]
  have h0 := hu.closed hψ hψU e
  unfold ctestVec at h0
  rw [MeasureTheory.L2.inner_def] at h0
  have h1 : ∫ z in U, ⟪D.uctest W ψ e z, (u : ℂ → XP (Wd d)) z⟫_ℝ = 0 := by
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [(D.memLp_uctest W hψ hψU e).coeFn_toLp] with z hz
    rw [hz]
  have h2 : ∀ z ∈ U, ⟪D.uctest W ψ e z, (u : ℂ → XP (Wd d)) z⟫_ℝ =
      fderiv ℝ ψ z (dir 0) * ⟪e, D.bcoef W u z⟫_ℝ - fderiv ℝ ψ z (dir 1) * ⟪e, D.acoef W u z⟫_ℝ := by
    intro z hz
    have h : 0 < Real.sqrt (W.θ z) := Real.sqrt_pos.mpr (W.θ_pos hz)
    have e1 : ⟪D.uctest W ψ e z, (u : ℂ → XP (Wd d)) z⟫_ℝ = ⟪D.ctest ψ e z, ucoef W u z⟫_ℝ := by
      unfold uctest ucoef
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [e1, ucoef_eq D W u hz]
    unfold ctest
    rw [Weyl.inner_mkX, real_inner_smul_left, real_inner_smul_left, D.inner_Tvec hz, D.inner_Tvec hz]
    ring
  rw [setIntegral_congr_fun isOpen_U.measurableSet h2] at h1
  have hz : ∀ z ∉ U, fderiv ℝ ψ z (dir 0) * ⟪e, D.bcoef W u z⟫_ℝ -
      fderiv ℝ ψ z (dir 1) * ⟪e, D.acoef W u z⟫_ℝ = 0 := by
    intro z hz
    have : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ fun h => hz (hψU h)
    simp [this]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_sub (i0.const_inner e |>.congr (Eventually.of_forall fun z => by
      simp [real_inner_smul_right])) (i1.const_inner e |>.congr (Eventually.of_forall fun z => by
      simp [real_inner_smul_right]))] at h1
  simpa [real_inner_smul_right] using sub_eq_zero.mp h1

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
