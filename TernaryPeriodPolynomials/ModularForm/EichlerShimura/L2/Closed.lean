module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Unfold
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Strong

@[expose] public section



/-!
# Closedness of exact forms

Smooth functions on `U` have symmetric second derivatives, hence `∫ ∂₀ψ • ∂₁φ = ∫ ∂₁ψ • ∂₀φ` for
compactly supported test functions `ψ` (`ibp_closed`).  The differential of a function satisfying the
cocycle law is equivariant (`eqv_fderiv_cocycle`).

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

/-- The differential of a function with the cocycle law is equivariant. -/
theorem HodgeDatum.eqv_fderiv_cocycle (D : HodgeDatum Γ d) {φ : ℂ → Wd d} (c : Γ → Wd d)
    (hφ : DifferentiableOn ℝ φ U)
    (h : ∀ δ : Γ, ∀ z ∈ U, φ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (φ z) + c δ) :
    D.Eqv (fun z => fderiv ℝ φ z) := by
  intro γ w hw
  rw [D.slash_fderiv γ hφ hw]
  have hev : (fun z => D.ρR γ⁻¹ (φ (mob (γ : SL(2, ℤ)) z))) =ᶠ[𝓝 w]
      fun z => φ z + D.ρR γ⁻¹ (c γ) := by
    filter_upwards [isOpen_U.mem_nhds hw] with z hz
    rw [h γ z hz, map_add]
    have h2 := congrArg (fun T : Wd d →L[ℂ] Wd d => T (φ z)) (D.ρ.map_mul γ⁻¹ γ)
    simp only [inv_mul_cancel, map_one] at h2
    congr 1
    exact h2.symm
  rw [hev.fderiv_eq]
  have hd : DifferentiableAt ℝ φ w := hφ.differentiableAt (isOpen_U.mem_nhds hw)
  exact fderiv_add_const _

theorem fderiv_symm_at {φ : ℂ → Wd d} {z : ℂ} (hφ : ContDiffAt ℝ ∞ φ z) (e₀ e₁ : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ φ z e₁) z e₀ = fderiv ℝ (fun z => fderiv ℝ φ z e₀) z e₁ := by
  have h : ∀ e, fderiv ℝ (fun z => fderiv ℝ φ z e) z = (fderiv ℝ (fderiv ℝ φ) z).flip e := by
    intro e
    have hc : DifferentiableAt ℝ (fderiv ℝ φ) z :=
      (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    rw [fderiv_clm_apply hc (differentiableAt_const e)]
    simp
  rw [h, h]
  have := ContDiffAt.isSymmSndFDerivAt hφ (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [ContinuousLinearMap.flip_apply]
  exact this e₀ e₁

theorem ibp_closed {φ : ℂ → Wd d} (hφ : ContDiffOn ℝ ∞ φ U) {ψ : ℂ → ℝ} (hψ : IsTest ψ)
    (hψU : tsupport ψ ⊆ U) :
    ∫ z, fderiv ℝ ψ z (dir 0) • fderiv ℝ φ z (dir 1) =
      ∫ z, fderiv ℝ ψ z (dir 1) • fderiv ℝ φ z (dir 0) := by
  have hg : ∀ e, ContDiffOn ℝ ∞ (fun z => fderiv ℝ φ z e) U := fun e =>
    (hφ.fderiv_of_isOpen isOpen_U (m := ∞) (by simp)).clm_apply contDiffOn_const
  have h0 := Weyl.ibp_testU isOpen_U hψ hψU (hg (dir 1)) 0
  have h1 := Weyl.ibp_testU isOpen_U hψ hψU (hg (dir 0)) 1
  have hs : ∫ z, ψ z • fderiv ℝ (fun z => fderiv ℝ φ z (dir 1)) z (dir 0) =
      ∫ z, ψ z • fderiv ℝ (fun z => fderiv ℝ φ z (dir 0)) z (dir 1) := by
    have hc : ∀ z ∉ U, ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hψU h))
    have e : ∀ z, ψ z • fderiv ℝ (fun z => fderiv ℝ φ z (dir 1)) z (dir 0) =
        ψ z • fderiv ℝ (fun z => fderiv ℝ φ z (dir 0)) z (dir 1) := by
      intro z
      by_cases hz : z ∈ U
      · rw [fderiv_symm_at ((hφ.contDiffAt (isOpen_U.mem_nhds hz))) (dir 0) (dir 1)]
      · rw [hc z hz]; simp
    simp_rw [e]
  rw [h0, h1] at hs
  exact neg_injective hs

namespace HodgeDatum

variable (D : HodgeDatum Γ d)

/-- The inverse of `S z`. -/
def Sinv (z : ℂ) : Wd d →L[ℂ] Wd d := Ring.inverse (D.S z)

theorem S_Sinv {z : ℂ} (hz : z ∈ U) (y : Wd d) : D.S z (D.Sinv z y) = y := by
  have := Ring.mul_inverse_cancel (D.S z) (D.S_unit z hz)
  exact congrArg (fun T : Wd d →L[ℂ] Wd d => T y) this

theorem continuousOn_Sinv : ContinuousOn D.Sinv U := by
  intro z hz
  obtain ⟨u, hu⟩ := D.S_unit z hz
  have hcs : CompleteSpace (Wd d →L[ℂ] Wd d) := ContinuousLinearMap.instCompleteSpace
  have hsg : HasSummableGeomSeries (Wd d →L[ℂ] Wd d) := inferInstance
  have h1 : ContinuousAt Ring.inverse (D.S z) := by
    rw [← hu]; exact NormedRing.inverse_continuousAt u
  exact h1.comp_continuousWithinAt (D.S_smooth.continuousOn z hz)

/-- The vector `S (H⁻¹ e)`: pairing it with `S x` gives `⟪e, x⟫`. -/
def Tvec (e : Wd d) (z : ℂ) : Wd d := D.S z (Weyl.invField D.H z e)

theorem inner_Tvec {z : ℂ} (hz : z ∈ U) (e x : Wd d) : ⟪D.Tvec e z, D.S z x⟫_ℝ = ⟪e, x⟫_ℝ := by
  unfold Tvec
  rw [← D.inner_H, D.hField.selfAdj_inv z hz]
  have := congrArg (fun T : Wd d →L[ℝ] Wd d => T x) (D.hField.inv_mul z hz)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  rw [this]

theorem continuousOn_Tvec (e : Wd d) : ContinuousOn (D.Tvec e) U := by
  have h1 : ContinuousOn (fun z => Weyl.invField D.H z e) U :=
    D.hField.smooth_inv.continuousOn.clm_apply continuousOn_const
  exact D.S_smooth.continuousOn.clm_apply h1

/-- The test covector pairing with the coordinates of `L` to
`∂₀ψ ⟪e, L z I⟫ - ∂₁ψ ⟪e, L z 1⟫`. -/
def ctest (ψ : ℂ → ℝ) (e : Wd d) (z : ℂ) : XP (Wd d) :=
  mkX (-(fderiv ℝ ψ z (dir 1)) • D.Tvec e z) (fderiv ℝ ψ z (dir 0) • D.Tvec e z)

theorem inner_ctest (ψ : ℂ → ℝ) (e : Wd d) (L : Form d) {z : ℂ} (hz : z ∈ U) :
    ⟪D.ctest ψ e z, D.coord L z⟫_ℝ =
      fderiv ℝ ψ z (dir 0) * ⟪e, L z Complex.I⟫_ℝ - fderiv ℝ ψ z (dir 1) * ⟪e, L z 1⟫_ℝ := by
  unfold ctest coord
  rw [Weyl.inner_mkX, real_inner_smul_left, real_inner_smul_left, D.inner_Tvec hz, D.inner_Tvec hz]
  ring

theorem continuousOn_ctest {ψ : ℂ → ℝ} (hψ : IsTest ψ) (e : Wd d) :
    ContinuousOn (D.ctest ψ e) U := by
  have hd : ∀ j, Continuous fun z => fderiv ℝ ψ z (dir j) := fun j =>
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : ContinuousOn (fun z => -(fderiv ℝ ψ z (dir 1)) • D.Tvec e z) U :=
    (hd 1).neg.continuousOn.smul (D.continuousOn_Tvec e)
  have h2 : ContinuousOn (fun z => fderiv ℝ ψ z (dir 0) • D.Tvec e z) U :=
    (hd 0).continuousOn.smul (D.continuousOn_Tvec e)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Wd d) (Wd d)).symm.continuous.comp_continuousOn
    (h1.prodMk h2)

theorem integral_closed_zero {φ : ℂ → Wd d} (hφ : ContDiffOn ℝ ∞ φ U) {ψ : ℂ → ℝ} (hψ : IsTest ψ)
    (hψU : tsupport ψ ⊆ U) (e : Wd d) :
    ∫ z in U, (fderiv ℝ ψ z (dir 0) * ⟪e, fderiv ℝ φ z (dir 1)⟫_ℝ -
      fderiv ℝ ψ z (dir 1) * ⟪e, fderiv ℝ φ z (dir 0)⟫_ℝ) = 0 := by
  have hgl : ∀ j : Fin 2, LocallyIntegrableOn (fun z => fderiv ℝ φ z (dir j)) U volume := fun j =>
    (((hφ.fderiv_of_isOpen isOpen_U (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn).locallyIntegrableOn isOpen_U.measurableSet
  have hcont : ∀ j : Fin 2, Continuous fun z => fderiv ℝ ψ z (dir j) := fun j =>
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : ∀ j : Fin 2, HasCompactSupport fun z => fderiv ℝ ψ z (dir j) := fun j =>
    Weyl.hasCompactSupport_fderiv_apply hψ.2 _
  have hts : ∀ j : Fin 2, tsupport (fun z => fderiv ℝ ψ z (dir j)) ⊆ U := fun j =>
    (Weyl.tsupport_fderiv_apply_subset _).trans hψU
  have i0 : Integrable fun z => fderiv ℝ ψ z (dir 0) • fderiv ℝ φ z (dir 1) :=
    Weyl.integrable_cutoff_smul (hgl 1) (hcont 0) (hcs 0) (hts 0)
  have i1 : Integrable fun z => fderiv ℝ ψ z (dir 1) • fderiv ℝ φ z (dir 0) :=
    Weyl.integrable_cutoff_smul (hgl 0) (hcont 1) (hcs 1) (hts 1)
  have h := ibp_closed hφ hψ hψU
  have e0 := integral_inner (𝕜 := ℝ) i0 e
  have e1 := integral_inner (𝕜 := ℝ) i1 e
  simp only [real_inner_smul_right] at e0 e1
  have hz : ∀ z ∉ U, fderiv ℝ ψ z (dir 0) * ⟪e, fderiv ℝ φ z (dir 1)⟫_ℝ -
      fderiv ℝ ψ z (dir 1) * ⟪e, fderiv ℝ φ z (dir 0)⟫_ℝ = 0 := by
    intro z hz
    have : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ fun h => hz (hψU h)
    simp [this]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_sub (i0.const_inner e |>.congr
    (Eventually.of_forall fun z => by simp [real_inner_smul_right])) (i1.const_inner e |>.congr
    (Eventually.of_forall fun z => by simp [real_inner_smul_right])), e0, e1, h, sub_self]

variable (W : Weights Γ)

/-- The weighted test covector, in the form used in the Hilbert space. -/
def uctest (ψ : ℂ → ℝ) (e : Wd d) (z : ℂ) : XP (Wd d) := (Real.sqrt (W.θ z))⁻¹ • D.ctest ψ e z

theorem memLp_uctest {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) (e : Wd d) :
    MemLp (D.uctest W ψ e) 2 (volume.restrict U) := by
  have hcont : ContinuousOn (D.uctest W ψ e) U :=
    (W.continuousOn_θ.sqrt.inv₀ fun z hz => (Real.sqrt_pos.mpr (W.θ_pos hz)).ne').smul
      (D.continuousOn_ctest hψ e)
  refine memLp_of_cpt hcont hψ.2 hψU fun z hz hzK => ?_
  have : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ hzK
  have e0 : mkX (0 : Wd d) 0 = 0 := rfl
  simp [uctest, ctest, this, e0]

/-- The Hilbert space vector dual to the closedness test `(ψ, e)`. -/
def ctestVec {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) (e : Wd d) : Hs d :=
  (D.memLp_uctest W hψ hψU e).toLp _

theorem inner_ctestVec_xvec {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) (e : Wd d)
    {L : Form d} (hL : Good D W L) :
    ⟪D.ctestVec W hψ hψU e, D.xvec W hL⟫_ℝ = ∫ z in U, ⟪D.ctest ψ e z, D.coord L z⟫_ℝ := by
  unfold ctestVec xvec
  rw [inner_toLp_eq]
  refine setIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
  have h : 0 < Real.sqrt (W.θ z) := Real.sqrt_pos.mpr (W.θ_pos hz)
  simp only [uctest, wcoord, real_inner_smul_left, real_inner_smul_right]
  field_simp

theorem ctestVec_orth {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) (e : Wd d)
    {φ : ℂ → Wd d} (hφ : ContDiffOn ℝ ∞ φ U) (hL : Good D W (fun z => fderiv ℝ φ z)) :
    ⟪D.ctestVec W hψ hψU e, D.xvec W hL⟫_ℝ = 0 := by
  rw [inner_ctestVec_xvec]
  rw [← integral_closed_zero hφ hψ hψU e]
  refine setIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
  rw [D.inner_ctest ψ e _ hz]
  simp [dir]

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
