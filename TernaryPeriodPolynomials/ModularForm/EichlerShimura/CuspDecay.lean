module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.ConeMeanValue
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HyperbolicLintegral
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CutoffCalculus
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Horoball
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HeightCutoff

@[expose] public section


/-!
# Decay of `L²` holomorphic modular forms at the cusps

Foundation file of the unconditional Eichler--Shimura route.  Let `Λ ≤ SL(2, ℤ)` have finite index and not contain `-1`, `f` holomorphic on the
upper half plane with `f(γ z) = (cz+d)^{m+2} f(z)` for `γ ∈ Λ` and finite energy
`∫ cutoff · y^m |f|² < ∞`.  For every `g ∈ SL(2, ℤ)` the slash `hs g = (f ∣ g)` satisfies
`(π r² / 3) |hs g (z)|² ≤ (Im z - r)^{-m} · ∫ cutoff y^m |f|²` for `Im z > 1 + r` (`decay_bound`):
the cone sub-mean-value inequality (`ConeMeanValue`) bounds `|hs g (z)|²` by the cone-weighted
energy of a disc around `z` of radius `r` in the horoball at `g ∞`; the disc injects into the
quotient by `Λ` (`disc_injective`, from the cyclicity of the cusp stabiliser in `Horoball`), so by
unfolding along the partition of unity (`lintegral_unfold_cutoff`) this energy is at most the total
energy.

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups NNReal ENNReal Real
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.Global
open TernaryPeriodPolynomials.Argument.ESFoundations
  (horoballAt cuspStab cuspStab_eq_zpowers transLen mem_cuspStab_of_horoball)

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CuspL2

open ModularGroup in
/-- **Injectivity of the quotient map on thin slabs of a horoball**: for a finite-index `Λ`
without `-1` and a cusp `g ∞`, there is `h > 0` such that two `Λ`-translates of a point `u` whose
`g⁻¹`-images lie in the horoball `Im > 1` at horizontal distance `< h` coincide. -/
theorem disc_injective (Λ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∉ Λ)
    (g : SL(2, ℤ)) :
    ∃ h : ℤ, 0 < h ∧ ∀ γ ∈ Λ, ∀ γ' ∈ Λ, ∀ u : ℍ, 1 < (g⁻¹ • γ • u).im →
      1 < (g⁻¹ • γ' • u).im → |(g⁻¹ • γ' • u).re - (g⁻¹ • γ • u).re| < h → γ = γ' := by
  obtain ⟨γ₁, hγ₁, hpos, hcyc, ε, hε, hform⟩ := cuspStab_eq_zpowers Λ hneg g
  set h := transLen (g⁻¹ * γ₁ * g) with hh
  refine ⟨h, hpos, fun γ hγ γ' hγ' u h1 h2 hre => ?_⟩
  have hmemΛ : γ' * γ⁻¹ ∈ Λ := Λ.mul_mem hγ' (Λ.inv_mem hγ)
  have hw1 : γ • u ∈ horoballAt g := by simpa [horoballAt] using h1
  have hw2 : (γ' * γ⁻¹) • (γ • u) ∈ horoballAt g := by
    rw [← mul_smul, inv_mul_cancel_right]; simpa [horoballAt] using h2
  have hstab := mem_cuspStab_of_horoball hmemΛ hw1 hw2
  rw [hcyc, Subgroup.mem_zpowers_iff] at hstab
  obtain ⟨j, hj⟩ := hstab
  have hd : g⁻¹ * γ₁ * g = ε * ModularGroup.T ^ h := by rw [hform]; group
  have hact : ∀ w : ℍ, (ε * ModularGroup.T ^ h) • w = ModularGroup.T ^ h • w := by
    intro w
    rcases hε with rfl | rfl
    · simp
    · rw [neg_one_mul, ModularGroup.SL_neg_smul]
  have hconj : g⁻¹ * (γ' * γ⁻¹) * g = (ε * ModularGroup.T ^ h) ^ j := by
    rw [← hj, ← hd]
    have := conj_zpow (a := g⁻¹) (b := γ₁) (i := j)
    simpa using this.symm
  have hperm : ∀ w : ℍ, ((ε * ModularGroup.T ^ h) ^ j) • w = (ModularGroup.T ^ h) ^ j • w := by
    intro w
    have e : MulAction.toPermHom SL(2, ℤ) ℍ (ε * ModularGroup.T ^ h) =
        MulAction.toPermHom SL(2, ℤ) ℍ (ModularGroup.T ^ h) := Equiv.ext hact
    calc ((ε * ModularGroup.T ^ h) ^ j) • w
        = ((MulAction.toPermHom SL(2, ℤ) ℍ (ε * ModularGroup.T ^ h)) ^ j) w := by
          rw [← map_zpow]; rfl
      _ = ((MulAction.toPermHom SL(2, ℤ) ℍ (ModularGroup.T ^ h)) ^ j) w := by rw [e]
      _ = (ModularGroup.T ^ h) ^ j • w := by rw [← map_zpow]; rfl
  have hz2 : g⁻¹ • γ' • u = (g⁻¹ * (γ' * γ⁻¹) * g) • (g⁻¹ • γ • u) := by
    simp [mul_smul]
  have hre' : (g⁻¹ • γ' • u).re = (g⁻¹ • γ • u).re + (h * j : ℤ) := by
    rw [hz2, hconj, hperm, ← zpow_mul, ModularGroup.re_T_zpow_smul]
  rw [hre'] at hre
  simp only [add_sub_cancel_left] at hre
  have hj0 : j = 0 := by
    by_contra hne
    have : (h : ℝ) ≤ |((h * j : ℤ) : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |j| := Int.one_le_abs hne
      have h2 : h ≤ |h * j| := by
        rw [abs_mul, abs_of_pos hpos]
        nlinarith
      exact_mod_cast h2
    linarith
  rw [hj0, zpow_zero] at hj
  have : γ' * γ⁻¹ = 1 := hj.symm
  exact (mul_inv_eq_one.mp this).symm


variable {Λ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)} {m : ℕ} {f : ℂ → ℂ}

/-- The invariant density `|f|² y^{m+2}` on `ℍ`. -/
def Gh (m : ℕ) (f : ℂ → ℂ) (z : ℍ) : ℝ := ‖f (z : ℂ)‖ ^ 2 * z.im ^ (m + 2)

theorem Gh_smul (hmod : ∀ γ ∈ Λ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Λ) (z : ℍ) : Gh m f (γ • z) = Gh m f z := by
  have hz : (z : ℂ) ∈ U := z.im_pos
  have hD : den γ z ≠ 0 := denom_ne_zero' γ hz
  have h1 : f ((γ • z : ℍ) : ℂ) = den γ z ^ (m + 2) * f z := by
    rw [← mob_coe]; exact hmod γ hγ z hz
  have h2 : (γ • z : ℍ).im = z.im / ‖den γ z‖ ^ 2 := by
    have := Height.norm_denom_sq γ hz
    rw [mob_coe] at this
    exact this
  unfold Gh
  rw [h1, h2, norm_mul, norm_pow]
  have hn : ‖den γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  rw [div_pow, ← pow_mul]
  field_simp
  ring

theorem measurable_ite_U {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] {φ : ℂ → α} (hφ : ContinuousOn φ U)
    [Zero α] [T2Space α] :
    Measurable fun z => if z ∈ U then φ z else 0 := by
  have := hφ.measurable_piecewise (g := fun _ => (0 : α)) continuousOn_const isOpen_U.measurableSet
  convert this using 1
  funext z
  simp [Set.piecewise]

/-- The slash by `g ∈ SL(2, ℤ)` of `f` (a function on `ℂ`), weight `m + 2`. -/
def hs (m : ℕ) (f : ℂ → ℂ) (g : SL(2, ℤ)) (w : ℂ) : ℂ := f (mob g w) * (den g w ^ (m + 2))⁻¹

theorem differentiableOn_hs (hf : DifferentiableOn ℂ f U) (g : SL(2, ℤ)) :
    DifferentiableOn ℂ (hs m f g) U := by
  have hmob : DifferentiableOn ℂ (mob g) U := fun z hz =>
    (Height.hasDerivAt_mob g hz).differentiableAt.differentiableWithinAt
  have hden : DifferentiableOn ℂ (fun w => den g w ^ (m + 2)) U := by
    have : DifferentiableOn ℂ (fun w : ℂ => ((g 1 0 : ℤ) : ℂ) * w + ((g 1 1 : ℤ) : ℂ)) U :=
      (differentiableOn_const _ |>.mul differentiableOn_id).add (differentiableOn_const _)
    exact (this.pow (m + 2))
  exact (hf.comp hmob (mapsTo_mob g)).mul (hden.inv fun z hz =>
    pow_ne_zero _ (denom_ne_zero' g hz))

theorem hs_norm_sq (g : SL(2, ℤ)) (w : ℍ) :
    ‖hs m f g (w : ℂ)‖ ^ 2 * w.im ^ (m + 2) = Gh m f (g • w) := by
  have hz : (w : ℂ) ∈ U := w.im_pos
  have hD : den g w ≠ 0 := denom_ne_zero' g hz
  have h2 : (g • w : ℍ).im = w.im / ‖den g w‖ ^ 2 := by
    have := Height.norm_denom_sq g hz
    rw [mob_coe] at this
    exact this
  have h1 : f ((g • w : ℍ) : ℂ) = f (mob g w) := by rw [mob_coe]
  unfold hs Gh
  rw [h1, h2, norm_mul, norm_inv, norm_pow]
  have hn : ‖den g w‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  rw [div_pow, ← pow_mul]
  field_simp
  ring

/-- The cone weight centred at `z₀` of radius `r`. -/
def coneW (z0 : ℂ) (r : ℝ) (z : ℂ) : ℝ := max 0 (1 - ‖z - z0‖ / r)

theorem coneW_nonneg (z0 : ℂ) (r : ℝ) (z : ℂ) : 0 ≤ coneW z0 r z := le_max_left _ _

theorem coneW_le_one {r : ℝ} (hr : 0 < r) (z0 z : ℂ) : coneW z0 r z ≤ 1 := by
  refine max_le zero_le_one ?_
  have : 0 ≤ ‖z - z0‖ / r := by positivity
  linarith

theorem continuous_coneW (z0 : ℂ) (r : ℝ) : Continuous (coneW z0 r) := by
  unfold coneW
  exact continuous_const.max
    (continuous_const.sub ((continuous_id.sub continuous_const).norm.div_const r))

/-- The weighted `L²` density `cutoff · y^m |f|²` (zero off the upper half plane). -/
def L2dens (Λ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if z ∈ U then cutoff Λ R z * (z.im ^ m * ‖f z‖ ^ 2) else 0

theorem measurable_L2dens (hR : IsCover Λ R) (hf : DifferentiableOn ℂ f U) :
    Measurable (L2dens Λ R m f) := by
  have h1 : ContinuousOn (cutoff Λ R) U := (contDiffOn_cutoff Λ R hR).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => cutoff Λ R z * (z.im ^ m * ‖f z‖ ^ 2)) U :=
    h1.mul (((Complex.continuous_im.pow m).continuousOn).mul (hf.continuousOn.norm.pow 2))
  exact measurable_ite_U h2

theorem continuous_Gh (hf : DifferentiableOn ℂ f U) : Continuous (Gh m f) := by
  unfold Gh
  have : ContinuousOn f U := hf.continuousOn
  exact ((this.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)).norm.pow 2).mul
    ((UpperHalfPlane.continuous_im).pow _)

theorem lintegral_L2dens (hR : IsCover Λ R) (hf : DifferentiableOn ℂ f U) :
    ∫⁻ z : ℂ, ENNReal.ofReal (L2dens Λ R m f z) =
      ∫⁻ u : ℍ, ENNReal.ofReal (cutoff Λ R (u : ℂ) * Gh m f u) ∂volume := by
  rw [lintegral_flat_eq_hyp (fun z => ENNReal.ofReal (L2dens Λ R m f z))
    (ENNReal.measurable_ofReal.comp (measurable_L2dens hR hf))
    (fun x hx => by simp [L2dens, hx])]
  refine lintegral_congr fun u => ?_
  have hu : (u : ℂ) ∈ U := u.im_pos
  have hcut := cutoff_nonneg Λ R (u : ℂ)
  simp only [L2dens, hu, ite_true, Gh, UpperHalfPlane.coe_im]
  rw [← ENNReal.ofReal_mul (by
    have : 0 ≤ (u.im : ℝ) ^ m := by have := u.im_pos; positivity
    positivity)]
  congr 1
  ring

/-- The cone-weighted slashed density. -/
def Wfun (m : ℕ) (f : ℂ → ℂ) (g : SL(2, ℤ)) (z0 : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  if z ∈ U then coneW z0 r z * ‖hs m f g z‖ ^ 2 * z.im ^ m else 0

theorem measurable_Wfun (hf : DifferentiableOn ℂ f U) (g : SL(2, ℤ)) (z0 : ℂ) (r : ℝ) :
    Measurable (Wfun m f g z0 r) := by
  have h1 : ContinuousOn (hs m f g) U := (differentiableOn_hs hf g).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => coneW z0 r z * ‖hs m f g z‖ ^ 2 * z.im ^ m) U :=
    ((continuous_coneW z0 r).continuousOn.mul (h1.norm.pow 2)).mul
      (Complex.continuous_im.pow m).continuousOn
  exact measurable_ite_U h2

/-- The reduced density on the quotient: `ψ(g⁻¹ u) G(u)`. -/
def Ft (m : ℕ) (f : ℂ → ℂ) (g : SL(2, ℤ)) (z0 : ℂ) (r : ℝ) (u : ℍ) : ℝ≥0∞ :=
  ENNReal.ofReal (coneW z0 r ((g⁻¹ • u : ℍ) : ℂ) * Gh m f u)

theorem measurable_Ft (hf : DifferentiableOn ℂ f U) (g : SL(2, ℤ)) (z0 : ℂ) (r : ℝ) :
    Measurable (Ft m f g z0 r) := by
  have : Continuous fun u : ℍ => coneW z0 r ((g⁻¹ • u : ℍ) : ℂ) * Gh m f u := by
    refine ((continuous_coneW z0 r).comp (UpperHalfPlane.continuous_coe.comp ?_)).mul
      (continuous_Gh hf)
    exact (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ g⁻¹) :
      Continuous fun u : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ g⁻¹) • u)
  exact ENNReal.measurable_ofReal.comp this.measurable

theorem lintegral_Wfun_eq (hf : DifferentiableOn ℂ f U) (g : SL(2, ℤ)) (z0 : ℂ) (r : ℝ) :
    ∫⁻ z : ℂ, ENNReal.ofReal (Wfun m f g z0 r z) = ∫⁻ u : ℍ, Ft m f g z0 r u ∂volume := by
  rw [lintegral_flat_eq_hyp (fun z => ENNReal.ofReal (Wfun m f g z0 r z))
    (ENNReal.measurable_ofReal.comp (measurable_Wfun hf g z0 r))
    (fun x hx => by simp [Wfun, hx])]
  rw [← lintegral_smul_hyp g (Ft m f g z0 r)]
  refine lintegral_congr fun v => ?_
  have hv : (v : ℂ) ∈ U := v.im_pos
  have hcut := coneW_nonneg z0 r (v : ℂ)
  simp only [Wfun, hv, ite_true, Ft, inv_smul_smul]
  rw [← ENNReal.ofReal_mul (by
    have : 0 ≤ (v : ℂ).im ^ m := pow_nonneg v.im_pos.le m
    positivity)]
  congr 1
  have := hs_norm_sq (m := m) (f := f) g v
  simp only [UpperHalfPlane.coe_im]
  calc coneW z0 r (v : ℂ) * ‖hs m f g (v : ℂ)‖ ^ 2 * v.im ^ m * v.im ^ 2
      = coneW z0 r (v : ℂ) * (‖hs m f g (v : ℂ)‖ ^ 2 * v.im ^ (m + 2)) := by ring
    _ = _ := by rw [this]

theorem coneW_ne_zero_iff {r : ℝ} (hr : 0 < r) {z0 z : ℂ} :
    coneW z0 r z ≠ 0 ↔ ‖z - z0‖ < r := by
  unfold coneW
  constructor
  · intro h
    by_contra hge
    push Not at hge
    apply h
    apply max_eq_left
    have : 1 ≤ ‖z - z0‖ / r := by rw [le_div_iff₀ hr]; linarith
    linarith
  · intro h
    have : 0 < 1 - ‖z - z0‖ / r := by
      have : ‖z - z0‖ / r < 1 := (div_lt_one hr).2 h
      linarith
    exact (lt_max_of_lt_right this).ne'

theorem lintegral_Ft_le (hR : IsCover Λ R) (hf : DifferentiableOn ℂ f U)
    (hmod : ∀ γ ∈ Λ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z) (g : SL(2, ℤ))
    {h : ℤ} (hinj : ∀ γ ∈ Λ, ∀ γ' ∈ Λ, ∀ u : ℍ, 1 < (g⁻¹ • γ • u).im →
      1 < (g⁻¹ • γ' • u).im → |(g⁻¹ • γ' • u).re - (g⁻¹ • γ • u).re| < h → γ = γ')
    {z0 : ℂ} {r : ℝ} (hr : 0 < r) (hrh : 2 * r < h) (hz0 : 1 + r < z0.im) :
    ∫⁻ u : ℍ, Ft m f g z0 r u ∂volume ≤
      ∫⁻ u : ℍ, ENNReal.ofReal (cutoff Λ R (u : ℂ) * Gh m f u) ∂volume := by
  rw [lintegral_unfold_cutoff hR (Ft m f g z0 r) (measurable_Ft hf g z0 r)]
  refine lintegral_mono fun u => ?_
  rw [ENNReal.ofReal_mul (cutoff_nonneg Λ R _)]
  refine mul_le_mul' le_rfl ?_
  have hbd : ∀ γ : Λ, coneW z0 r (((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ)) : ℂ) ≠ 0 →
      1 < (g⁻¹ • (γ : SL(2, ℤ)) • u).im ∧
        |((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ)).re - z0.re| < r := by
    intro γ hne
    have hlt := (coneW_ne_zero_iff hr).1 hne
    have him : |((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ) : ℂ).im - z0.im| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_im] using
        Complex.abs_im_le_norm (((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ) : ℂ) - z0)) hlt
    have hre : |((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ) : ℂ).re - z0.re| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_re] using
        Complex.abs_re_le_norm (((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ) : ℂ) - z0)) hlt
    refine ⟨?_, hre⟩
    have := (abs_lt.1 him).1
    simp only [UpperHalfPlane.coe_im] at this
    linarith
  by_cases hex : ∃ γ0 : Λ, coneW z0 r (((g⁻¹ • (γ0 : SL(2, ℤ)) • u : ℍ)) : ℂ) ≠ 0
  · obtain ⟨γ0, h0⟩ := hex
    have hnz : ∀ γ : Λ, coneW z0 r (((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ)) : ℂ) ≠ 0 → γ = γ0 := by
      intro γ hγ
      obtain ⟨i1, r1⟩ := hbd γ hγ
      obtain ⟨i0, r0⟩ := hbd γ0 h0
      have : |((g⁻¹ • (γ0 : SL(2, ℤ)) • u : ℍ)).re - ((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ)).re| < h := by
        have h1 := abs_lt.1 r1
        have h2 := abs_lt.1 r0
        rw [abs_lt]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      exact Subtype.ext (hinj _ γ.2 _ γ0.2 u i1 i0 this)
    rw [tsum_eq_single γ0 (fun γ hγ => ?_)]
    · unfold Ft
      rw [Gh_smul hmod γ0.2 u]
      refine ENNReal.ofReal_le_ofReal ?_
      have hG : 0 ≤ Gh m f u := by
        unfold Gh; have := u.im_pos; positivity
      calc _ ≤ 1 * Gh m f u := mul_le_mul_of_nonneg_right (coneW_le_one hr _ _) hG
        _ = _ := one_mul _
    · unfold Ft
      have : coneW z0 r (((g⁻¹ • (γ : SL(2, ℤ)) • u : ℍ)) : ℂ) = 0 := by
        by_contra hne
        exact hγ (hnz γ hne)
      rw [Gh_smul hmod γ.2 u, this, zero_mul, ENNReal.ofReal_zero]
  · push Not at hex
    have : ∀ γ : Λ, Ft m f g z0 r ((γ : SL(2, ℤ)) • u) = 0 := by
      intro γ
      unfold Ft
      rw [Gh_smul hmod γ.2 u, hex γ, zero_mul, ENNReal.ofReal_zero]
    rw [tsum_congr this, tsum_zero]
    exact zero_le

/-- **The decay estimate**: the slash `hs g` of an `L²` holomorphic modular form satisfies
`(π r² / 3) |hs g (z₀)|² ≤ (Im z₀ - r)^{-m} ∫ cutoff y^m |f|²` for `Im z₀ > 1 + r`. -/
theorem decay_bound [Λ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∉ Λ) (hR : IsCover Λ R)
    (hf : DifferentiableOn ℂ f U)
    (hmod : ∀ γ ∈ Λ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z) (g : SL(2, ℤ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ z0 : ℂ, 1 + r < z0.im →
      ENNReal.ofReal (π * r ^ 2 / 3 * ‖hs m f g z0‖ ^ 2) ≤
        ENNReal.ofReal (((z0.im - r) ^ m)⁻¹) *
          ∫⁻ z : ℂ, ENNReal.ofReal (L2dens Λ R m f z) := by
  obtain ⟨h, hpos, hinj⟩ := disc_injective Λ hneg g
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hpos
  set r : ℝ := min (1 / 2) ((h : ℝ) / 3) with hrdef
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrh : 2 * r < h := by
    have : r ≤ (h : ℝ) / 3 := min_le_right _ _
    linarith
  refine ⟨r, hr, fun z0 hz0 => ?_⟩
  have hz0pos : 0 < z0.im := by linarith
  have hball : Metric.closedBall z0 r ⊆ U := by
    intro z hz
    have h1 : ‖z - z0‖ ≤ r := by simpa [dist_eq_norm] using hz
    have h2 : |z.im - z0.im| ≤ r := by
      have := Complex.abs_im_le_norm (z - z0)
      simp only [Complex.sub_im] at this
      linarith
    have := (abs_le.1 h2).1
    show 0 < z.im
    have hr1 : r ≤ 1 / 2 := min_le_left _ _
    linarith
  have hdiff : DifferentiableOn ℂ (hs m f g) (Metric.closedBall z0 r) :=
    (differentiableOn_hs hf g).mono hball
  refine (ConeMeanValue.cone_lintegral_ge hr hdiff).trans ?_
  have hpos' : 0 < z0.im - r := by linarith
  -- pointwise bound
  have hpt : ∀ z : ℂ, ENNReal.ofReal (ConeMeanValue.coneG (hs m f g) z0 r z) ≤
      ENNReal.ofReal (((z0.im - r) ^ m)⁻¹) * ENNReal.ofReal (Wfun m f g z0 r z) := by
    intro z
    by_cases hz : z ∈ Metric.closedBall z0 r
    · have hzU := hball hz
      have h1 : ‖z - z0‖ ≤ r := by simpa [dist_eq_norm] using hz
      have h2 : z0.im - r ≤ z.im := by
        have := Complex.abs_im_le_norm (z - z0)
        simp only [Complex.sub_im] at this
        have := (abs_le.1 (this.trans h1)).1
        linarith
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [ConeMeanValue.coneG, Set.indicator_of_mem hz, Wfun, hzU, ite_true]
      have hpw : (z0.im - r) ^ m ≤ z.im ^ m := pow_le_pow_left₀ hpos'.le h2 m
      have hW : 0 ≤ coneW z0 r z * ‖hs m f g z‖ ^ 2 := mul_nonneg (coneW_nonneg _ _ _) (sq_nonneg _)
      have : coneW z0 r z = max 0 (1 - ‖z - z0‖ / r) := rfl
      rw [← this]
      calc coneW z0 r z * ‖hs m f g z‖ ^ 2
          = ((z0.im - r) ^ m)⁻¹ * ((z0.im - r) ^ m * (coneW z0 r z * ‖hs m f g z‖ ^ 2)) := by
            field_simp
        _ ≤ ((z0.im - r) ^ m)⁻¹ * (z.im ^ m * (coneW z0 r z * ‖hs m f g z‖ ^ 2)) := by
            gcongr
        _ = _ := by ring
    · have : ConeMeanValue.coneG (hs m f g) z0 r z = 0 := by
        unfold ConeMeanValue.coneG
        rw [Set.indicator_of_notMem hz]; simp
      rw [this, ENNReal.ofReal_zero]
      exact zero_le
  calc ∫⁻ z : ℂ, ENNReal.ofReal (ConeMeanValue.coneG (hs m f g) z0 r z)
      ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((z0.im - r) ^ m)⁻¹) * ENNReal.ofReal (Wfun m f g z0 r z) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (((z0.im - r) ^ m)⁻¹) * ∫⁻ z : ℂ, ENNReal.ofReal (Wfun m f g z0 r z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul' le_rfl ?_
        rw [lintegral_Wfun_eq hf g z0 r, lintegral_L2dens hR hf]
        exact lintegral_Ft_le hR hf hmod g hinj hr hrh hz0

end TernaryPeriodPolynomials.Argument.ESFoundations.CuspL2
