module

public import Mathlib

@[expose] public section


/-!
# The energy identity of a Hodge pair

Foundation file of the unconditional Eichler--Shimura route.  For a pair `(a_k, b_{k+1})` of component functions satisfying the strong differential
equations `2iy ∂_z̄ a = (m-k) a - (k+1) b`, `2iy ∂_z b = (m-k) a - (k+1) b` (HYPOTHESES here) the
density `y^m ((m-k)|a|² + (k+1)|b|²)` is the `∂_z̄`-divergence `-∂_z̄ (2i y^{m+1} a b̄)`
(`dbar_pairW`), so against a compactly supported `C¹` cutoff `χ` the integral is
`∫ ∂_z̄χ · W` (`pair_energy`).

This file proves only these strong-pair identities (pointwise divergence identity and the
compact-cutoff integration by parts).  It does not derive the pair equations from a harmonic form
(that is `HodgeReduce`, in monomial coordinates, from closed and co-closed forms) and it does not
perform the cutoff exhaustion of the quotient `Γ\ℍ` (that is `HodgeGlobal.middle_pair_vanish`, which
uses the partition of unity and the height cutoffs, and `HodgeDecoupling.decoupling`, which
assembles them); the assembly of an actual harmonic quotient form from the compactly supported
cohomology representative is to be proved (`L2Forms`, `Weyl`, `Assembly`).

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair

/-- The Wirtinger derivative `∂_z̄`. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I)

/-- The Wirtinger derivative `∂_z`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f z 1 - I * fderiv ℝ f z I)

theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = dbar f z * g z + f z * dbar g z := by
  unfold dbar
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem dbar_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w => starRingEnd ℂ (f w)) z = starRingEnd ℂ (dz f z) := by
  unfold dbar dz
  have h : fderiv ℝ (fun w => starRingEnd ℂ (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) :=
    (Complex.conjCLE.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  rw [h]
  have e : ∀ x, (Complex.conjCLE : ℂ →L[ℝ] ℂ) x = starRingEnd ℂ x := fun x => rfl
  simp only [ContinuousLinearMap.comp_apply, e, map_mul, map_sub,
    map_div₀, map_one, map_ofNat, Complex.conj_I]
  ring

/-- The height function. -/
def ht (z : ℂ) : ℂ := (z.im : ℂ)

theorem differentiable_ht : Differentiable ℝ ht := by
  unfold ht
  exact Complex.ofRealCLM.differentiable.comp Complex.imCLM.differentiable

theorem dbar_ht (z : ℂ) : dbar ht z = I / 2 := by
  unfold dbar ht
  have h : fderiv ℝ (fun w : ℂ => (w.im : ℂ)) z =
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp Complex.imCLM :=
    (Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt).fderiv
  rw [h]
  simp
  ring

theorem dbar_pow_ht (p : ℕ) (z : ℂ) :
    dbar (fun w => ht w ^ p) z = (p : ℂ) * ht z ^ (p - 1) * (I / 2) := by
  have h0 : HasFDerivAt ht ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp Complex.imCLM) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hd := h0.pow p
  unfold dbar
  rw [hd.fderiv]
  simp [ht]
  ring

/-- The boundary vector field of the pair identity. -/
def pairW (m : ℕ) (a b : ℂ → ℂ) (w : ℂ) : ℂ :=
  2 * I * ht w ^ (m + 1) * (a w * starRingEnd ℂ (b w))

/-- **The pair identity**: the density is a `∂_z̄`-divergence. -/
theorem dbar_pairW (m k : ℕ) {a b : ℂ → ℂ} {z : ℂ} (hy : 0 < z.im)
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z)
    (h1 : 2 * I * ht z * dbar a z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z)
    (h2 : 2 * I * ht z * dz b z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z) :
    dbar (pairW m a b) z =
      -(ht z ^ m * (((m : ℂ) - k) * (a z * starRingEnd ℂ (a z)) +
        ((k : ℂ) + 1) * (b z * starRingEnd ℂ (b z)))) := by
  have hyc : ht z ≠ 0 := by
    unfold ht; exact_mod_cast hy.ne'
  have hconj : starRingEnd ℂ (ht z) = ht z := by simp [ht]
  have hbd : DifferentiableAt ℝ (fun w => starRingEnd ℂ (b w)) z :=
    (Complex.conjCLE.differentiableAt).comp z hb
  have hpd : DifferentiableAt ℝ (fun w => ht w ^ (m + 1)) z :=
    (differentiable_ht z).pow (m + 1)
  unfold pairW
  have e1 : (fun w => 2 * I * ht w ^ (m + 1) * (a w * starRingEnd ℂ (b w))) =
      fun w => (2 * I * ht w ^ (m + 1)) * (a w * starRingEnd ℂ (b w)) := rfl
  have hc : DifferentiableAt ℝ (fun w => 2 * I * ht w ^ (m + 1)) z := hpd.const_mul _
  have hab : DifferentiableAt ℝ (fun w => a w * starRingEnd ℂ (b w)) z := ha.mul hbd
  rw [e1, dbar_mul hc hab, dbar_mul ha hbd, dbar_conj hb]
  have hc' : dbar (fun w => 2 * I * ht w ^ (m + 1)) z =
      2 * I * dbar (fun w => ht w ^ (m + 1)) z := by
    unfold dbar
    rw [fderiv_const_mul hpd]
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [hc', dbar_pow_ht]
  have hda : dbar a z = (((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z) / (2 * I * ht z) := by
    field_simp
    linear_combination h1
  have hdb : dz b z = (((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z) / (2 * I * ht z) := by
    field_simp
    linear_combination h2
  rw [hda, hdb]
  simp only [map_div₀, map_sub, map_mul, map_add, map_natCast, map_one, map_ofNat, Complex.conj_I,
    hconj]
  field_simp
  simp only [Nat.add_sub_cancel]
  push_cast
  linear_combination ((1 + (m : ℂ)) * ht z * ht z ^ m * a z * starRingEnd ℂ (b z)) * Complex.I_sq

/-- The upper half plane as a subset of `ℂ`. -/
def U : Set ℂ := {z | 0 < z.im}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

theorem integrable_cs {F G : ℂ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFs : tsupport F ⊆ U) (hG : ContinuousOn G U) : Integrable (fun x => F x * G x) := by
  have h1 : IntegrableOn (fun x => F x * G x) (tsupport F) := by
    refine ContinuousOn.integrableOn_compact hFc ?_
    exact (hF.continuousOn).mul (hG.mono hFs)
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport F)]
  · exact h1
  · intro x hx
    exact subset_tsupport _ (fun h => hx (by simp [h]))

/-- **Integration by parts for `∂_z̄`** against a compactly supported `C¹` cutoff. -/
theorem integral_mul_dbar {χ W : ℂ → ℂ} (hχ : ContDiff ℝ 1 χ) (hcs : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) (hW : ContDiffOn ℝ 1 W U) :
    ∫ z, χ z * dbar W z = -∫ z, dbar χ z * W z := by
  have hWd : ∀ x ∈ tsupport χ, DifferentiableAt ℝ W x := fun x hx =>
    (hW.differentiableOn (by norm_num) x (hsupp hx)).differentiableAt
      (isOpen_U.mem_nhds (hsupp hx))
  have hχd : ∀ x, DifferentiableAt ℝ χ x := fun x => hχ.differentiable (by norm_num) x
  have hWc : ContinuousOn W U := hW.continuousOn
  have hdW : ∀ v, ContinuousOn (fun x => fderiv ℝ W x v) U := fun v =>
    ((hW.continuousOn_fderiv_of_isOpen isOpen_U (by norm_num)).clm_apply continuousOn_const)
  have hdχ : ∀ v, Continuous (fun x => fderiv ℝ χ x v) := fun v =>
    ((hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hdχs : ∀ v, tsupport (fun x => fderiv ℝ χ x v) ⊆ U := fun v => by
    refine ((closure_mono ?_).trans (tsupport_fderiv_subset ℝ)).trans hsupp
    intro x hx h
    exact hx (by simp [h])
  have hdχc : ∀ v, HasCompactSupport (fun x => fderiv ℝ χ x v) := fun v =>
    hcs.fderiv_apply ℝ v
  have key : ∀ v, ∫ z, χ z * fderiv ℝ W z v = -∫ z, fderiv ℝ χ z v * W z := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_cs (hdχ v) (hdχc v) (hdχs v) hWc)
      (integrable_cs hχ.continuous hcs hsupp (hdW v))
      (integrable_cs hχ.continuous hcs hsupp hWc) (fun x _ => hχd x) hWd
  have e1 := key 1
  have e2 := key I
  have i1 := integrable_cs hχ.continuous hcs hsupp (hdW 1)
  have i2 := integrable_cs hχ.continuous hcs hsupp (hdW I)
  have j1 := integrable_cs (hdχ 1) (hdχc 1) (hdχs 1) hWc
  have j2 := integrable_cs (hdχ I) (hdχc I) (hdχs I) hWc
  have L : ∀ z, χ z * dbar W z = (1 / 2 : ℂ) * (χ z * fderiv ℝ W z 1) +
      (I / 2) * (χ z * fderiv ℝ W z I) := fun z => by unfold dbar; ring
  have R : ∀ z, dbar χ z * W z = (1 / 2 : ℂ) * (fderiv ℝ χ z 1 * W z) +
      (I / 2) * (fderiv ℝ χ z I * W z) := fun z => by unfold dbar; ring
  simp_rw [L, R]
  rw [integral_add (i1.const_mul _) (i2.const_mul _),
    integral_add (j1.const_mul _) (j2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, e1, e2]
  ring

theorem contDiffOn_pairW (m : ℕ) {a b : ℂ → ℂ} (ha : ContDiffOn ℝ 1 a U)
    (hb : ContDiffOn ℝ 1 b U) : ContDiffOn ℝ 1 (pairW m a b) U := by
  unfold pairW
  have h1 : ContDiff ℝ 1 (fun w : ℂ => ht w ^ (m + 1)) :=
    (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow (m + 1)
  have h2 : ContDiffOn ℝ 1 (fun w => starRingEnd ℂ (b w)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn hb
  exact ((contDiffOn_const.mul h1.contDiffOn).mul (ha.mul h2))

/-- **The energy identity of a pair**: for a compactly supported `C¹` cutoff `χ`,
`∫ χ y^m ((m-k)|a|² + (k+1)|b|²) = ∫ ∂_z̄χ · W`. -/
theorem pair_energy (m k : ℕ) {a b : ℂ → ℂ} (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U)
    (h1 : ∀ z ∈ U, 2 * I * ht z * dbar a z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z)
    (h2 : ∀ z ∈ U, 2 * I * ht z * dz b z = ((m : ℂ) - k) * a z - ((k : ℂ) + 1) * b z)
    {χ : ℂ → ℂ} (hχ : ContDiff ℝ 1 χ) (hcs : HasCompactSupport χ) (hsupp : tsupport χ ⊆ U) :
    ∫ z, χ z * (ht z ^ m * (((m : ℂ) - k) * (a z * starRingEnd ℂ (a z)) +
        ((k : ℂ) + 1) * (b z * starRingEnd ℂ (b z)))) = ∫ z, dbar χ z * pairW m a b z := by
  have hW := contDiffOn_pairW m ha hb
  have := integral_mul_dbar hχ hcs hsupp hW
  have hz : ∀ z, χ z * dbar (pairW m a b) z =
      -(χ z * (ht z ^ m * (((m : ℂ) - k) * (a z * starRingEnd ℂ (a z)) +
        ((k : ℂ) + 1) * (b z * starRingEnd ℂ (b z))))) := by
    intro z
    by_cases hzU : z ∈ U
    · rw [dbar_pairW m k hzU (((ha.differentiableOn (by norm_num)) z hzU).differentiableAt
        (isOpen_U.mem_nhds hzU)) (((hb.differentiableOn (by norm_num)) z hzU).differentiableAt
        (isOpen_U.mem_nhds hzU)) (h1 z hzU) (h2 z hzU)]
      ring
    · have : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzU (hsupp h))
      simp [this]
  simp_rw [hz] at this
  rw [integral_neg] at this
  exact neg_injective this

end TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair
