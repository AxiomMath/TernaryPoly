module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Pair

@[expose] public section


/-!
# The zero order term and the scalar form of the co-closed equation

For a smooth field `H` of invertible symmetric operators, testing the co-closed equation against
`ψ • G e`, with `G = H⁻¹`, turns it into `∂₀ a + ∂₁ b - (∂₀ G) H a - (∂₁ G) H b = 0` in the weak
sense (`coclosed_vec`).  Since `∂ⱼ G = - G (∂ⱼ H) G`, we have `- (∂ⱼ G) H = G (∂ⱼ H)`, so the
distributional divergence `∂₀ a + ∂₁ b` carries the term `G (∂₀ H) a + G (∂₁ H) b`, and the equation
is `G · div (H (a, b)) = 0`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Sys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- First component of `XP E`. -/
def fstX : XP E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E) ∘L (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

/-- Second component of `XP E`. -/
def sndX : XP E →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ E E) ∘L (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

/-- The embedding `b ↦ (0, b)`. -/
def inrX : E →L[ℝ] XP E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.inr ℝ E E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem fstX_apply (x : XP E) : fstX x = x.fst := rfl
omit [FiniteDimensional ℝ E] in
@[simp] theorem sndX_apply (x : XP E) : sndX x = x.snd := rfl
omit [FiniteDimensional ℝ E] in
@[simp] theorem inrX_apply (b : E) : inrX b = mkX 0 b := rfl

/-- The derivative `∂ⱼ G` of the inverse field `G = H⁻¹` in the `j`-th direction; it equals
`- G (∂ⱼ H) G`. -/
def Gd (Hm : ℂ → E →L[ℝ] E) (j : Fin 2) (z : ℂ) : E →L[ℝ] E := fderiv ℝ (invField Hm) z (dir j)

/-- The zero order term of the first order system for `(a, b)`: with `P₀ (a, b) = (b, a)`,
`P₁ (a, b) = (-a, b)` the closed and co-closed equations read `P · ∂(a, b) + Qsys (a, b) = 0`,
i.e. `∂₀ b - ∂₁ a = 0` and `∂₀ a + ∂₁ b - ((∂₀ G) H a + (∂₁ G) H b) = 0` with `G = H⁻¹`, where
`- (∂ⱼ G) H = G ∂ⱼ H`. -/
def Qsys (Hm : ℂ → E →L[ℝ] E) (z : ℂ) : XP E →L[ℝ] XP E :=
  inrX ∘L (-((Gd Hm 0 z ∘L Hm z) ∘L fstX) - ((Gd Hm 1 z ∘L Hm z) ∘L sndX))

omit [FiniteDimensional ℝ E] in
theorem Qsys_apply (Hm : ℂ → E →L[ℝ] E) (z : ℂ) (x : XP E) :
    Qsys Hm z x = mkX 0 (-(Gd Hm 0 z (Hm z x.fst)) - Gd Hm 1 z (Hm z x.snd)) := rfl

omit [FiniteDimensional ℝ E] in
theorem locInt_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (T : E →L[ℝ] E')
    {u : ℂ → E} {V : Set ℂ} (hV : IsOpen V) (hu : LocallyIntegrableOn u V volume) :
    LocallyIntegrableOn (fun z => T (u z)) V volume := by
  rw [locallyIntegrableOn_iff hV.isLocallyClosed] at hu ⊢
  exact fun K hKV hK => T.integrable_comp (hu K hKV hK)

/-- A smooth cutoff times a smooth field of operators applied to a locally integrable function is
integrable. -/
theorem integrable_cutoff_clm {M : ℂ → E →L[ℝ] E} {V : Set ℂ} (hV : IsOpen V)
    (hM : ContDiffOn ℝ ∞ M V) {u : ℂ → E} (hu : LocallyIntegrableOn u V volume) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ V) :
    Integrable fun z => ψ z • M z (u z) := by
  obtain ⟨n, T, q, hq, hQe⟩ := exists_expansion hM
  have hsum : (fun z => ψ z • M z (u z)) = fun z => ∑ s, (ψ z * q s z) • T s (u z) := by
    funext z
    rw [hQe z (u z), Finset.smul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [smul_smul]
  rw [hsum]
  refine integrable_finsetSum _ fun s _ => ?_
  have hcd : ContDiff ℝ ∞ (fun z => ψ z * q s z) :=
    contDiff_of_tsupport_subset' hV (hψ.contDiffOn.mul (hq s))
      ((tsupport_mul_subset_left).trans hs)
  exact integrable_cutoff_smul (locInt_clm (T s) hV hu) hcd.continuous
    (hc.mul_right) ((tsupport_mul_subset_left).trans hs)

omit [FiniteDimensional ℝ E] in
theorem contDiff_of_tsupport_subset_E {V : Set ℂ} (hV : IsOpen V) {f : ℂ → E}
    (hf : ContDiffOn ℝ ∞ f V) (hs : tsupport f ⊆ V) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact (hf x hx).contDiffAt (hV.mem_nhds hx)
  · exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hs ht)))

variable {U : Set ℂ} {Hm : ℂ → E →L[ℝ] E} (hH : HField U Hm)
include hH

theorem smooth_Gd (j : Fin 2) : ContDiffOn ℝ ∞ (Gd Hm j) U :=
  (hH.smooth_inv.fderiv_of_isOpen hH.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem smooth_Qsys : ContDiffOn ℝ ∞ (Qsys Hm) U := by
  have h0 := (smooth_Gd hH 0).clm_comp hH.smooth
  have h1 := (smooth_Gd hH 1).clm_comp hH.smooth
  exact contDiffOn_const.clm_comp
    (((h0.clm_comp contDiffOn_const).neg).sub (h1.clm_comp contDiffOn_const))

/-- The test field `ψ • G e` used to put the co-closed equation into scalar form. -/
theorem fderiv_testField {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (e : E) (j : Fin 2) {z : ℂ}
    (hz : z ∈ U) :
    fderiv ℝ (fun z => ψ z • invField Hm z e) z (dir j) =
      ψ z • Gd Hm j z e + fderiv ℝ ψ z (dir j) • invField Hm z e := by
  have hGd : DifferentiableAt ℝ (invField Hm) z :=
    ((hH.smooth_inv z hz).contDiffAt (hH.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hGe : DifferentiableAt ℝ (fun z => invField Hm z e) z := hGd.clm_apply (differentiableAt_const e)
  have e1 : fderiv ℝ (fun z => invField Hm z e) z (dir j) = Gd Hm j z e := by
    rw [fderiv_clm_apply hGd (differentiableAt_const e)]
    simp [Gd]
  rw [fderiv_fun_smul (hψ.differentiable (by simp) z) hGe]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, e1]

theorem coclosed_vec {a b : ℂ → E} (ha : LocallyIntegrableOn a U volume)
    (hb : LocallyIntegrableOn b U volume)
    (hco : ∀ φ : ℂ → E, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, (⟪fderiv ℝ φ z (dir 0), Hm z (a z)⟫_ℝ + ⟪fderiv ℝ φ z (dir 1), Hm z (b z)⟫_ℝ) = 0)
    {ψ : ℂ → ℝ} (hψ : IsTest ψ) (hψU : tsupport ψ ⊆ U) :
    (∫ z, fderiv ℝ ψ z (dir 0) • a z) + (∫ z, fderiv ℝ ψ z (dir 1) • b z) +
      ∫ z, ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))) = 0 := by
  have hdψ : ∀ j, Integrable fun z => fderiv ℝ ψ z (dir j) • (if j = 0 then a z else b z) := by
    intro j
    have hloc : LocallyIntegrableOn (if j = 0 then a else b) U volume := by
      split_ifs <;> assumption
    have := integrable_cutoff_smul hloc (hψ.fderiv_apply (dir j)) (hψ.fderiv_compact (dir j))
      ((tsupport_fderiv_apply_subset (dir j)).trans hψU)
    refine this.congr (Eventually.of_forall fun z => ?_)
    split_ifs <;> rfl
  have hM : ∀ j, ContDiffOn ℝ ∞ (fun z => Gd Hm j z ∘L Hm z) U := fun j =>
    (smooth_Gd hH j).clm_comp hH.smooth
  have i0 := integrable_cutoff_clm hH.isOpen (hM 0) ha hψ.1 hψ.2 hψU
  have i1 := integrable_cutoff_clm hH.isOpen (hM 1) hb hψ.1 hψ.2 hψU
  have hint : Integrable fun z => (fderiv ℝ ψ z (dir 0) • a z + fderiv ℝ ψ z (dir 1) • b z +
      ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z)))) := by
    have e : (fun z => (fderiv ℝ ψ z (dir 0) • a z + fderiv ℝ ψ z (dir 1) • b z +
        ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))))) = fun z =>
        (fderiv ℝ ψ z (dir 0) • a z + fderiv ℝ ψ z (dir 1) • b z) +
          (ψ z • (Gd Hm 0 z ∘L Hm z) (a z) + ψ z • (Gd Hm 1 z ∘L Hm z) (b z)) := by
      funext z
      simp [smul_add, add_assoc]
    rw [e]
    exact ((hdψ 0).add (hdψ 1)).add (i0.add i1)
  have hsplit : (∫ z, fderiv ℝ ψ z (dir 0) • a z) + (∫ z, fderiv ℝ ψ z (dir 1) • b z) +
      ∫ z, ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))) =
      ∫ z, (fderiv ℝ ψ z (dir 0) • a z + fderiv ℝ ψ z (dir 1) • b z +
        ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z)))) := by
    have d0 : Integrable fun z => fderiv ℝ ψ z (dir 0) • a z := by simpa using hdψ 0
    have d1 : Integrable fun z => fderiv ℝ ψ z (dir 1) • b z := by simpa using hdψ 1
    have i2 : Integrable fun z => ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z))) := by
      refine (i0.add i1).congr (Eventually.of_forall fun z => ?_)
      simp [smul_add]
    rw [integral_add (f := fun z => fderiv ℝ ψ z (dir 0) • a z + fderiv ℝ ψ z (dir 1) • b z)
      (g := fun z => ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z)))) (d0.add d1) i2,
      integral_add d0 d1]
  rw [hsplit]
  refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hint fun e => ?_
  have hφd : ContDiff ℝ ∞ fun z => ψ z • invField Hm z e :=
    contDiff_of_tsupport_subset_E hH.isOpen
      (hψ.1.contDiffOn.smul (hH.smooth_inv.clm_apply contDiffOn_const))
      (tsupport_smul_subset_left _ _ |>.trans hψU)
  have hφc : HasCompactSupport fun z => ψ z • invField Hm z e :=
    hψ.2.mono' fun z hz => subset_tsupport ψ fun h0 => hz (by simp [h0])
  have hφU : tsupport (fun z => ψ z • invField Hm z e) ⊆ U :=
    (tsupport_smul_subset_left _ _).trans hψU
  have key : ∀ z, ⟪e, fderiv ℝ ψ z (dir 0) • a z + fderiv ℝ ψ z (dir 1) • b z +
      ψ z • (Gd Hm 0 z (Hm z (a z)) + Gd Hm 1 z (Hm z (b z)))⟫_ℝ =
      ⟪fderiv ℝ (fun z => ψ z • invField Hm z e) z (dir 0), Hm z (a z)⟫_ℝ +
        ⟪fderiv ℝ (fun z => ψ z • invField Hm z e) z (dir 1), Hm z (b z)⟫_ℝ := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · have hzU := hψU hz
      rw [fderiv_testField hH hψ.1 e 0 hzU, fderiv_testField hH hψ.1 e 1 hzU]
      have c1 : ∀ w : E, invField Hm z (Hm z w) = w := fun w => by
        simpa using congrArg (fun T => T w) (hH.inv_mul z hzU)
      have s1 : ∀ w : E, ⟪invField Hm z e, Hm z w⟫_ℝ = ⟪e, w⟫_ℝ := fun w => by
        rw [hH.selfAdj_inv z hzU, c1]
      have s2 : ∀ (j : Fin 2) (w : E), ⟪Gd Hm j z e, Hm z w⟫_ℝ = ⟪e, Gd Hm j z (Hm z w)⟫_ℝ :=
        fun j w => hH.selfAdj_fderiv_inv z hzU (dir j) e (Hm z w)
      simp only [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left, s1, s2,
        RCLike.conj_to_real]
      ring
    · have h1 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have h2 : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ hz
      have h3 : fderiv ℝ (fun z => ψ z • invField Hm z e) z = 0 :=
        fderiv_of_notMem_tsupport ℝ fun h => hz (tsupport_smul_subset_left _ _ h)
      simp [h1, h2, h3]
  simp only [key]
  exact hco _ hφd hφc hφU

end Sys

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
