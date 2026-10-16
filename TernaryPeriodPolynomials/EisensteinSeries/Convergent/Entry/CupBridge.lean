module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.TriangleGreen

@[expose] public section


/-!
# The cup / triangle bridge

The cup / triangle bridge: for a `C¹` potential `a` and a `C²` function `l` and a bilinear pairing `β`,
the integral of `β(da, dl)` antisymmetrised over an affine triangle equals the Alexander--Whitney cup
cochain of the `0`-cochains `a, l` plus the coboundary of the edge cochain `B(x,y) = ∫_{[x,y]} β(a - a x, dl)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

section CupBridge

variable {E A B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup A]
  [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace B] [CompleteSpace F]

/-- The one-form `η = β(a, dl)`. -/
def cupForm (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (x : E) : E →L[ℝ] F :=
  (β (a x)).comp (fderiv ℝ l x)

omit [CompleteSpace B] [CompleteSpace F] in
theorem contDiffOn_cupForm (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hl : ContDiffOn ℝ 2 l U) : ContDiffOn ℝ 1 (cupForm β a l) U := by
  have h1 : ContDiffOn ℝ 1 (fun x => β (a x)) U := β.contDiff.comp_contDiffOn ha
  have h2 : ContDiffOn ℝ 1 (fun x => fderiv ℝ l x) U := hl.fderiv_of_isOpen hU (by norm_num)
  exact h1.clm_comp h2

omit [CompleteSpace B] [CompleteSpace F] in
theorem fderiv_cupForm (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hl : ContDiffOn ℝ 2 l U) {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (cupForm β a l) x u v =
      β (fderiv ℝ a x u) (fderiv ℝ l x v) + β (a x) (fderiv ℝ (fderiv ℝ l) x u v) := by
  have hax : HasFDerivAt a (fderiv ℝ a x) x :=
    ((ha.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hc : DifferentiableAt ℝ (fun y => β (a y)) x := (β.hasFDerivAt.comp x hax).differentiableAt
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ l y) x :=
    ((hl.fderiv_of_isOpen hU (by norm_num)).differentiableOn one_ne_zero).differentiableAt
      (hU.mem_nhds hx)
  have hcf : fderiv ℝ (fun y => β (a y)) x = β.comp (fderiv ℝ a x) :=
    (β.hasFDerivAt.comp x hax).fderiv
  unfold cupForm
  rw [fderiv_clm_comp hc hd]
  simp [hcf, add_comm]

omit [CompleteSpace B] [CompleteSpace F] in
theorem fderiv_cupForm_antisymm (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E)
    (hU : IsOpen U) (ha : ContDiffOn ℝ 1 a U) (hl : ContDiffOn ℝ 2 l U) {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (cupForm β a l) x u v - fderiv ℝ (cupForm β a l) x v u =
      β (fderiv ℝ a x u) (fderiv ℝ l x v) - β (fderiv ℝ a x v) (fderiv ℝ l x u) := by
  rw [fderiv_cupForm β a l U hU ha hl hx, fderiv_cupForm β a l U hU ha hl hx]
  have hsymm : IsSymmSndFDerivAt ℝ l x :=
    (hl.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by simp)
  rw [hsymm u v]
  abel

/-- The line integral `B(x,y) = ∫_{[x,y]} β(a - a(x), dl)`. -/
def cupEdge (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (x y : E) : F :=
  ∫ t in (0 : ℝ)..1, β (a (x + t • (y - x)) - a x) (fderiv ℝ l (x + t • (y - x)) (y - x))

theorem segmentIntegral_cupForm (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E)
    (hU : IsOpen U) (ha : ContDiffOn ℝ 1 a U) (hl : ContDiffOn ℝ 2 l U) (x y : E)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U) :
    segmentIntegral (cupForm β a l) x y = cupEdge β a l x y + β (a x) (l y - l x) := by
  have hγ : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
  have hcl1 : ContDiffOn ℝ 1 l U := hl.of_le (by norm_num)
  have hdl : ContDiffOn ℝ 1 (fun z => fderiv ℝ l z) U := hl.fderiv_of_isOpen hU (by norm_num)
  have hca : ContinuousOn (fun t : ℝ => a (x + t • (y - x))) (Icc 0 1) :=
    ha.continuousOn.comp hγ.continuousOn hseg
  have hcd : ContinuousOn (fun t : ℝ => fderiv ℝ l (x + t • (y - x)) (y - x)) (Icc 0 1) :=
    ((hdl.continuousOn.comp hγ.continuousOn hseg).clm_apply continuousOn_const)
  have hI1 : IntervalIntegrable (fun t : ℝ => β (a (x + t • (y - x)) - a x)
      (fderiv ℝ l (x + t • (y - x)) (y - x))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact (β.continuous.comp_continuousOn (hca.sub continuousOn_const)).clm_apply hcd
  have hI2 : IntervalIntegrable (fun t : ℝ => β (a x) (fderiv ℝ l (x + t • (y - x)) (y - x)))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact (β (a x)).continuous.comp_continuousOn hcd
  have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ l (x + t • (y - x)) (y - x) = l y - l x := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => l (x + t • (y - x)))
        (fderiv ℝ l (x + t • (y - x)) (y - x)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hxt : x + t • (y - x) ∈ U := hseg t ht
      have h1 : HasFDerivAt l (fderiv ℝ l (x + t • (y - x))) (x + t • (y - x)) :=
        ((hcl1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hxt)).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
        simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
      exact h1.comp_hasDerivAt t h2
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le zero_le_one]
        exact hcd)
    simpa using this
  have hsplit : ∀ t : ℝ, β (a (x + t • (y - x))) (fderiv ℝ l (x + t • (y - x)) (y - x)) =
      β (a (x + t • (y - x)) - a x) (fderiv ℝ l (x + t • (y - x)) (y - x)) +
        β (a x) (fderiv ℝ l (x + t • (y - x)) (y - x)) := by
    intro t
    rw [← add_apply, ← map_add, sub_add_cancel]
  have hcdI : IntervalIntegrable (fun t : ℝ => fderiv ℝ l (x + t • (y - x)) (y - x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hcd
  show (∫ t in (0 : ℝ)..1, β (a (x + t • (y - x))) (fderiv ℝ l (x + t • (y - x)) (y - x))) = _
  unfold cupEdge
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add hI1 hI2,
    ((β (a x)).intervalIntegral_comp_comm hcdI), hftc]

/-- **The cup / triangle bridge.** For a `C¹` function `a` and a `C²` function `l` on an open set `U` containing the
affine triangle `[y₀, y₁, y₂]`, and a bilinear pairing `β`:
`∫_Δ (β(da, dl) - β(da, dl)^T) = β(a(y₁) - a(y₀), l(y₂) - l(y₁)) + B(y₁,y₂) - B(y₀,y₂) + B(y₀,y₁)`
(the Alexander--Whitney cup cochain of the 0-cochains `a, l` plus the coboundary of the 1-cochain `B`). -/
theorem cup_bridge (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hl : ContDiffOn ℝ 2 l U) (y₀ y₁ y₂ : E)
    (hT : ∀ p ∈ stdTriangle, affTri y₀ y₁ y₂ p ∈ U) :
    ∫ p in stdTriangle,
        (β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₁ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₂ - y₀)) -
          β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₂ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₁ - y₀))) =
      β (a y₁ - a y₀) (l y₂ - l y₁) + cupEdge β a l y₁ y₂ - cupEdge β a l y₀ y₂ +
        cupEdge β a l y₀ y₁ := by
  have hη := contDiffOn_cupForm β a l U hU ha hl
  have hst := stokes_affine_triangle (cupForm β a l) U hU hη y₀ y₁ y₂ hT
  have hint : ∫ p in stdTriangle,
        (β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₁ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₂ - y₀)) -
          β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₂ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₁ - y₀))) =
      ∫ p in stdTriangle, (fderiv ℝ (cupForm β a l) (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₁ - y₀) (y₂ - y₀) -
          fderiv ℝ (cupForm β a l) (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₂ - y₀) (y₁ - y₀)) := by
    refine setIntegral_congr_fun measurableSet_stdTriangle (fun p hp => ?_)
    have hpU : affTri y₀ y₁ y₂ p ∈ U := hT p hp
    exact (fderiv_cupForm_antisymm β a l U hU ha hl hpU _ _).symm
  rw [hint, hst]
  have e12 : ∀ t ∈ Icc (0 : ℝ) 1, y₁ + t • (y₂ - y₁) ∈ U := by
    intro t ht
    have := hT (1 - t, t) ⟨by linarith [ht.2], ht.1, by linarith⟩
    convert this using 1
    simp only [affTri]
    module
  have e02 : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • (y₂ - y₀) ∈ U := by
    intro t ht
    have := hT (0, t) ⟨le_refl _, ht.1, by linarith [ht.2]⟩
    convert this using 1
    simp [affTri]
  have e01 : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • (y₁ - y₀) ∈ U := by
    intro t ht
    have := hT (t, 0) ⟨ht.1, le_refl _, by linarith [ht.2]⟩
    convert this using 1
    simp [affTri]
  rw [segmentIntegral_cupForm β a l U hU ha hl y₁ y₂ e12, segmentIntegral_cupForm β a l U hU ha hl y₀ y₂ e02,
    segmentIntegral_cupForm β a l U hU ha hl y₀ y₁ e01]
  simp only [map_sub, sub_apply]
  abel

end CupBridge

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
