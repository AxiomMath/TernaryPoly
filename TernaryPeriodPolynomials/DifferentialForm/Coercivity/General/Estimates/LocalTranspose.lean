module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalMollify
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.ConvolutionTranspose
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionLinear
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Gram
public import TernaryPeriodPolynomials.DifferentialForm.LocalIntegrationByParts

@[expose] public section



/-! # General coercivity, Tier B: linearity and weighted transposition of the local mollifier

`frMol` is linear in its form argument, and its transpose for the metric-density pairing is the
explicit smooth compactly supported operator `frTr` obtained from the weighted transposition of
the cutoff convolution.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.CompactCoordinateIntegration TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

variable {n k : ℕ}

theorem continuous_components_of {g : Coordinates → FormValue n k} (hg : Continuous g)
    (i : Index n k) : Continuous (components n k g i) :=
  (continuous_apply i).comp ((coordinates n k).continuous.comp hg)

theorem hasCompactSupport_components_of {g : Coordinates → FormValue n k}
    (hcg : HasCompactSupport g) (i : Index n k) : HasCompactSupport (components n k g i) :=
  hcg.comp_left (g := fun z : FormValue n k => coordinates n k z i)
    (by simp only [ContinuousLinearEquiv.map_zero, Pi.zero_apply])

theorem zero_smul_fv (f : FormValue n k) : (0 : ℝ) • f = 0 :=
  ContinuousAlternatingMap.ext (fun v => zero_smul ℝ (f v))

theorem one_smul_fv (f : FormValue n k) : (1 : ℝ) • f = f :=
  ContinuousAlternatingMap.ext (fun v => one_smul ℝ (f v))

theorem frConv_add (c : ℝ) {g g' : Coordinates → FormValue n k}
    (hg : Continuous g) (hcg : HasCompactSupport g) (hg' : Continuous g')
    (hcg' : HasCompactSupport g') (x : Coordinates) :
    frConv n k c (fun y => g y + g' y) x = frConv n k c g x + frConv n k c g' x := by
  have hκ : Continuous (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) :=
    (TernaryPoly.CompactScalarMollifier.kernel_contDiff Coordinates volume c).continuous
  have hcomp : ∀ i, components n k (fun y => g y + g' y) i =
      components n k g i + components n k g' i := fun i =>
    funext fun y => congrArg (fun z : Index n k → ℝ => z i)
      (map_add (coordinates n k) (g y) (g' y))
  have hsc : ∀ i, scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
      (components n k (fun y => g y + g' y) i) x =
      scalarConvolution volume (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (components n k g i) x +
      scalarConvolution volume (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (components n k g' i) x := fun i =>
    (congrArg (fun f : Coordinates → ℝ => scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) f x) (hcomp i)).trans
      (congrFun (scalarConvolution_add volume _ _ _ hκ (continuous_components_of hg i)
        (continuous_components_of hg' i) (hasCompactSupport_components_of hcg i)
        (hasCompactSupport_components_of hcg' i)) x)
  have e : (fun i => scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
      (components n k (fun y => g y + g' y) i) x) =
      (fun i => scalarConvolution volume
        (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) (components n k g i) x) +
      (fun i => scalarConvolution volume
        (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) (components n k g' i) x) :=
    funext hsc
  exact (congrArg (coordinates n k).symm e).trans (map_add (coordinates n k).symm _ _)

theorem frConv_smul (c r : ℝ) (g : Coordinates → FormValue n k) (x : Coordinates) :
    frConv n k c (fun y => r • g y) x = r • frConv n k c g x := by
  have hcomp : ∀ i, components n k (fun y => r • g y) i = r • components n k g i := fun i =>
    funext fun y => congrArg (fun z : Index n k → ℝ => z i)
      (map_smul (coordinates n k) r (g y))
  have hsc : ∀ i, scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
      (components n k (fun y => r • g y) i) x =
      r * scalarConvolution volume (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (components n k g i) x := fun i =>
    (congrArg (fun f : Coordinates → ℝ => scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) f x) (hcomp i)).trans
      (congrFun (scalarConvolution_smul volume _ _ r) x)
  have e : (fun i => scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
      (components n k (fun y => r • g y) i) x) =
      r • (fun i => scalarConvolution volume
        (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) (components n k g i) x) :=
    funext hsc
  exact (congrArg (coordinates n k).symm e).trans (map_smul (coordinates n k).symm r _)

theorem frMol_add {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ positiveCoordinates) (c : ℝ) {f f' : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (hf' : ContDiffOn ℝ ∞ f' positiveCoordinates)
    (x : Coordinates) :
    frMol n k χ η c (fun y => f y + f' y) x = frMol n k χ η c f x + frMol n k χ η c f' x := by
  have hcut : (fun y => χ y • (f y + f' y)) = fun y => χ y • f y + χ y • f' y :=
    funext fun y => smul_add (χ y) (f y) (f' y)
  have h1 : frConv n k c (fun y => χ y • (f y + f' y)) x =
      frConv n k c (fun y => χ y • f y) x + frConv n k c (fun y => χ y • f' y) x :=
    (congrArg (fun g : Coordinates → FormValue n k => frConv n k c g x) hcut).trans
      (frConv_add c (contDiff_cut hχ hsχ hf).continuous (hasCompactSupport_cut hcχ f)
        (contDiff_cut hχ hsχ hf').continuous (hasCompactSupport_cut hcχ f') x)
  exact (congrArg (fun z : FormValue n k => η x • z) h1).trans
    (smul_add (η x) (frConv n k c (fun y => χ y • f y) x)
      (frConv n k c (fun y => χ y • f' y) x))

theorem frMol_smul (χ η : Coordinates → ℝ) (c r : ℝ) (f : Coordinates → FormValue n k)
    (x : Coordinates) :
    frMol n k χ η c (fun y => r • f y) x = r • frMol n k χ η c f x := by
  have hcut : (fun y => χ y • (r • f y)) = fun y => r • (χ y • f y) :=
    funext fun y => smul_comm (χ y) r (f y)
  have h1 : frConv n k c (fun y => χ y • (r • f y)) x = r • frConv n k c (fun y => χ y • f y) x :=
    (congrArg (fun g : Coordinates → FormValue n k => frConv n k c g x) hcut).trans
      (frConv_smul c r (fun y => χ y • f y) x)
  exact (congrArg (fun z : FormValue n k => η x • z) h1).trans
    (smul_comm (η x) r (frConv n k c (fun y => χ y • f y) x))

theorem frMol_congr {χ η : Coordinates → ℝ} (hsχ : tsupport χ ⊆ positiveCoordinates) (c : ℝ)
    {f f' : Coordinates → FormValue n k} (h : ∀ x ∈ positiveCoordinates, f x = f' x) :
    frMol n k χ η c f = frMol n k χ η c f' := by
  have hcut : (fun y => χ y • f y) = fun y => χ y • f' y := by
    funext y
    by_cases hy : y ∈ tsupport χ
    · exact congrArg (fun z : FormValue n k => χ y • z) (h y (hsχ hy))
    · have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      exact (congrArg (fun r : ℝ => r • f y) h0).trans
        ((zero_smul_fv (f y)).trans (zero_smul_fv (f' y)).symm |>.trans
          (congrArg (fun r : ℝ => r • f' y) h0.symm))
  funext x
  exact congrArg (fun g : Coordinates → FormValue n k => η x • frConv n k c g x) hcut

/-! ### The weighted transpose -/

variable (n k) in
/-- The metric dual of the form, multiplied by the outer cutoff. -/
def frDual (η : Coordinates → ℝ) (h : Coordinates → FormValue n k) (i : Index n k)
    (x : Coordinates) : ℝ :=
  η x * metricDual (weightedGram n k) (components n k h) i x

variable (n k) in
/-- Components of the weighted transpose of the cutoff mollifier. -/
def frTrComp (χ η : Coordinates → ℝ) (c : ℝ) (h : Coordinates → FormValue n k) :
    Index n k → Coordinates → ℝ :=
  weightedCutoffTranspose volume (weightedGram n k)
    (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) χ η (components n k h)

variable (n k) in
/-- The weighted transpose of the cutoff mollifier, as a form-valued function. -/
def frTr (χ η : Coordinates → ℝ) (c : ℝ) (h : Coordinates → FormValue n k) (x : Coordinates) :
    FormValue n k :=
  (coordinates n k).symm (fun i => frTrComp n k χ η c h i x)

theorem contDiff_frDual {η : Coordinates → ℝ} (hη : ContDiff ℝ ∞ η)
    (hsη : tsupport η ⊆ positiveCoordinates) {h : Coordinates → FormValue n k}
    (hh : ContDiffOn ℝ ∞ h positiveCoordinates) (i : Index n k) :
    ContDiff ℝ ∞ (frDual n k η h i) := by
  apply contDiff_of_tsupport_subset isOpen_positiveCoordinates _
    (tsupport_mul_subset_left.trans hsη)
  apply hη.contDiffOn.mul
  apply contDiffOn_metricDual
  · intro j l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n k) j) l
  · intro j
    exact contDiffOn_components n k hh j

theorem contDiff_frTrComp {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ positiveCoordinates) (hη : ContDiff ℝ ∞ η)
    (hsη : tsupport η ⊆ positiveCoordinates) {c : ℝ} (hc : c ≠ 0)
    {h : Coordinates → FormValue n k} (hh : ContDiffOn ℝ ∞ h positiveCoordinates)
    (i : Index n k) : ContDiff ℝ ∞ (frTrComp n k χ η c h i) := by
  apply contDiff_of_tsupport_subset isOpen_positiveCoordinates _
    (tsupport_mul_subset_left.trans hsχ)
  apply hχ.contDiffOn.mul
  apply contDiffOn_metricDual
  · intro j l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram_inverse n k) j) l
  · intro j
    exact (contDiff_scalarConvolution volume _ (frDual n k η h j)
      ((TernaryPoly.CompactScalarMollifier.kernel_contDiff Coordinates volume c).comp contDiff_neg)
      ((TernaryPoly.CompactScalarMollifier.kernel_compact Coordinates volume c hc).comp_homeomorph
        (Homeomorph.neg Coordinates))
      (contDiff_frDual hη hsη hh j).continuous).contDiffOn

theorem components_frTr (χ η : Coordinates → ℝ) (c : ℝ) (h : Coordinates → FormValue n k) :
    components n k (frTr n k χ η c h) = frTrComp n k χ η c h := by
  funext i x
  exact congrFun ((coordinates n k).apply_symm_apply
    (fun j => frTrComp n k χ η c h j x)) i

theorem contDiff_frTr {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ positiveCoordinates) (hη : ContDiff ℝ ∞ η)
    (hsη : tsupport η ⊆ positiveCoordinates) {c : ℝ} (hc : c ≠ 0)
    {h : Coordinates → FormValue n k} (hh : ContDiffOn ℝ ∞ h positiveCoordinates) :
    ContDiff ℝ ∞ (frTr n k χ η c h) := by
  change ContDiff ℝ ∞ ((coordinates n k).symm ∘ _)
  apply ContDiff.comp (𝕜 := ℝ) (E := Coordinates) (F := Index n k → ℝ) (G := FormValue n k)
    (ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := Index n k → ℝ) (F := FormValue n k)
      (coordinates n k).symm)
  exact contDiff_pi.mpr (fun i => contDiff_frTrComp hχ hsχ hη hsη hc hh i)

theorem tsupport_frTr_subset (χ η : Coordinates → ℝ) (c : ℝ) (h : Coordinates → FormValue n k) :
    tsupport (frTr n k χ η c h) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  apply hx
  have hv : (fun i => frTrComp n k χ η c h i x) = 0 := by
    funext i
    exact image_eq_zero_of_notMem_tsupport
      (fun hi => hn (tsupport_mul_subset_left hi))
  change (coordinates n k).symm _ = 0
  rw [hv, map_zero]

theorem hasCompactSupport_frTr {χ η : Coordinates → ℝ} (hcχ : HasCompactSupport χ) (c : ℝ)
    (h : Coordinates → FormValue n k) : HasCompactSupport (frTr n k χ η c h) :=
  hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_frTr_subset χ η c h)

/-- The transpose identity for the metric-density pairing. -/
theorem integral_frMol_transpose {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ positiveCoordinates)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ positiveCoordinates)
    {c : ℝ} (hc : c ≠ 0) {f h : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (hh : ContDiffOn ℝ ∞ h positiveCoordinates) :
    ∫ x, coordinateDensity x * formPairing n k x (frMol n k χ η c f x) (h x) =
      ∫ x, coordinateDensity x * formPairing n k x (f x) (frTr n k χ η c h x) := by
  have key := integral_weightedCutoffTranspose volume (weightedGram n k)
    (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) χ η
    (fun x hx => isUnit_iff_ne_zero.mpr (ne_of_gt (weightedGram_posDef n k x
      (hsχ hx)).det_pos))
    ((TernaryPoly.CompactScalarMollifier.kernel_contDiff Coordinates volume c).of_le (by simp))
    (TernaryPoly.CompactScalarMollifier.kernel_compact Coordinates volume c hc)
    (components n k f) (components n k h)
    (fun i => (contDiff_components_cut hχ hsχ hf i).continuous)
    (fun i => hcχ.mul_right)
    (fun i => (contDiff_frDual hη hsη hh i).continuous)
    (fun i => hcη.mul_right)
  have e1 : components n k (frMol n k χ η c f) = cutoffConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) χ η (components n k f) :=
    funext fun i => funext fun x => components_frMol χ η c f i x
  have e2 : components n k (frTr n k χ η c h) = weightedCutoffTranspose volume (weightedGram n k)
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) χ η (components n k h) :=
    components_frTr χ η c h
  have l1 : ∀ x, coordinateDensity x * formPairing n k x (frMol n k χ η c f x) (h x) =
      weightedPairing (weightedGram n k) (cutoffConvolution volume
        (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) χ η (components n k f))
        (components n k h) x := fun x =>
    ((weightedPairing_components n k (frMol n k χ η c f) h x).symm).trans
      (congrArg (fun F => weightedPairing (weightedGram n k) F (components n k h) x) e1)
  have l2 : ∀ x, coordinateDensity x * formPairing n k x (f x) (frTr n k χ η c h x) =
      weightedPairing (weightedGram n k) (components n k f)
        (weightedCutoffTranspose volume (weightedGram n k)
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) χ η (components n k h)) x :=
    fun x => ((weightedPairing_components n k f (frTr n k χ η c h) x).symm).trans
      (congrArg (fun G => weightedPairing (weightedGram n k) (components n k f) G x) e2)
  exact (integral_congr_ae (Eventually.of_forall l1)).trans
    (key.trans (integral_congr_ae (Eventually.of_forall l2)).symm)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
