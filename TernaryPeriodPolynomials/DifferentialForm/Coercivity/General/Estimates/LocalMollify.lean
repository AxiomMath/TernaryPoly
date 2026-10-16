module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Unfold
public import TernaryPeriodPolynomials.Analysis.Compact.FiniteMollifier
public import TernaryPeriodPolynomials.Analysis.Compact.FiniteMollifierApproximation
public import TernaryPeriodPolynomials.DifferentialForm.WeightedCoordinateUpper
public import TernaryPeriodPolynomials.DifferentialForm.WeightedConvergence
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.Integral
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.IntegralUpper
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.ConvolutionTranspose
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Gram

@[expose] public section



/-! # General coercivity, Tier B: the local mollifier on the positive coordinates

A `Γ`-free layer on `Ω = positiveCoordinates ⊂ ℝ⁵`: componentwise convolution of a form-valued
function with the scaled mollifier, cut off on both sides, together with its smoothness, support
and `L²` bounds in the plain coordinate norm and in the metric-density norm.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.CompactCoordinateIntegration
open scoped ContDiff

variable (n k : ℕ)

/-- Componentwise convolution of a form-valued function with the scale-`c` mollifier. -/
def frConv (c : ℝ) (g : Coordinates → FormValue n k) (x : Coordinates) : FormValue n k :=
  (coordinates n k).symm (fun i => scalarConvolution volume
    (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) (components n k g i) x)

/-- Cut off, mollified, cut off: `η (κ_c ∗ (χ f))`. -/
def frMol (χ η : Coordinates → ℝ) (c : ℝ) (f : Coordinates → FormValue n k) (x : Coordinates) :
    FormValue n k :=
  η x • frConv n k c (fun y => χ y • f y) x

variable {n k}

theorem components_smul_fun (χ : Coordinates → ℝ) (f : Coordinates → FormValue n k) (i : Index n k)
    (x : Coordinates) : components n k (fun y => χ y • f y) i x = χ x * components n k f i x := by
  change (coordinates n k (χ x • f x)) i = _
  rw [map_smul]
  rfl

theorem components_frMol (χ η : Coordinates → ℝ) (c : ℝ) (f : Coordinates → FormValue n k)
    (i : Index n k) (x : Coordinates) :
    components n k (frMol n k χ η c f) i x = η x * scalarConvolution volume
      (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
      (fun y => χ y * components n k f i y) x := by
  change (coordinates n k (η x • (coordinates n k).symm _)) i = _
  rw [map_smul, (coordinates n k).apply_symm_apply]
  have : components n k (fun y => χ y • f y) i = fun y => χ y * components n k f i y :=
    funext (components_smul_fun χ f i)
  simp only [Pi.smul_apply, smul_eq_mul, this]

theorem contDiff_components_of {g : Coordinates → FormValue n k} (hg : ContDiff ℝ ∞ g)
    (i : Index n k) : ContDiff ℝ ∞ (components n k g i) := by
  have hcoord : ContDiff ℝ ∞ (coordinates n k) :=
    ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := FormValue n k) (F := Index n k → ℝ) (coordinates n k)
  have h : ContDiff ℝ ∞ (fun x => coordinates n k (g x)) :=
    ContDiff.comp (𝕜 := ℝ) (E := Coordinates) (F := FormValue n k)
      (G := Index n k → ℝ) hcoord hg
  exact contDiff_pi.mp h i

theorem contDiff_cut {χ : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ positiveCoordinates) {f : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) : ContDiff ℝ ∞ (fun y => χ y • f y) := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  exact contDiff_of_tsupport_subset isOpen_positiveCoordinates (hχ.contDiffOn.smul hf)
    ((tsupport_smul_subset_left χ f).trans hsχ)

theorem tsupport_cut_subset (χ : Coordinates → ℝ) (f : Coordinates → FormValue n k) :
    tsupport (fun y => χ y • f y) ⊆ tsupport χ :=
  tsupport_smul_subset_left χ f

theorem hasCompactSupport_cut {χ : Coordinates → ℝ} (hcχ : HasCompactSupport χ)
    (f : Coordinates → FormValue n k) : HasCompactSupport (fun y => χ y • f y) :=
  hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_cut_subset χ f)

theorem contDiff_frConv {c : ℝ} (hc : c ≠ 0) {g : Coordinates → FormValue n k}
    (hg : Continuous g) : ContDiff ℝ ∞ (frConv n k c g) := by
  change ContDiff ℝ ∞ ((coordinates n k).symm ∘ _)
  apply ContDiff.comp (𝕜 := ℝ) (E := Coordinates) (F := Index n k → ℝ) (G := FormValue n k)
    (ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := Index n k → ℝ) (F := FormValue n k)
      (coordinates n k).symm)
  apply contDiff_pi.mpr
  intro i
  exact contDiff_scalarConvolution volume _ _
    (TernaryPoly.CompactScalarMollifier.kernel_contDiff Coordinates volume c)
    (TernaryPoly.CompactScalarMollifier.kernel_compact Coordinates volume c hc)
    ((continuous_apply i).comp ((coordinates n k).continuous.comp hg))

theorem contDiff_frMol {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ positiveCoordinates) (hη : ContDiff ℝ ∞ η) {c : ℝ} (hc : c ≠ 0)
    {f : Coordinates → FormValue n k} (hf : ContDiffOn ℝ ∞ f positiveCoordinates) :
    ContDiff ℝ ∞ (frMol n k χ η c f) := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  exact ContDiff.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k) hη
    (contDiff_frConv hc (contDiff_cut hχ hsχ hf).continuous)

theorem tsupport_frMol_subset (χ η : Coordinates → ℝ) (c : ℝ) (f : Coordinates → FormValue n k) :
    tsupport (frMol n k χ η c f) ⊆ tsupport η :=
  tsupport_smul_subset_left η (frConv n k c (fun y => χ y • f y))

theorem hasCompactSupport_frMol {χ η : Coordinates → ℝ} (hcη : HasCompactSupport η) (c : ℝ)
    (f : Coordinates → FormValue n k) : HasCompactSupport (frMol n k χ η c f) :=
  hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_frMol_subset χ η c f)

/-- The plain coordinate `L²` mass of a form-valued function. -/
def compL2 (g : Coordinates → FormValue n k) : ℝ := ∑ i, ∫ x, ‖components n k g i x‖ ^ 2

theorem compL2_le_integral {g : Coordinates → FormValue n k} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    compL2 g ≤ ((Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2) *
      ∫ x, ‖g x‖ ^ 2 := by
  have h := TernaryPoly.FiniteCoordinateSquare.compact_integral_coordinates_le_square
    (E := Coordinates) (F := FormValue n k) (I := Index n k) volume (coordinates n k) g hg hc
  exact h

theorem integral_le_compL2 {g : Coordinates → FormValue n k} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    ∫ x, ‖g x‖ ^ 2 ≤ ‖(coordinates n k).symm.toContinuousLinearMap‖ ^ 2 * compL2 g := by
  have h := TernaryPoly.FiniteCoordinateSquare.compact_integral_square_le_coordinates
    (E := Coordinates) (F := FormValue n k) (I := Index n k) volume (coordinates n k) g hg hc
  exact h

theorem compL2_nonneg (g : Coordinates → FormValue n k) : 0 ≤ compL2 g :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

theorem contDiff_components_cut {χ : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ positiveCoordinates) {f : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (i : Index n k) :
    ContDiff ℝ ∞ (fun y => χ y * components n k f i y) :=
  by
  have h := contDiff_components_of (contDiff_cut hχ hsχ hf) i
  rwa [show components n k (fun y => χ y • f y) i = fun y => χ y * components n k f i y from
    funext (components_smul_fun χ f i)] at h

/-- Uniform plain `L²` bound of the mollifier, independent of the scale. -/
theorem integral_norm_frMol_le {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ positiveCoordinates)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ x, ‖η x‖ ≤ M) {c : ℝ} (hc : 0 < c)
    {f : Coordinates → FormValue n k} (hf : ContDiffOn ℝ ∞ f positiveCoordinates) :
    ∫ x, ‖frMol n k χ η c f x‖ ^ 2 ≤
      ‖(coordinates n k).symm.toContinuousLinearMap‖ ^ 2 * M ^ 2 *
        compL2 (fun y => χ y • f y) := by
  have h := finite_mollifier_square_bound (E := Coordinates) (F := FormValue n k)
    (I := Index n k) volume (coordinates n k)
    (components n k (fun y => χ y • f y))
    (fun i => (contDiff_components_of (contDiff_cut hχ hsχ hf) i).continuous)
    (fun i => (hasCompactSupport_cut hcχ f).comp_left (g := fun z : FormValue n k =>
      coordinates n k z i)
      (by simp only [ContinuousLinearEquiv.map_zero, Pi.zero_apply]))
    η hη.continuous hcη M hM hηM c hc
  exact h

/-- The plain coordinate mass of the mollifier is bounded uniformly in the scale. -/
theorem compL2_frMol_le {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ positiveCoordinates)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ x, ‖η x‖ ≤ M) {c : ℝ} (hc : 0 < c)
    {f : Coordinates → FormValue n k} (hf : ContDiffOn ℝ ∞ f positiveCoordinates) :
    compL2 (frMol n k χ η c f) ≤
      (((Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2) *
        (‖(coordinates n k).symm.toContinuousLinearMap‖ ^ 2 * M ^ 2)) *
        compL2 (fun y => χ y • f y) := by
  have h1 := compL2_le_integral (contDiff_frMol hχ hsχ hη hc.ne' hf).continuous
    (hasCompactSupport_frMol hcη c f)
  have h2 := integral_norm_frMol_le hχ hcχ hsχ hη hcη hM hηM hc hf
  exact h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (mul_assoc _ _ _).symm)

/-- The metric-density `L²` mass. -/
def wL2 (g : Coordinates → FormValue n k) : ℝ := ∫ x, weightedSquare n k g x

/-- On a compact subset of the positive coordinates the metric-density and plain coordinate
masses are comparable. -/
theorem exists_wL2_comp (n k : ℕ) {K : Set Coordinates} (hK : IsCompact K)
    (hKpos : K ⊆ positiveCoordinates) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ g : Coordinates → FormValue n k, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ K → wL2 g ≤ A * compL2 g ∧ compL2 g ≤ A * wL2 g := by
  obtain ⟨C1, hC1, hU⟩ := exists_compact_weighted_coordinate_upper n k hK hKpos
  obtain ⟨c, C, hc, hC, hb⟩ := compact_integral_weighted_bounds n k hK hKpos
  let D : ℝ := (Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2
  have hD : 0 ≤ D := by positivity
  refine ⟨max C1 (D / c), le_max_of_le_left hC1, fun g hg hcg hsg => ⟨?_, ?_⟩⟩
  · exact (hU g hg hcg hsg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (compL2_nonneg g))
  · have h1 := compL2_le_integral hg.continuous hcg
    have h2 := (hb g hg hcg hsg).1
    have h3 : ∫ x, ‖g x‖ ^ 2 ≤ (∫ x, weightedSquare n k g x) / c := by
      rw [le_div_iff₀ hc]
      linarith
    calc compL2 g ≤ D * ∫ x, ‖g x‖ ^ 2 := h1
      _ ≤ D * ((∫ x, weightedSquare n k g x) / c) := mul_le_mul_of_nonneg_left h3 hD
      _ = (D / c) * wL2 g := by unfold wL2; ring
      _ ≤ max C1 (D / c) * wL2 g := by
          refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
          exact (mul_nonneg hc.le (integral_nonneg (fun x => sq_nonneg _))).trans h2

/-- Uniform metric-density bound of the mollifier. -/
theorem exists_wL2_frMol_le {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ positiveCoordinates)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ positiveCoordinates)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ x, ‖η x‖ ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {c : ℝ}, 0 < c → ∀ {f : Coordinates → FormValue n k},
      ContDiffOn ℝ ∞ f positiveCoordinates → wL2 (frMol n k χ η c f) ≤ A * compL2 (fun y => χ y • f y) := by
  obtain ⟨A, hA, hAK⟩ := exists_wL2_comp n k hcη.isCompact hsη
  let A1 : ℝ := (((Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2) *
        (‖(coordinates n k).symm.toContinuousLinearMap‖ ^ 2 * M ^ 2))
  have hA1 : 0 ≤ A1 := by positivity
  refine ⟨A * A1, mul_nonneg hA hA1, fun {c} hc {f} hf => ?_⟩
  have h1 := (hAK (frMol n k χ η c f) (contDiff_frMol hχ hsχ hη hc.ne' hf)
    (hasCompactSupport_frMol hcη c f) (tsupport_frMol_subset χ η c f)).1
  have h2 := compL2_frMol_le hχ hcχ hsχ hη hcη hM hηM hc hf
  exact h1.trans ((mul_le_mul_of_nonneg_left h2 hA).trans_eq (mul_assoc _ _ _).symm)

/-- The error `η (κ_c ∗ (χ f)) - η χ f` of the mollifier, in the metric-density norm, tends to
zero as the scale tends to infinity. -/
theorem frMol_weighted_tendsto {χ η : Coordinates → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ positiveCoordinates)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ positiveCoordinates)
    {f : Coordinates → FormValue n k} (hf : ContDiffOn ℝ ∞ f positiveCoordinates) :
    Tendsto (fun c : ℝ => wL2 (fun y => frMol n k χ η c f y - η y • (χ y • f y))) atTop (𝓝 0) := by
  have h := cutoff_finite_mollifier_square_tendsto (E := Coordinates) (F := FormValue n k)
    (I := Index n k) volume (coordinates n k) (components n k (fun y => χ y • f y))
    (fun i => (contDiff_components_of (contDiff_cut hχ hsχ hf) i).continuous)
    (fun i => (hasCompactSupport_cut hcχ f).comp_left (g := fun z : FormValue n k =>
      coordinates n k z i)
      (by simp only [ContinuousLinearEquiv.map_zero, Pi.zero_apply])) η hη.continuous hcη
  have hw : ∀ᶠ c : ℝ in atTop, ContDiff ℝ ∞ (fun y => frMol n k χ η c f y - η y • (χ y • f y)) ∧
      HasCompactSupport (fun y => frMol n k χ η c f y - η y • (χ y • f y)) ∧
      tsupport (fun y => frMol n k χ η c f y - η y • (χ y • f y)) ⊆ tsupport η := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have hsub : tsupport (fun y => frMol n k χ η c f y - η y • (χ y • f y)) ⊆ tsupport η :=
      (tsupport_sub (frMol n k χ η c f) (fun y => η y • (χ y • f y))).trans
        (union_subset (tsupport_frMol_subset χ η c f)
          (tsupport_smul_subset_left η (fun y => χ y • f y)))
    refine ⟨?_, hcη.of_isClosed_subset (isClosed_tsupport _) hsub, hsub⟩
    let : IsBoundedSMul ℝ (FormValue n k) :=
      @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
    exact (contDiff_frMol hχ hsχ hη hc.ne' hf).sub
      (ContDiff.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k) hη
        (contDiff_cut hχ hsχ hf))
  have hpt : ∀ (c : ℝ) (x : Coordinates), frMol n k χ η c f x - η x • (χ x • f x) =
      η x • (frConv n k c (fun y => χ y • f y) x - χ x • f x) :=
    fun c x => (smul_sub (η x) (frConv n k c (fun y => χ y • f y) x) (χ x • f x)).symm
  have hB : ∀ x : Coordinates, (coordinates n k).symm
      (fun i => components n k (fun y => χ y • f y) i x) = χ x • f x :=
    fun x => (coordinates n k).symm_apply_apply (χ x • f x)
  have ht : Tendsto (fun c : ℝ => ∫ x, ‖frMol n k χ η c f x - η x • (χ x • f x)‖ ^ 2)
      atTop (𝓝 0) :=
    Tendsto.congr (fun c => (integral_congr_ae (Eventually.of_forall (fun x =>
      (congrArg (fun z : FormValue n k => ‖z‖ ^ 2) (hpt c x)).trans
        (congrArg (fun z : FormValue n k => ‖η x • (frConv n k c (fun y => χ y • f y) x - z)‖ ^ 2)
          (hB x).symm)))).symm) h
  exact compact_weighted_square_tendsto n k (tsupport η) hcη.isCompact hsη
    (fun c => fun y => frMol n k χ η c f y - η y • (χ y • f y)) hw ht

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
