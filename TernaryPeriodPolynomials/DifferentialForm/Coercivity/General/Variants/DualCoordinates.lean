module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Theta
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.SpaceVolume
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Inverse
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricNormalizeDerivative

@[expose] public section


/-!
# General coercivity, dual coefficients: the Cartan involution in coordinates

`iotaC x = extract (normalize (reconstruct x)⁻¹)` is the coordinate expression of the Cartan
involution `S ↦ S⁻¹ / tr S⁻¹` of the model `Space`.  It is an involutive diffeomorphism of the
positive coordinates carrying the action of `g` to the action of `θ g`, and it is an isometry of the
trace metric: the differential satisfies
`coordinatePair (iotaC x) (D v) (D w) = coordinatePair x v w`.  Hence it preserves the Riemannian
density and volume.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set Matrix MeasureTheory TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceTraceMetric
open TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.PolynomialFormConnection
open TernaryPoly.PolynomialCoefficientMetric
open scoped ContDiff Matrix.Norms.Elementwise Topology

/-- The Cartan involution in the five coordinates. -/
def iotaC (x : Coordinates) : Coordinates := extract (normalize (reconstruct x)⁻¹)

theorem iotaC_chart (S : Space) : iotaC (coordinateChart S) = coordinateChart (iota S) := by
  change extract (normalize (reconstruct (extract S.val))⁻¹) = extract (iota S).val
  rw [reconstruct_extract S.val (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian)
    S.property.2]
  rfl

theorem iotaC_eq_chart {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    iotaC x = coordinateChart (iota (coordinateChart.symm x)) := by
  rw [← iotaC_chart, coordinateChart.right_inv (by simpa using hx)]

theorem iotaC_mem {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    iotaC x ∈ positiveCoordinates := by
  rw [iotaC_eq_chart hx]
  exact extract_mem _

theorem reconstruct_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    reconstruct (iotaC x) = normalize (reconstruct x)⁻¹ := by
  rw [iotaC_eq_chart hx]
  have h : reconstruct (coordinateChart (iota (coordinateChart.symm x))) =
      (iota (coordinateChart.symm x)).val :=
    reconstruct_extract _ (Matrix.isHermitian_iff_isSymm.mp
      (iota (coordinateChart.symm x)).property.1.isHermitian)
      (iota (coordinateChart.symm x)).property.2
  rw [h, iota_val, coordinateChart_inverse x hx]

theorem iotaC_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates) : iotaC (iotaC x) = x := by
  rw [iotaC_eq_chart hx, iotaC_chart, iota_iota, coordinateChart.right_inv (by simpa using hx)]

theorem iotaC_injOn : InjOn iotaC positiveCoordinates := fun x hx y hy h => by
  rw [← iotaC_iotaC hx, ← iotaC_iotaC hy, h]

theorem iotaC_action (g : RealGL) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    iotaC (coordinateAction g x) = coordinateAction (thetaHom g) (iotaC x) := by
  obtain ⟨S, rfl⟩ : ∃ S : Space, x = coordinateChart S :=
    ⟨coordinateChart.symm x, (coordinateChart.right_inv (by simpa using hx)).symm⟩
  rw [← coordinateChart_act, iotaC_chart, iota_act, coordinateChart_act, iotaC_chart]

theorem contDiffOn_iotaC : ContDiffOn ℝ ∞ iotaC positiveCoordinates := by
  have hR : ContDiffOn ℝ ∞ (fun x => (reconstruct x)⁻¹) positiveCoordinates :=
    contDiffOn_inverse contDiff_reconstruct.contDiffOn
      (fun x hx => (show (reconstruct x).PosDef from hx).isUnit)
  have hne : ∀ x ∈ positiveCoordinates, ((reconstruct x)⁻¹).trace ≠ 0 := fun x hx =>
    (Matrix.PosDef.inv (show (reconstruct x).PosDef from hx)).trace_pos.ne'
  exact contDiff_extract.comp_contDiffOn (((contDiffOn_trace hR).inv hne).smul hR)

/-- The derivative of the inverse of the reconstructed matrix, from differentiating `S S⁻¹ = 1`. -/
theorem fderiv_reconstruct_inv {x : Coordinates} (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    fderiv ℝ (fun y => (reconstruct y)⁻¹) x v =
      -((reconstruct x)⁻¹ * tangentMatrix v * (reconstruct x)⁻¹) := by
  have hR : ContDiffOn ℝ ∞ (fun x => (reconstruct x)⁻¹) positiveCoordinates :=
    contDiffOn_inverse contDiff_reconstruct.contDiffOn
      (fun x hx => (show (reconstruct x).PosDef from hx).isUnit)
  have hi : DifferentiableAt ℝ (fun y => (reconstruct y)⁻¹) x :=
    (hR.contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hd := hasDerivAt_matrixField_line _ x v hi
  have hr := hasDerivAt_matrixField_line reconstruct x v
    (contDiff_reconstruct.differentiable (by simp) x)
  rw [fderiv_reconstruct, tangentCLM_apply] at hr
  have hp := hasDerivAt_matrix_product hr hd
  have hc : HasDerivAt (fun _ : ℝ => (1 : TernaryPoly.SymmetricSpacePositive.Mat))
      (tangentMatrix v * (reconstruct x)⁻¹ +
        reconstruct x * fderiv ℝ (fun y => (reconstruct y)⁻¹) x v) 0 := by
    have he : (fun _ : ℝ => (1 : TernaryPoly.SymmetricSpacePositive.Mat)) =ᶠ[nhds 0]
        (fun t : ℝ => reconstruct (x + t • v) * (reconstruct (x + t • v))⁻¹) := by
      filter_upwards [eventually_coordinateLine_positive x hx v] with t ht
      exact (Matrix.mul_nonsing_inv _
        ((reconstruct (x + t • v)).isUnit_iff_isUnit_det.mp
          (show (reconstruct (x + t • v)).PosDef from ht).isUnit)).symm
    have hh := hp.congr_of_eventuallyEq he
    convert! hh using 1
    simp only [zero_smul, add_zero]
  have hz := hc.unique (hasDerivAt_const (0 : ℝ) (1 : TernaryPoly.SymmetricSpacePositive.Mat))
  have he := congrArg (fun A : TernaryPoly.SymmetricSpacePositive.Mat => (reconstruct x)⁻¹ * A) hz
  have hinv := Matrix.nonsing_inv_mul (reconstruct x)
    ((reconstruct x).isUnit_iff_isUnit_det.mp (show (reconstruct x).PosDef from hx).isUnit)
  simp only [mul_add, ← mul_assoc, hinv, one_mul, mul_zero] at he
  exact eq_neg_of_add_eq_zero_right he

theorem tangentMatrix_fderiv_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (v : Coordinates) :
    tangentMatrix (fderiv ℝ iotaC x v) =
      normalizationDerivative (reconstruct x)⁻¹
        (-((reconstruct x)⁻¹ * tangentMatrix v * (reconstruct x)⁻¹)) := by
  have hR : ContDiffOn ℝ ∞ (fun x => (reconstruct x)⁻¹) positiveCoordinates :=
    contDiffOn_inverse contDiff_reconstruct.contDiffOn
      (fun x hx => (show (reconstruct x).PosDef from hx).isUnit)
  have hi : DifferentiableAt ℝ (fun y => (reconstruct y)⁻¹) x :=
    (hR.contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ iotaC x :=
    (contDiffOn_iotaC.contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)
  have htr : ((reconstruct x)⁻¹).trace ≠ 0 :=
    (Matrix.PosDef.inv (show (reconstruct x).PosDef from hx)).trace_pos.ne'
  have h1 := (hasFDerivAt_reconstruct (iotaC x)).comp x hd.hasFDerivAt
  have h2 := (hasFDerivAt_normalize _ htr).comp x hi.hasFDerivAt
  have h2' : HasFDerivAt (fun y => reconstruct (iotaC y))
      ((normalizationDerivative (reconstruct x)⁻¹).comp
        (fderiv ℝ (fun y => (reconstruct y)⁻¹) x)) x := by
    apply h2.congr_of_eventuallyEq
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact reconstruct_iotaC hy
  have he := h1.unique h2'
  have h3 := congrArg (fun L : Coordinates →L[ℝ] TernaryPoly.SymmetricSpacePositive.Mat => L v) he
  have h4 : tangentMatrix (fderiv ℝ iotaC x v) = normalizationDerivative (reconstruct x)⁻¹
      (fderiv ℝ (fun y => (reconstruct y)⁻¹) x v) := h3
  rw [h4, fderiv_reconstruct_inv hx v]

theorem tracePair_add_smul_one (A B : TernaryPoly.SymmetricSpacePositive.Mat) (c d : ℝ) :
    tracePair (A + c • (1 : TernaryPoly.SymmetricSpacePositive.Mat)) (B + d • (1 : TernaryPoly.SymmetricSpacePositive.Mat)) = tracePair A B := by
  rw [tracePair_formula, tracePair_formula]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
  ring

theorem coordinatePair_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (v w : Coordinates) :
    coordinatePair (iotaC x) (fderiv ℝ iotaC x v) (fderiv ℝ iotaC x w) = coordinatePair x v w := by
  have hP : (reconstruct x).PosDef := hx
  have hSu : IsUnit (reconstruct x).det := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hRP : ((reconstruct x)⁻¹).PosDef := Matrix.PosDef.inv hP
  have hRu : IsUnit ((reconstruct x)⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).mp hRP.isUnit
  have ht : ((reconstruct x)⁻¹).trace ≠ 0 := hRP.trace_pos.ne'
  have hSR : reconstruct x * (reconstruct x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hSu
  have hS' : (normalize (reconstruct x)⁻¹)⁻¹ =
      ((reconstruct x)⁻¹).trace • reconstruct x := by
    show (((reconstruct x)⁻¹).trace⁻¹ • (reconstruct x)⁻¹)⁻¹ = _
    rw [Matrix.inv_eq_right_inv (B := ((reconstruct x)⁻¹).trace • reconstruct x)]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul,
      Matrix.nonsing_inv_mul _ hSu]
  have key : ∀ a : Coordinates, ∃ c : ℝ,
      (normalize (reconstruct x)⁻¹)⁻¹ * tangentMatrix (fderiv ℝ iotaC x a) =
        -(tangentMatrix a * (reconstruct x)⁻¹) + c • (1 : TernaryPoly.SymmetricSpacePositive.Mat) := by
    intro a
    refine ⟨-((reconstruct x)⁻¹.trace)⁻¹ * (-((reconstruct x)⁻¹ * tangentMatrix a *
      (reconstruct x)⁻¹)).trace, ?_⟩
    rw [tangentMatrix_fderiv_iotaC hx a, normalizationDerivative_apply, hS',
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul, Matrix.mul_add,
      Matrix.mul_smul, hSR]
    congr 1
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSR, Matrix.one_mul]
  obtain ⟨c, hc⟩ := key v
  obtain ⟨d, hd⟩ := key w
  calc coordinatePair (iotaC x) (fderiv ℝ iotaC x v) (fderiv ℝ iotaC x w)
      = tracePair ((normalize (reconstruct x)⁻¹)⁻¹ * tangentMatrix (fderiv ℝ iotaC x v))
          ((normalize (reconstruct x)⁻¹)⁻¹ * tangentMatrix (fderiv ℝ iotaC x w)) := by
        unfold coordinatePair tangentPair
        rw [reconstruct_iotaC hx]
    _ = tracePair (-(tangentMatrix v * (reconstruct x)⁻¹))
          (-(tangentMatrix w * (reconstruct x)⁻¹)) := by
        rw [hc, hd, tracePair_add_smul_one]
    _ = coordinatePair x v w := by
        unfold coordinatePair tangentPair
        rw [tracePair_formula, tracePair_formula, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
          Matrix.trace_neg, Matrix.trace_neg, neg_mul_neg]
        have e1 : (tangentMatrix v * (reconstruct x)⁻¹ * (tangentMatrix w * (reconstruct x)⁻¹)).trace =
            ((reconstruct x)⁻¹ * tangentMatrix v * ((reconstruct x)⁻¹ * tangentMatrix w)).trace := by
          rw [show tangentMatrix v * (reconstruct x)⁻¹ * (tangentMatrix w * (reconstruct x)⁻¹) =
              (tangentMatrix v * (reconstruct x)⁻¹ * tangentMatrix w) * (reconstruct x)⁻¹ by
            simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
        rw [e1, Matrix.trace_mul_comm (tangentMatrix v) _, Matrix.trace_mul_comm (tangentMatrix w) _]

/-! ### The involution preserves the Riemannian volume -/

theorem coordinateBilin_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    LinearMap.BilinForm.comp (coordinateBilin (iotaC x)) (fderiv ℝ iotaC x).toLinearMap
      (fderiv ℝ iotaC x).toLinearMap = coordinateBilin x := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact coordinatePair_iotaC hx v w

theorem coordinateDensity_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateDensity x =
      |(fderiv ℝ iotaC x).toLinearMap.det| * coordinateDensity (iotaC x) := by
  change TernaryPoly.BilinearVolumeDensity.density (coordinateBilin x) = _
  rw [← coordinateBilin_iotaC hx, TernaryPoly.BilinearVolumeDensity.density_comp]
  rfl

theorem coordinateVolume_iotaC_image {s : Set Coordinates} (hs : MeasurableSet s)
    (hsub : s ⊆ positiveCoordinates) : coordinateVolume (iotaC '' s) = coordinateVolume s := by
  have hd (x : Coordinates) (hx : x ∈ s) :
      HasFDerivWithinAt iotaC (fderiv ℝ iotaC x) s x :=
    ((contDiffOn_iotaC.differentiableOn (by simp) x (hsub hx)).differentiableAt
      (isOpen_positiveCoordinates.mem_nhds (hsub hx))).hasFDerivAt.hasFDerivWithinAt
  rw [coordinateVolume_apply, coordinateVolume_apply,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd (iotaC_injOn.mono hsub)]
  apply setLIntegral_congr_fun hs
  intro x hx
  change ENNReal.ofReal |(fderiv ℝ iotaC x).det| * ENNReal.ofReal (coordinateDensity (iotaC x)) =
    ENNReal.ofReal (coordinateDensity x)
  rw [coordinateDensity_iotaC (hsub hx), ENNReal.ofReal_mul (abs_nonneg _)]

/-- The Cartan involution preserves the Riemannian volume of `Space`. -/
theorem spaceVolume_iota_image {s : Set Space} (hs : MeasurableSet s) :
    spaceVolume (iota '' s) = spaceVolume s := by
  rw [spaceVolume_apply, spaceVolume_apply]
  have himg : coordinateChart '' (iota '' s) = iotaC '' (coordinateChart '' s) := by
    rw [image_image, image_image]
    exact image_congr (fun S _ => (iotaC_chart S).symm)
  rw [himg]
  exact coordinateVolume_iotaC_image
    (measurableEmbedding_coordinateChart.measurableSet_image.mpr hs)
    (by rintro _ ⟨S, _, rfl⟩; exact extract_mem S)

theorem measurePreserving_iota : MeasurePreserving iota spaceVolume spaceVolume := by
  refine ⟨continuous_iota.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply continuous_iota.measurable hs]
  have : iota ⁻¹' s = iota '' s := by
    ext S
    constructor
    · intro hS
      exact ⟨iota S, hS, iota_iota S⟩
    · rintro ⟨T, hT, rfl⟩
      change iota (iota T) ∈ s
      rw [iota_iota]
      exact hT
  rw [this]
  exact spaceVolume_iota_image hs

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
