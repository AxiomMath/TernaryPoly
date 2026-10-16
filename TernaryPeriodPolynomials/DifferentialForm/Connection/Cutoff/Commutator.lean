module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Metric
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingOrdinaryMaps
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Slope
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.SymbolTransport

@[expose] public section


/-! Literal compact differential commutators and their actual uniform metric bound. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham SmoothDeRhamGluing
  PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormHilbert PolynomialFormCoordinates
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
  PolynomialCoefficientBundle Manifold
open scoped ContDiff Manifold SymmetricSpaceRiemannian Topology

/-- The genuine compact exterior differential commutator with a smooth global scalar. -/
def coreExteriorCommutator (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) : Core n k →ₗ[ℝ] Core n (k + 1) :=
  (compactDifferential (deckRepresentation n) isOpen_univ k).comp (coreScalarMultiply n k χ hχ) -
    (coreScalarMultiply n (k + 1) χ hχ).comp (compactDifferential (deckRepresentation n) isOpen_univ k)

theorem coreExteriorCommutator_eq (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k) :
    coreExteriorCommutator n k χ hχ a =
      compactDifferential (deckRepresentation n) isOpen_univ k (coreScalarMultiply n k χ hχ a) -
        coreScalarMultiply n (k + 1) χ hχ (compactDifferential (deckRepresentation n) isOpen_univ k a) := rfl

attribute [irreducible] coreExteriorCommutator

/-- Its coordinate value is the literal scalar exterior symbol, including every derivative of chi. -/
theorem coreExteriorCommutator_apply (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (coreExteriorCommutator n k χ hχ a).val.val.val x =
      scalarWedge (fderiv ℝ (liftScalar χ) x) (a.val.val.val x) := by
  let d := compactDifferential (deckRepresentation n) isOpen_univ k
  have hd : (d (coreScalarMultiply n k χ hχ a)).val.val.val x =
      scalarWedge (fderiv ℝ (liftScalar χ) x) (a.val.val.val x) +
        χ (coordinateProjection x) • (d a).val.val.val x :=
    (congrArg (fun z => (SmoothCoveringDeRham.differential (deckRepresentation n) isOpen_univ k z).val.val x)
      (coreScalarMultiply_val n k χ hχ a)).trans
      (differential_scalarMultiply (deckRepresentation n) isOpen_univ χ hχ.contMDiffOn a.val ⟨hx, mem_univ _⟩)
  calc
    _ = (d (coreScalarMultiply n k χ hχ a)).val.val.val x -
        (coreScalarMultiply n (k + 1) χ hχ (d a)).val.val.val x :=
      congrArg (fun z : Core n (k + 1) => z.val.val.val x) (coreExteriorCommutator_eq n k χ hχ a)
    _ = (scalarWedge (fderiv ℝ (liftScalar χ) x) (a.val.val.val x) +
        χ (coordinateProjection x) • (d a).val.val.val x) -
        χ (coordinateProjection x) • (d a).val.val.val x :=
      congrArg₂ (· - ·) hd (coreScalarMultiply_apply n (k + 1) χ hχ (d a) x)
    _ = _ := add_sub_cancel_right _ _

/-- This is the exact Leibniz identity for the actual compact differential. -/
theorem compactDifferential_coreScalarMultiply (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k) :
    compactDifferential (deckRepresentation n) isOpen_univ k (coreScalarMultiply n k χ hχ a) =
      coreScalarMultiply n (k + 1) χ hχ (compactDifferential (deckRepresentation n) isOpen_univ k a) +
        coreExteriorCommutator n k χ hχ a := by
  have h := coreExteriorCommutator_eq n k χ hχ a
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- The bound is uniform over the actual quotient and over the scalar function. -/
theorem exists_coreExteriorCommutator_square_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : OrbitSpace → ℝ)
      (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ), 0 ≤ B →
      (∀ q, scalarSlope χ q ≤ B) → ∀ a : Core n k,
      ‖inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a)‖ ^ 2 ≤
        C * B ^ 2 * ‖inclusion n k a‖ ^ 2 := by
  let H := exists_scalarWedge_metric_bound n k
  let C : ℝ := H.choose
  have hC : 0 ≤ C := H.choose_spec.1
  have h := H.choose_spec.2
  refine ⟨C, hC, fun χ hχ B hB hb a => ?_⟩
  let b := coreExteriorCommutator n k χ hχ a
  have hp (q : OrbitSpace) : scalarPairing n (k + 1) b.val b.val q ≤
      C * B ^ 2 * scalarPairing n k a.val a.val q := by
    change formPairing n (k + 1) (coordinateChart (chosenLift q))
      (b.val.val.val (coordinateChart (chosenLift q))) (b.val.val.val (coordinateChart (chosenLift q))) ≤ _
    have he := coreExteriorCommutator_apply n k χ hχ a (coordinateChart (chosenLift q)) (extract_mem _)
    exact (congrArg₂ (formPairing n (k + 1) (coordinateChart (chosenLift q))) he he).trans_le
      (h B hB _ (extract_mem _) _ (liftScalar_derivative_slope_bound χ hχ hb _ (extract_mem _)) _)
  have hn (r : ℕ) (w : Core n r) : ‖inclusion n r w‖ ^ 2 =
      ∫ q, scalarPairing n r w.val w.val q ∂orbitVolume :=
    (real_inner_self_eq_norm_sq (inclusion n r w)).symm.trans (inner_inclusion n r w w)
  calc
    _ = ∫ q, scalarPairing n (k + 1) b.val b.val q ∂orbitVolume := hn (k + 1) b
    _ ≤ ∫ q, (C * B ^ 2) * scalarPairing n k a.val a.val q ∂orbitVolume :=
      integral_mono (integrable_scalarPairing n (k + 1) b b.val)
        ((integrable_scalarPairing n k a a.val).const_mul _) hp
    _ = _ := (integral_const_mul (C * B ^ 2) (scalarPairing n k a.val a.val)).trans
      (congrArg ((C * B ^ 2) * ·) (hn k a).symm)

end TernaryPoly.PolynomialFormConnection
