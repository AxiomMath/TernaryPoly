module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingSupport
public import TernaryPeriodPolynomials.DifferentialForm.QuotientPairing
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic

@[expose] public section


/-! Actual quotient scalar multiplication and its genuine form metric. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham SmoothDeRhamGluing
  PolynomialCoefficientMetric PolynomialCoefficientBundle PolynomialFormMetric PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold SymmetricSpaceRiemannian

theorem scalarPairing_scalarMultiply_left (n k : ℕ) {U : Set OrbitSpace}
    (χ : OrbitSpace → ℝ) (hχ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ U)
    (a b : EquivariantForm (deckRepresentation n) U k) (q : OrbitSpace) :
    scalarPairing n k (scalarMultiply (deckRepresentation n) χ hχ k a) b q =
      χ q * scalarPairing n k a b q := by
  change formPairing n k (coordinateChart (chosenLift q))
    (liftScalar χ (coordinateChart (chosenLift q)) • a.val.val (coordinateChart (chosenLift q)))
    (b.val.val (coordinateChart (chosenLift q))) = _
  rw [formPairing_smul_left]
  congr 1
  simp only [liftScalar, Function.comp_apply, coordinateProjection,
    coordinateChart.left_inv (by simp), chosenLift_projection]

theorem scalarPairing_scalarMultiply_right (n k : ℕ) {U : Set OrbitSpace}
    (χ : OrbitSpace → ℝ) (hχ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ U)
    (a b : EquivariantForm (deckRepresentation n) U k) (q : OrbitSpace) :
    scalarPairing n k a (scalarMultiply (deckRepresentation n) χ hχ k b) q =
      χ q * scalarPairing n k a b q := by
  rw [scalarPairing_symm, scalarPairing_scalarMultiply_left, scalarPairing_symm n k b a]

/-- This is the existing literal multiplication on genuine compact quotient forms. -/
def coreScalarMultiply (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) : Core n k →ₗ[ℝ] Core n k :=
  compactScalarMultiply (ρ := deckRepresentation n) χ hχ.contMDiffOn k

@[simp] theorem coreScalarMultiply_apply (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k) (x : Coordinates) :
    (coreScalarMultiply n k χ hχ a).val.val.val x = χ (coordinateProjection x) • a.val.val.val x := rfl

theorem coreScalarMultiply_val (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k) :
    (coreScalarMultiply n k χ hχ a).val = scalarMultiply (deckRepresentation n) χ hχ.contMDiffOn k a.val := rfl

attribute [irreducible] coreScalarMultiply

theorem scalarPairing_coreScalarMultiply_left (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k)
    (b : EquivariantForm (deckRepresentation n) univ k) (q : OrbitSpace) :
    scalarPairing n k (coreScalarMultiply n k χ hχ a).val b q =
      χ q * scalarPairing n k a.val b q :=
  (congrArg (fun z => scalarPairing n k z b q) (coreScalarMultiply_val n k χ hχ a)).trans
    (scalarPairing_scalarMultiply_left n k χ hχ.contMDiffOn a.val b q)

theorem scalarPairing_coreScalarMultiply_right (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ)
    (a : EquivariantForm (deckRepresentation n) univ k) (b : Core n k) (q : OrbitSpace) :
    scalarPairing n k a (coreScalarMultiply n k χ hχ b).val q =
      χ q * scalarPairing n k a b.val q :=
  (congrArg (fun z => scalarPairing n k a z q) (coreScalarMultiply_val n k χ hχ b)).trans
    (scalarPairing_scalarMultiply_right n k χ hχ.contMDiffOn a b.val q)

theorem scalarPairing_coreScalarMultiply_self (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k) (q : OrbitSpace) :
    scalarPairing n k (coreScalarMultiply n k χ hχ a).val
      (coreScalarMultiply n k χ hχ a).val q = χ q ^ 2 * scalarPairing n k a.val a.val q := by
  calc
    _ = χ q * scalarPairing n k a.val (coreScalarMultiply n k χ hχ a).val q :=
      scalarPairing_coreScalarMultiply_left n k χ hχ a _ q
    _ = χ q * (χ q * scalarPairing n k a.val a.val q) :=
      congrArg (χ q * ·) (scalarPairing_coreScalarMultiply_right n k χ hχ a.val a q)
    _ = _ := by ring

theorem coreScalarMultiply_square_bound (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ q, |χ q| ≤ A) (a : Core n k) :
    ‖inclusion n k (coreScalarMultiply n k χ hχ a)‖ ^ 2 ≤ A ^ 2 * ‖inclusion n k a‖ ^ 2 := by
  have hnorm (b : Core n k) : ‖inclusion n k b‖ ^ 2 =
      ∫ q, scalarPairing n k b.val b.val q ∂orbitVolume :=
    (real_inner_self_eq_norm_sq (inclusion n k b)).symm.trans (inner_inclusion n k b b)
  let b := coreScalarMultiply n k χ hχ a
  have hp (q : OrbitSpace) : scalarPairing n k b.val b.val q ≤ A ^ 2 * scalarPairing n k a.val a.val q :=
    (scalarPairing_coreScalarMultiply_self n k χ hχ a q).trans_le
      (mul_le_mul_of_nonneg_right
        (sq_le_sq.mpr (by simpa only [abs_of_nonneg hA] using hb q))
        (scalarPairing_nonneg n k a.val q))
  calc
    _ = ∫ q, scalarPairing n k b.val b.val q ∂orbitVolume := hnorm b
    _ ≤ ∫ q, A ^ 2 * scalarPairing n k a.val a.val q ∂orbitVolume :=
      integral_mono (PolynomialFormCoordinates.integrable_scalarPairing n k b b.val)
        ((PolynomialFormCoordinates.integrable_scalarPairing n k a a.val).const_mul _) hp
    _ = _ := (integral_const_mul (A ^ 2) (scalarPairing n k a.val a.val)).trans
      (congrArg (A ^ 2 * ·) (hnorm a).symm)

theorem coreScalarMultiply_bound (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ q, |χ q| ≤ A) (a : Core n k) :
    ‖inclusion n k (coreScalarMultiply n k χ hχ a)‖ ≤ A * ‖inclusion n k a‖ := by
  have hh := coreScalarMultiply_square_bound n k χ hχ hA hb a
  have hp := mul_nonneg hA (norm_nonneg (inclusion n k a))
  exact (sq_le_sq₀ (norm_nonneg _) hp).mp (hh.trans_eq (mul_pow A ‖inclusion n k a‖ 2).symm)

theorem inner_coreScalarMultiply (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a b : Core n k) :
    inner ℝ (inclusion n k (coreScalarMultiply n k χ hχ a)) (inclusion n k b) =
      inner ℝ (inclusion n k a) (inclusion n k (coreScalarMultiply n k χ hχ b)) := by
  refine (inner_inclusion n k (coreScalarMultiply n k χ hχ a) b).trans
    (Eq.trans ?_ (inner_inclusion n k a (coreScalarMultiply n k χ hχ b)).symm)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q =>
    (scalarPairing_coreScalarMultiply_left n k χ hχ a b.val q).trans
      (scalarPairing_coreScalarMultiply_right n k χ hχ a.val b q).symm)

/-- A cutoff equal to one on actual projected support fixes the actual compact form. -/
theorem coreScalarMultiply_eq_self (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k)
    (he : EqOn χ (fun _ => (1 : ℝ)) (quotientSupport a.val)) :
    coreScalarMultiply n k χ hχ a = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x _hx
  rw [coreScalarMultiply_apply]
  by_cases ha : a.val.val.val x = 0
  · rw [ha, smul_zero]
  · have hx : coordinateProjection x ∈ quotientSupport a.val :=
      subset_closure (mem_image_of_mem coordinateProjection ha)
    exact (congrArg (fun t : ℝ => t • a.val.val.val x) (he hx)).trans (one_smul ℝ _)

end TernaryPoly.PolynomialFormConnection
