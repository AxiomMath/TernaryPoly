module

public import TernaryPeriodPolynomials.DifferentialForm.LocalIntegrationTest
public import TernaryPeriodPolynomials.DifferentialForm.TestPairing
public import TernaryPeriodPolynomials.DifferentialForm.Deck.Integration

@[expose] public section


/-! Linearity of the genuine local adjoint on its actual smooth domain. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open SmoothLocalDeRham Set MeasureTheory
open scoped ContDiff

theorem tsupport_extDeriv_subset (n k : ℕ) (f : Coordinates → FormValue n k) :
    tsupport (extDeriv f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  exact hx (extDeriv_eq_zero_of_notMem_tsupport n k f hn)

@[simp] theorem localAdjoint_zero (n k : ℕ) : localAdjoint n k 0 = 0 := by
  have hs := tsupport_localAdjoint n k 0
  rw [tsupport_zero] at hs
  funext x
  exact image_eq_zero_of_notMem_tsupport (fun hx => hs hx)

theorem localIntegral_add_right (n k : ℕ) {f g z : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (hg : ContDiffOn ℝ ∞ g positiveCoordinates)
    (hz : ContDiffOn ℝ ∞ z positiveCoordinates) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ positiveCoordinates) :
    localIntegral n k f (g + z) = localIntegral n k f g + localIntegral n k f z := by
  unfold localIntegral
  simp only [Pi.add_apply, formPairing_add_right, mul_add]
  exact integral_add (integrable_densityPairing n k hf hg hc hs)
    (integrable_densityPairing n k hf hz hc hs)

theorem localIntegral_smul_right (n k : ℕ) (c : ℝ) (f g : Coordinates → FormValue n k) :
    localIntegral n k f (c • g) = c * localIntegral n k f g := by
  unfold localIntegral
  simp only [Pi.smul_apply, formPairing_smul_right]
  simp_rw [mul_left_comm (coordinateDensity _) c]
  exact integral_const_mul _ _

/-- Actual addition law, with precisely the smoothness needed by the differential expression. -/
theorem localAdjoint_add (n k : ℕ) {w z : Coordinates → FormValue n (k + 1)}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (hz : ContDiffOn ℝ ∞ z positiveCoordinates) :
    EqOn (localAdjoint n k (w + z)) (localAdjoint n k w + localAdjoint n k z) positiveCoordinates := by
  apply eqOn_of_form_test_integrals n k (contDiffOn_localAdjoint n k (hw.add hz))
    ((contDiffOn_localAdjoint n k hw).add (contDiffOn_localAdjoint n k hz))
  intro f hf hc hs
  have hds := tsupport_extDeriv_subset n k f
  have hdc : HasCompactSupport (extDeriv f) := hc.of_isClosed_subset (isClosed_tsupport _) hds
  have hd := smooth_extDeriv isOpen_positiveCoordinates hf.contDiffOn
  change localIntegral n k f (localAdjoint n k (w + z)) =
    localIntegral n k f (localAdjoint n k w + localAdjoint n k z)
  calc
    _ = localIntegral n k f (localAdjoint n k w) + localIntegral n k f (localAdjoint n k z) := by
      change (∫ x, coordinateDensity x * formPairing n k x (f x) (localAdjoint n k (w + z) x)) = _
      rw [← integral_extDeriv_localAdjoint_test n k f (w + z) hf.contDiffOn (hw.add hz) hc hs]
      change localIntegral n (k + 1) (extDeriv f) (w + z) = _
      rw [localIntegral_add_right n (k + 1) hd hw hz hdc (hds.trans hs)]
      exact congrArg₂ (· + ·) (integral_extDeriv_localAdjoint_test n k f w hf.contDiffOn hw hc hs)
        (integral_extDeriv_localAdjoint_test n k f z hf.contDiffOn hz hc hs)
    _ = _ := (localIntegral_add_right n k hf.contDiffOn (contDiffOn_localAdjoint n k hw)
      (contDiffOn_localAdjoint n k hz) hc hs).symm

/-- Actual scalar-linearity law on smooth forms. -/
theorem localAdjoint_smul (n k : ℕ) (c : ℝ) {w : Coordinates → FormValue n (k + 1)}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    EqOn (localAdjoint n k (c • w)) (c • localAdjoint n k w) positiveCoordinates := by
  apply eqOn_of_form_test_integrals n k (contDiffOn_localAdjoint n k (hw.const_smul c))
    ((contDiffOn_localAdjoint n k hw).const_smul c)
  intro f hf hc hs
  change localIntegral n k f (localAdjoint n k (c • w)) = localIntegral n k f (c • localAdjoint n k w)
  calc
    _ = localIntegral n (k + 1) (extDeriv f) (c • w) :=
      (integral_extDeriv_localAdjoint_test n k f (c • w) hf.contDiffOn (hw.const_smul c) hc hs).symm
    _ = c * localIntegral n (k + 1) (extDeriv f) w := localIntegral_smul_right n (k + 1) c _ _
    _ = c * localIntegral n k f (localAdjoint n k w) :=
      congrArg (c * ·) (integral_extDeriv_localAdjoint_test n k f w hf.contDiffOn hw hc hs)
    _ = _ := (localIntegral_smul_right n k c f (localAdjoint n k w)).symm

end TernaryPoly.PolynomialFormCoordinates
