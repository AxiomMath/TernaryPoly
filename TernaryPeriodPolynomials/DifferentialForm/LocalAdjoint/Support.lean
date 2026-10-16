module

public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic

@[expose] public section


/-! The actual local exterior adjoint does not enlarge the support of genuine forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration Set
open scoped ContDiff

/-- The local inverse-Gram adjoint has support contained in the original closed form support. -/
theorem tsupport_localAdjoint (n k : ℕ) (w : Coordinates → FormValue n (k + 1)) :
    tsupport (localAdjoint n k w) ⊆ tsupport w := by
  have hs (i : Index n k) : tsupport (components n k (localAdjoint n k w) i) ⊆ tsupport w := by
    rw [components_localAdjoint]
    exact tsupport_weightedMatrixAdjoint_subset _ _ _ _ _ _ (isClosed_tsupport w)
      (fun j => tsupport_components n (k + 1) w j) i
  apply closure_minimal _ (isClosed_tsupport w)
  intro x hx
  by_contra hn
  apply hx
  apply (coordinates n k).injective
  ext i
  change components n k (localAdjoint n k w) i x = _
  rw [image_eq_zero_of_notMem_tsupport (fun h => hn (hs i h))]
  simp only [ContinuousLinearEquiv.map_zero, Pi.zero_apply]

theorem hasCompactSupport_localAdjoint (n k : ℕ) (w : Coordinates → FormValue n (k + 1))
    (hw : HasCompactSupport w) : HasCompactSupport (localAdjoint n k w) :=
  hw.of_isClosed_subset (isClosed_tsupport _) (tsupport_localAdjoint n k w)

/-- Compact coordinate forms supported inside the true open domain have globally smooth adjoints. -/
theorem contDiff_localAdjoint (n k : ℕ) {w : Coordinates → FormValue n (k + 1)}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (hs : tsupport w ⊆ positiveCoordinates) :
    ContDiff ℝ ∞ (localAdjoint n k w) :=
  contDiff_of_tsupport_subset isOpen_positiveCoordinates (contDiffOn_localAdjoint n k hw)
    ((tsupport_localAdjoint n k w).trans hs)

end TernaryPoly.PolynomialFormCoordinates
