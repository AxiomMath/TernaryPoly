module

public import TernaryPeriodPolynomials.DifferentialForm.AdjointDeckCovariance

@[expose] public section


/-! The actual local adjoint descends to smooth equivariant forms on the whole arithmetic quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpaceCovering
open SmoothCoveringDeRham SmoothLocalDeRham Set Filter
open scoped ContDiff Topology

/-- Actual equivariant forms are fixed by the coefficient-normalized deck pullback. -/
theorem deckPull_equivariant (n k : ℕ) (w : EquivariantForm (deckRepresentation n) univ k)
    (a : DeckGroup) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    deckPull n k a w.val.val x = w.val.val x := by
  rw [deckPull_apply n k a w.val.val hx]
  have he := w.property a x (by simpa only [liftedDomain_univ] using hx)
  change (w.val.val (deckMap a x)).compContinuousLinearMap (fderiv ℝ (deckMap a) x) = _ at he
  rw [he, ← coefficientFormMap_mul, inv_mul_cancel, coefficientFormMap_one]

/-- The actual coordinate adjoint obeys the full coefficient equivariance relation. -/
theorem localAdjoint_equivariant (n k : ℕ)
    (w : EquivariantForm (deckRepresentation n) univ (k + 1)) :
    IsEquivariant (deckRepresentation n) univ (localAdjoint n k w.val.val) := by
  have hw : ContDiffOn ℝ ∞ w.val.val positiveCoordinates := by
    simpa only [liftedDomain_univ] using Form.smooth w.val
  intro a x hx
  have hxp : x ∈ positiveCoordinates := by simpa only [liftedDomain_univ] using hx
  have he : deckPull n (k + 1) a w.val.val =ᶠ[𝓝 x] w.val.val := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hxp] with y hy
    exact deckPull_equivariant n (k + 1) w a hy
  have hcov := localAdjoint_deckPull n k a hw hxp
  rw [localAdjoint_congr n k he] at hcov
  have hp := deckPull_equation n k a (localAdjoint n k w.val.val) hxp
  rw [← hcov] at hp
  exact hp.symm

/-- The genuine smooth adjoint on global equivariant forms, canonically zero outside the domain. -/
def equivariantAdjoint (n k : ℕ) (w : EquivariantForm (deckRepresentation n) univ (k + 1)) :
    EquivariantForm (deckRepresentation n) univ k := by
  have hs : ContDiffOn ℝ ∞ (localAdjoint n k w.val.val) (liftedDomain univ) := by
    simpa only [liftedDomain_univ] using contDiffOn_localAdjoint n k
      (show ContDiffOn ℝ ∞ w.val.val positiveCoordinates from
        by simpa only [liftedDomain_univ] using Form.smooth w.val)
  refine ⟨restrictForm (liftedDomain univ) (localAdjoint n k w.val.val) hs, ?_⟩
  intro a x hx
  have hax := deckMap_liftedDomain a univ hx
  change ((restrictForm (liftedDomain univ) (localAdjoint n k w.val.val) hs).val
    (deckMap a x)).compContinuousLinearMap (fderiv ℝ (deckMap a) x) =
      coefficientFormMap (coefficientMap (deckRepresentation n) a) k
        ((restrictForm (liftedDomain univ) (localAdjoint n k w.val.val) hs).val x)
  rw [restrictForm_apply _ _ hax, restrictForm_apply _ _ hx]
  exact localAdjoint_equivariant n k w a x hx

@[simp] theorem equivariantAdjoint_apply (n k : ℕ)
    (w : EquivariantForm (deckRepresentation n) univ (k + 1)) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    (equivariantAdjoint n k w).val.val x = localAdjoint n k w.val.val x :=
  indicator_of_mem (by simpa only [liftedDomain_univ] using hx) _

end TernaryPoly.PolynomialFormCoordinates
