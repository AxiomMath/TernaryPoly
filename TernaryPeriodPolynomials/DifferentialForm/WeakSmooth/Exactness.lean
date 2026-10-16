module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CechGluing
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.HilbertCover

@[expose] public section


/-! A genuine maximal Hilbert weak primitive yields a genuine global smooth equivariant primitive. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpaceCovering SmoothCoveringDeRham

/-- Every actual compact smooth two-form with an actual maximal Hilbert weak primitive is
smoothly exact globally. The resulting smooth primitive need not be compact or square integrable. -/
theorem hilbert_weak_primitive_smooth_exact (n : ℕ) (omega : Core n 2) (u : Hilbert n 1)
    (hu : (u, inclusion n 2 omega) ∈ (maximalDifferential n 1).graph) :
    ∃ v : EquivariantForm (deckRepresentation n) univ 1,
      differential (deckRepresentation n) isOpen_univ 1 v = omega.val :=
  (hilbert_weak_primitive_intrinsic_cover n omega u hu).elim (fun U hU =>
    hU.elim (fun hOpen hv => hv.elim (fun v hf => hf.elim (fun f H =>
      global_primitive_of_local_intrinsic_corrections n U hOpen H.1 omega.val
        (intrinsicHilbertCurrent n 1 univ u) v f H.2.1 H.2.2))))

end TernaryPoly.PolynomialFormWeakSmooth
