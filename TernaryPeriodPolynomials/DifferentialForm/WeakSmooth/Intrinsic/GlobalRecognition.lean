module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Recognition
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.BoxNeighborhood
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.LocallySmooth

@[expose] public section


/-! Smooth recognition of genuine scalar currents on arbitrary actual quotient opens. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set TopologicalSpace PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpacePositive
  SymmetricSpaceCovering SmoothCoveringDeRham

/-- A genuine scalar current on any actual quotient open with actual smooth current differential
is itself the actual current of a genuine smooth equivariant zero-form. -/
theorem intrinsicCurrent_zero_smooth_of_smooth_differential (n : ℕ) (U : Set OrbitSpace)
    (hU : IsOpen U) (T : IntrinsicCurrent n 0 U)
    (a : EquivariantForm (deckRepresentation n) U 1)
    (hT : intrinsicCurrentDifferential n 0 U T = intrinsicSmoothCurrent n 1 U hU a) :
    ∃ f : EquivariantForm (deckRepresentation n) U 0,
      T = intrinsicSmoothCurrent n 0 U hU f := by
  apply intrinsicCurrent_smooth_of_locally_smooth n 0 U hU T
  intro q
  exact (exists_intrinsic_coordinateTestBox U hU q.val q.property).elim (fun S hS =>
    hS.elim (fun b hb => hb.elim (fun c hc => by
      let Ω := coordinateTestBox b c
      let V : Opens (TopCat.of OrbitSpace) := ⟨chartOpen S Ω, chartOpen_isOpen S Ω.isOpen⟩
      let hVU : (V : Set OrbitSpace) ⊆ U := chartOpen_subset_of_chartDomain S hc.2
      have hd : intrinsicCurrentDifferential n 0 V (intrinsicCurrentRestriction n 0 hVU T) =
          intrinsicSmoothCurrent n 1 V V.isOpen (restrictEquivariant (deckRepresentation n) hVU 1 a) :=
        (intrinsicCurrentRestriction_differential n 0 hVU T).symm.trans
          ((congrArg (intrinsicCurrentRestriction n 1 hVU) hT).trans
            (intrinsicSmoothCurrent_restriction n 1 hU V.isOpen hVU a))
      refine ⟨V, hVU, hc.1, ?_⟩
      exact intrinsicCurrent_zero_smooth_on_coordinateTestBox n S b c (hc.2.trans inter_subset_left)
        (intrinsicCurrentRestriction n 0 hVU T) (restrictEquivariant (deckRepresentation n) hVU 1 a) hd)))

end TernaryPoly.PolynomialFormWeakSmooth
