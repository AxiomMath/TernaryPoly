module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ChartAlgebra
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.HilbertLocalPotential

@[expose] public section

/-! Actual intrinsic quotient potentials for genuine maximal Hilbert weak primitives. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpacePositive
  SymmetricSpaceCharts SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- A genuine maximal Hilbert weak primitive has, on every actual coordinate-box quotient open,
a genuine smooth local primitive and a genuine intrinsic scalar-current correction. -/
theorem hilbert_weak_primitive_intrinsic_local_potential (n : ℕ) (S : Space)
    (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates)
    (hΩ : (coordinateTestBox e a : Set Coordinates) ⊆ (quotientChart S).target)
    (omega : Core n 2) (u : Hilbert n 1)
    (hu : (u, inclusion n 2 omega) ∈ (maximalDifferential n 1).graph) :
    ∃ v : EquivariantForm (deckRepresentation n) (chartOpen S (coordinateTestBox e a)) 1,
      differential (deckRepresentation n) (chartOpen_isOpen S (coordinateTestBox e a).isOpen) 1 v =
        restrictEquivariant (deckRepresentation n) (subset_univ _) 2 omega.val ∧
      ∃ T : IntrinsicCurrent n 0 (chartOpen S (coordinateTestBox e a)),
        intrinsicCurrentDifferential n 0 (chartOpen S (coordinateTestBox e a)) T =
          intrinsicHilbertCurrent n 1 (chartOpen S (coordinateTestBox e a)) u -
            intrinsicSmoothCurrent n 1 (chartOpen S (coordinateTestBox e a))
              (chartOpen_isOpen S (coordinateTestBox e a).isOpen) v := by
  let Ω := coordinateTestBox e a
  exact (hilbert_weak_primitive_local_potential n S e a hΩ omega u hu).elim (fun v hv =>
    hv.2.elim (fun T hT => by
      refine ⟨chartExtendOn (deckRepresentation n) S Ω.isOpen 1 v, ?_,
        intrinsicCurrentOfForm n 0 S Ω T, ?_⟩
      · exact (chartExtendOn_d (deckRepresentation n) S Ω.isOpen v).trans
          ((congrArg (chartExtendOn (deckRepresentation n) S Ω.isOpen 2) hv.1).trans
            (intrinsicChartExtend_globalRepresentative n 2 S Ω hΩ omega.val))
      · apply (Function.LeftInverse.injective (intrinsicCurrentOfForm_chartFormCurrent n 1 S Ω hΩ))
        apply (intrinsicChartFormCurrent_differential n 0 S Ω hΩ _).symm.trans
        apply (congrArg (formWeakExterior n 0 Ω) (intrinsicChartFormCurrent_ofForm n 0 S Ω hΩ T)).trans
        apply hT.trans
        apply Eq.trans _ (intrinsicChartFormCurrent_sub n 1 S Ω hΩ _ _).symm
        exact congrArg₂ (fun X Y : FormWeak n 1 Ω => X - Y)
          (intrinsicChartFormCurrent_hilbert n 1 S Ω hΩ u).symm
          (intrinsicChartFormCurrent_smooth_extend n 1 S Ω hΩ v).symm))

end TernaryPoly.PolynomialFormWeakSmooth
