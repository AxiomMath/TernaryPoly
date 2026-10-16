module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.HilbertPotential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.BoxNeighborhood

@[expose] public section


/-! Genuine quotient neighborhoods carrying actual Hilbert primitive correction data. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set TopologicalSpace PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpacePositive
  SymmetricSpaceCharts SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- Every quotient point has an actual open neighborhood carrying a genuine smooth primitive
and a genuine intrinsic scalar-current correction for the given actual weak Hilbert primitive. -/
theorem hilbert_weak_primitive_intrinsic_neighborhood (n : ℕ) (omega : Core n 2)
    (u : Hilbert n 1) (hu : (u, inclusion n 2 omega) ∈ (maximalDifferential n 1).graph)
    (q : OrbitSpace) :
    ∃ V : Opens (TopCat.of OrbitSpace), q ∈ V ∧
      ∃ v : EquivariantForm (deckRepresentation n) V 1,
        differential (deckRepresentation n) V.isOpen 1 v =
          restrictEquivariant (deckRepresentation n) (subset_univ _) 2 omega.val ∧
        ∃ T : IntrinsicCurrent n 0 V,
          intrinsicCurrentDifferential n 0 V T = intrinsicHilbertCurrent n 1 V u -
            intrinsicSmoothCurrent n 1 V V.isOpen v := by
  exact (exists_intrinsic_coordinateTestBox univ isOpen_univ q (mem_univ q)).elim
    (fun S hS => hS.elim (fun e he => he.elim (fun a ha => by
      let V : Opens (TopCat.of OrbitSpace) :=
        ⟨chartOpen S (coordinateTestBox e a), chartOpen_isOpen S (coordinateTestBox e a).isOpen⟩
      refine ⟨V, ha.1, ?_⟩
      exact hilbert_weak_primitive_intrinsic_local_potential n S e a
        (ha.2.trans inter_subset_left) omega u hu)))

end TernaryPoly.PolynomialFormWeakSmooth
