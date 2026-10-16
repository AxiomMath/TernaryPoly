module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.HilbertNeighborhood

@[expose] public section


/-! A genuine global quotient cover carrying actual intrinsic Hilbert primitive data. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set TopologicalSpace PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpacePositive
  SymmetricSpaceCharts SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- Every genuine Hilbert weak primitive supplies a genuine quotient open cover with actual
smooth local primitives and actual intrinsic scalar-current corrections. -/
theorem hilbert_weak_primitive_intrinsic_cover (n : ℕ) (omega : Core n 2)
    (u : Hilbert n 1) (hu : (u, inclusion n 2 omega) ∈ (maximalDifferential n 1).graph) :
    ∃ (U : OrbitSpace → Set OrbitSpace) (hU : ∀ q, IsOpen (U q))
      (v : ∀ q, EquivariantForm (deckRepresentation n) (U q) 1)
      (T : ∀ q, IntrinsicCurrent n 0 (U q)),
      (⋃ q, U q) = univ ∧
      (∀ q, differential (deckRepresentation n) (hU q) 1 (v q) =
        restrictEquivariant (deckRepresentation n) (subset_univ _) 2 omega.val) ∧
      (∀ q, intrinsicCurrentDifferential n 0 (U q) (T q) =
        intrinsicCurrentRestriction n 1 (subset_univ _)
          (intrinsicHilbertCurrent n 1 univ u) - intrinsicSmoothCurrent n 1 (U q) (hU q) (v q)) := by
  classical
  let h (q : OrbitSpace) := hilbert_weak_primitive_intrinsic_neighborhood n omega u hu q
  let V (q : OrbitSpace) : Opens (TopCat.of OrbitSpace) := (h q).choose
  let v (q : OrbitSpace) : EquivariantForm (deckRepresentation n) (V q) 1 :=
    (h q).choose_spec.2.choose
  let T (q : OrbitSpace) : IntrinsicCurrent n 0 (V q) :=
    (h q).choose_spec.2.choose_spec.2.choose
  refine ⟨fun q => (V q : Set OrbitSpace), fun q => (V q).isOpen, v, T, ?_, ?_, ?_⟩
  · apply eq_univ_of_forall
    intro q
    exact mem_iUnion.mpr ⟨q, (h q).choose_spec.1⟩
  · intro q
    exact (h q).choose_spec.2.choose_spec.1
  · intro q
    exact (h q).choose_spec.2.choose_spec.2.choose_spec

end TernaryPoly.PolynomialFormWeakSmooth
