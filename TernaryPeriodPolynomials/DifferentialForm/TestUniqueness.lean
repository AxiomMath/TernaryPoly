module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Basis
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.AdjointUniqueness

@[expose] public section


/-! Genuine compact form tests detect every smooth polynomial-valued form pointwise. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open Set MeasureTheory
open scoped ContDiff

/-- Nondegeneracy of the actual weighted form pairing, tested by compact smooth forms. -/
theorem eqOn_zero_of_form_test_integrals (n k : ℕ) {g : Coordinates → FormValue n k}
    (hg : ContDiffOn ℝ ∞ g positiveCoordinates)
    (h : ∀ f : Coordinates → FormValue n k, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ positiveCoordinates →
      ∫ x, coordinateDensity x * formPairing n k x (f x) (g x) = 0) :
    EqOn g 0 positiveCoordinates := by
  have hz (a : FormValue n k) : EqOn
      (fun x => coordinateDensity x * formPairing n k x a (g x)) 0 positiveCoordinates := by
    apply eqOn_zero_of_test_integrals (μ := volume) isOpen_positiveCoordinates
    · exact (contDiffOn_coordinateDensity.mul
        (contDiffOn_formPairing_functions n k Subset.rfl contDiffOn_const hg)).continuousOn
    · intro φ hφ hφc hφs
      let : IsBoundedSMul ℝ (FormValue n k) :=
        @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
      let f : Coordinates → FormValue n k := fun x => φ x • a
      have hfc : HasCompactSupport f := hφc.of_isClosed_subset (isClosed_tsupport f)
        (tsupport_smul_subset_left φ (fun _ => a))
      have hfs : tsupport f ⊆ positiveCoordinates :=
        (tsupport_smul_subset_left φ (fun _ => a)).trans hφs
      have he := h f (ContDiff.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates)
        (F := FormValue n k) hφ contDiff_const) hfc hfs
      convert he using 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only [f]
      rw [formPairing_smul_left]
      ring
  intro x hx
  have he := hz (g x) hx
  have hp := coordinateDensity_pos x hx
  have hn : formPairing n k x (g x) (g x) = 0 := (mul_eq_zero.mp he).resolve_left (ne_of_gt hp)
  by_contra hne
  exact (ne_of_gt (formPairing_positive n k x hx (g x) hne)) hn

end TernaryPoly.PolynomialFormCoordinates
