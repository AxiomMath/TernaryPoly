module

public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Support

@[expose] public section


/-! Actual local integration by parts for genuine polynomial-valued exterior forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open Set MeasureTheory
open scoped ContDiff

/-- The coordinate weighted pairing is exactly metric times Riemannian density. -/
theorem weightedPairing_components (n k : ℕ) (f g : Coordinates → FormValue n k) (x : Coordinates) :
    weightedPairing (weightedGram n k) (components n k f) (components n k g) x =
      coordinateDensity x * formPairing n k x (f x) (g x) :=
  weightedGram_pairing n k x (f x) (g x)

/-- Actual compact forms satisfy integration by parts against the true metric-volume density. -/
theorem integral_extDeriv_localAdjoint (n k : ℕ)
    (f : Coordinates → FormValue n k) (g : Coordinates → FormValue n (k + 1))
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (hg : ContDiffOn ℝ ∞ g positiveCoordinates)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ positiveCoordinates)
    (hgs : tsupport g ⊆ positiveCoordinates) :
    ∫ x, coordinateDensity x * formPairing n (k + 1) x (extDeriv f x) (g x) =
      ∫ x, coordinateDensity x * formPairing n k x (f x) (localAdjoint n k g x) := by
  have hfg : ContDiff ℝ ∞ f := contDiff_of_tsupport_subset isOpen_positiveCoordinates hf hfs
  have hfi (i : Index n k) : ContDiff ℝ 1 (components n k f i) :=
    (contDiff_of_tsupport_subset isOpen_positiveCoordinates (contDiffOn_components n k hf i)
      ((tsupport_components n k f i).trans hfs)).of_le (by simp)
  have hgi (j : Index n (k + 1)) : ContDiffOn ℝ 1 (components n (k + 1) g j) positiveCoordinates :=
    (contDiffOn_components n (k + 1) hg j).of_le (by simp)
  have hext : matrixFirstOrder (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k)
      (fun _ _ _ _ => 0) (components n k f) = components n (k + 1) (extDeriv f) := by
    funext j x
    exact (extDeriv_eq_matrixFirstOrder n k f (hfg.differentiable (by simp) x) j).symm
  have h := integral_weightedMatrixAdjoint_on (μ := volume) isOpen_positiveCoordinates
    (weightedGram n k) (weightedGram n (k + 1))
    (fun x hx => isUnit_iff_ne_zero.mpr (ne_of_gt (weightedGram_posDef n k x hx).det_pos))
    (fun j l => (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n (k + 1)) j) l).of_le (by simp))
    (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k) (fun _ _ _ _ => 0)
    (components n k f) (components n (k + 1) g)
    (fun _ _ _ => contDiff_const) (fun _ _ _ => continuous_const) hfi hgi
    (fun i => hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_components n k f i))
    (fun i => (tsupport_components n k f i).trans hfs)
    (fun j => (tsupport_components n (k + 1) g j).trans hgs)
  rw [hext, ← components_localAdjoint] at h
  simpa only [weightedPairing_components] using h

end TernaryPoly.PolynomialFormCoordinates
