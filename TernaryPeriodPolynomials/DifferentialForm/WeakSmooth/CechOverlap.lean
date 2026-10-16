module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.GlobalRecognition
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothGlobal
public import TernaryPeriodPolynomials.Analysis.LinearCorrectionDifference

@[expose] public section


/-! Genuine smooth overlap differences of intrinsic scalar correction currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric SymmetricSpaceCovering SmoothCoveringDeRham

theorem intrinsicCorrection_difference_smooth (n : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (T : IntrinsicCurrent n 1 U) (f g : IntrinsicCurrent n 0 U)
    (a b : EquivariantForm (deckRepresentation n) U 1)
    (hf : intrinsicCurrentDifferential n 0 U f = T - intrinsicSmoothCurrent n 1 U hU a)
    (hg : intrinsicCurrentDifferential n 0 U g = T - intrinsicSmoothCurrent n 1 U hU b) :
    ∃ c : EquivariantForm (deckRepresentation n) U 0,
      intrinsicSmoothCurrent n 0 U hU c = g - f ∧
      differential (deckRepresentation n) hU 0 c = a - b := by
  have hd : intrinsicCurrentDifferential n 0 U (g-f) =
      intrinsicSmoothCurrent n 1 U hU (a-b) :=
    LinearCorrection.differential_difference (intrinsicCurrentDifferential n 0 U)
      (intrinsicSmoothCurrent n 1 U hU) T f g a b hf hg
  exact (intrinsicCurrent_zero_smooth_of_smooth_differential n U hU (g-f) (a-b) hd).elim
    (fun c hc => ⟨c,hc.symm,intrinsicSmoothCurrent_injective n 1 U hU
      ((intrinsicSmoothCurrent_differential n 0 U hU c).symm.trans
        ((congrArg (intrinsicCurrentDifferential n 0 U) hc.symm).trans hd))⟩)

theorem intrinsicCorrection_restrict (n : ℕ) {U V : Set OrbitSpace}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (T : IntrinsicCurrent n 1 univ) (f : IntrinsicCurrent n 0 U)
    (a : EquivariantForm (deckRepresentation n) U 1)
    (hf : intrinsicCurrentDifferential n 0 U f =
      intrinsicCurrentRestriction n 1 (subset_univ U) T - intrinsicSmoothCurrent n 1 U hU a) :
    intrinsicCurrentDifferential n 0 V (intrinsicCurrentRestriction n 0 hVU f) =
      intrinsicCurrentRestriction n 1 (subset_univ V) T -
        intrinsicSmoothCurrent n 1 V hV (restrictEquivariant (deckRepresentation n) hVU 1 a) := by
  exact (intrinsicCurrentRestriction_differential n 0 hVU f).symm.trans
    ((congrArg (intrinsicCurrentRestriction n 1 hVU) hf).trans
      ((map_sub (intrinsicCurrentRestriction n 1 hVU) _ _).trans
        (congrArg₂ (fun x y : IntrinsicCurrent n 1 V => x-y)
          (intrinsicCurrentRestriction_trans n 1 (subset_univ U) hVU T)
          (intrinsicSmoothCurrent_restriction n 1 hU hV hVU a))))

end TernaryPoly.PolynomialFormWeakSmooth
